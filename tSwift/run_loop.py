#!/usr/bin/env python3
"""
run_loop.py - Autonomous continuous loop for AI workers and managers

Copyright 2026 Dropbox, Inc.
Created by Andrew Yates
Licensed under the Apache License, Version 2.0

Usage:
    ./run_loop.py worker    # Fast autonomous worker loop
    ./run_loop.py manager   # Slower manager loop with longer intervals

Worker mode: Grinds through tasks, restarts immediately
Manager mode: Periodic check-ins, 10-min intervals, skips if still running
"""

import json
import os
import re
import select
import shutil
import signal
import socket
import subprocess
import sys
import time
import uuid
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

# --- Configuration ---

CONFIG = {
    "worker": {
        "restart_delay": 0,  # No delay - WORKERs grind continuously
        "error_delay": 5,  # seconds after error (brief pause before retry)
        "iteration_timeout": 90
        * 60,  # 90 minutes max per iteration (increased from 45)
        "git_author_name": "WORKER",
        "prompt": """You are WORKER. Be rigorous and thorough.

Check for [MANAGER] directives in recent commits.
Prioritize: in-progress issues first, then P0>P1>P2.
If no issues: use [maintain] tag, fix code quality.

RULES:
- Never edit tests to make them pass
- No mocks, no suppressing failures
- Evidence for every claim""",
        "codex_interval": 9,  # Use codex every Nth iteration (0 to disable)
    },
    "manager": {
        "restart_delay": 15 * 60,  # 15 minutes between iterations (increased from 10)
        "error_delay": 60,  # 1 minute after error
        "iteration_timeout": 90
        * 60,  # 90 minutes max per iteration (increased from 30)
        "git_author_name": "MANAGER",
        "prompt": """You are MANAGER. Be rigorous, skeptical, and ambitious.

CHECK FIRST:
- .flags/* for pulse signals (large_files, crashes, blocked_issues, no_work)
- metrics/latest.json for trends
- worker_logs/crashes.log for health

AUDIT ROTATION (check .manager_iteration for current position):
- Odd iterations: Freeform state check, direct worker
- Even iterations rotate: code_quality → test_gaps → anti_patterns → refactoring
- Find at least 3 issues. If found, loop until <3 remain. If not, explain why.

DIRECT WORKERS:
- HINT.md: echo "urgent" > HINT.md (worker reads next iteration)
- Directive files: MANAGER_DIRECTIVE_YYYY-MM-DD_topic.md, commit immediately
- Subissues: gh issue create --title "[M] Task (Part of #N)"

Link commits: Re: #N (feedback), Reopens #N (reopen)""",
        "codex_interval": 0,  # MANAGERs don't use codex
    },
}

LOG_DIR = Path("worker_logs")
HINTS_LOG = Path("HINTS_HISTORY.log")
ITERATION_FILE_TEMPLATE = ".iteration_{mode}"
PID_FILE_TEMPLATE = ".pid_{mode}"
STATUS_FILE_TEMPLATE = ".{mode}_status.json"  # Per-mode status files
MAX_LOG_FILES = 50
MAX_CRASH_LOG_LINES = 500

# Git hooks to install
# Fast linters only - slow ones (clippy, clang-tidy) run during cleanup iterations
# Only lint staged files (excludes submodules)
HOOKS = {
    "pre-commit": """#!/bin/bash
STAGED=$(git diff --cached --name-only --diff-filter=ACMR)
# Check for sensitive files (block if found)
SENSITIVE=$(echo "$STAGED" | grep -E '\\.(env|key|pem|p12|pfx)$|credentials\\.json|secrets\\.json|_secret')
if [ -n "$SENSITIVE" ]; then
    echo "ERROR: Refusing to commit potentially sensitive files:"
    echo "$SENSITIVE"
    echo "If these are safe, use: git commit --no-verify"
    exit 1
fi
echo "$STAGED" | grep '\\.py$' | xargs -r ruff check || exit 1
echo "$STAGED" | grep '\\.sh$' | xargs -r shellcheck 2>/dev/null || true
""",
}


def get_project_name() -> str:
    """Get project name from git remote or directory name."""
    try:
        result = subprocess.run(
            ["git", "remote", "get-url", "origin"],
            check=False,
            capture_output=True,
            text=True,
            timeout=5,
        )
        if result.returncode == 0:
            url = result.stdout.strip()
            # Handle SSH: git@github.com:user/repo.git
            # Handle HTTPS: https://github.com/user/repo.git
            return url.rstrip("/").rsplit("/", 1)[-1].removesuffix(".git")
    except Exception:
        pass
    # Fall back to current directory name
    return Path.cwd().name


def install_hooks():
    """Install git hooks if not present or outdated."""
    hooks_dir = Path(".git/hooks")
    if not hooks_dir.exists():
        return  # Not a git repo

    # Markers to detect our hooks
    markers = {
        "pre-commit": "ruff check",
    }

    for name, content in HOOKS.items():
        hook_path = hooks_dir / name
        marker = markers.get(name, name)
        needs_update = False

        if not hook_path.exists():
            needs_update = True
        else:
            existing = hook_path.read_text()
            if marker not in existing:
                # Append to existing hook
                content = existing.rstrip() + "\n\n" + content
                needs_update = True

        if needs_update:
            hook_path.write_text(content)
            hook_path.chmod(0o755)
            print(f"✓ Installed hook: {name}")


class LoopRunner:
    def __init__(self, mode: str):
        self.mode = mode
        self.config = CONFIG[mode]
        self.iteration = 1
        self.running = True
        self.current_process: Optional[subprocess.Popen] = None

        # File paths
        self.iteration_file = LOG_DIR / ITERATION_FILE_TEMPLATE.format(mode=mode)
        self.pid_file = Path(PID_FILE_TEMPLATE.format(mode=mode))
        self.status_file = Path(STATUS_FILE_TEMPLATE.format(mode=mode))
        self.crash_log = LOG_DIR / "crashes.log"

        # Check for codex availability
        self.codex_available = shutil.which("codex") is not None

        # Session identity
        self._session_id = uuid.uuid4().hex[:6]

    def get_git_iteration(self) -> int:
        """Get current iteration from git log by parsing [W]N commits.

        Searches ALL commits on current branch to avoid duplicates when
        many non-worker commits happen between iterations.

        Returns:
            Next iteration number to use (max found + 1, or 1 if none found)
        """
        try:
            # Search all commits, find ALL [W]N patterns, return max + 1
            result = subprocess.run(
                ["git", "log", "--oneline", "--all"],
                capture_output=True,
                text=True,
                timeout=30,
            )
            if result.returncode == 0:
                pattern = r"\[W\]#?(\d+)"
                max_iteration = 0
                for line in result.stdout.split("\n"):
                    match = re.search(pattern, line)
                    if match:
                        max_iteration = max(max_iteration, int(match.group(1)))
                if max_iteration > 0:
                    return max_iteration + 1
        except Exception:
            pass
        return 1

    def setup_git_identity(self):
        """Set up rich git identity for commits.

        Format: {project}-{role}-{iteration} <{session}@{machine}.{project}.ai-fleet>
        This enables forensic tracking of which AI session made which commits.
        """
        project = get_project_name()
        role = self.config["git_author_name"].lower()  # "worker" or "manager"
        iteration = self.get_git_iteration()
        machine = socket.gethostname().split(".")[0]
        session = self._session_id

        git_name = f"{project}-{role}-{iteration}"
        git_email = f"{session}@{machine}.{project}.ai-fleet"

        os.environ["GIT_AUTHOR_NAME"] = git_name
        os.environ["GIT_AUTHOR_EMAIL"] = git_email
        os.environ["GIT_COMMITTER_NAME"] = git_name
        os.environ["GIT_COMMITTER_EMAIL"] = git_email

        # Export for MCP tools and other scripts
        os.environ["AI_FLEET_PROJECT"] = project
        os.environ["AI_FLEET_ROLE"] = role.upper()
        os.environ["AI_FLEET_ITERATION"] = str(iteration)
        os.environ["AI_FLEET_SESSION"] = session
        os.environ["AI_FLEET_MACHINE"] = machine

        print(f"✓ Git identity: {git_name}")

    def setup(self):
        """Initialize environment and check dependencies."""
        # Check core dependencies
        if not shutil.which("claude"):
            print("ERROR: claude CLI not found in PATH")
            print("  Install: npm install -g @anthropic-ai/claude-code")
            sys.exit(1)
        print(f"✓ Found claude: {shutil.which('claude')}")

        if self.config["codex_interval"] > 0:
            if self.codex_available:
                print(f"✓ Found codex: {shutil.which('codex')}")
            else:
                print("  (codex not found, will use claude only)")

        json_to_text = Path("ai_template_scripts/json_to_text.py")
        if not json_to_text.exists():
            print(f"ERROR: {json_to_text} not found")
            sys.exit(1)
        print(f"✓ Found {json_to_text}")

        # Check git
        if not shutil.which("git"):
            print("ERROR: git not found in PATH")
            sys.exit(1)
        print(f"✓ Found git: {shutil.which('git')}")

        # Check GitHub CLI
        if not shutil.which("gh"):
            print("ERROR: gh (GitHub CLI) not found in PATH")
            print("  Install: brew install gh")
            sys.exit(1)
        print(f"✓ Found gh: {shutil.which('gh')}")

        # Check gh authentication
        auth_result = subprocess.run(
            ["gh", "auth", "status"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        if auth_result.returncode != 0:
            print("ERROR: gh not authenticated")
            print("  Run: gh auth login")
            sys.exit(1)
        print("✓ gh authenticated")

        # Check network (non-blocking warning)
        try:
            net_result = subprocess.run(
                ["gh", "api", "user", "--jq", ".login"],
                capture_output=True,
                text=True,
                timeout=10,
            )
            if net_result.returncode == 0:
                print(f"✓ GitHub connected as: {net_result.stdout.strip()}")
            else:
                print("⚠ GitHub API unreachable (offline mode)")
        except subprocess.TimeoutExpired:
            print("⚠ GitHub API timeout (offline mode)")

        # Create log directory
        LOG_DIR.mkdir(exist_ok=True)

        # Install git hooks
        install_hooks()

        # Set up git identity for commits
        self.setup_git_identity()

        # Check for existing instance
        if self.pid_file.exists():
            try:
                old_pid = int(self.pid_file.read_text().strip())
                # Check if process is still running
                os.kill(old_pid, 0)  # Doesn't kill, just checks
                print(
                    f"ERROR: Another {self.mode} loop is already running (PID {old_pid})"
                )
                print(f"  Stop it first or remove {self.pid_file}")
                sys.exit(1)
            except (ProcessLookupError, ValueError):
                # Process not running, clean up stale PID file
                self.pid_file.unlink()

        # Write our PID
        self.pid_file.write_text(str(os.getpid()))

        # Restore iteration counter
        if self.iteration_file.exists():
            try:
                self.iteration = int(self.iteration_file.read_text().strip())
                print(f"Resuming from iteration {self.iteration}")
            except ValueError:
                self.iteration = 1

        # Rotate logs
        self.rotate_logs()

        # Setup signal handlers
        signal.signal(signal.SIGINT, self.handle_signal)
        signal.signal(signal.SIGTERM, self.handle_signal)

        # Track start time for status
        self._started_at = datetime.now(timezone.utc).isoformat()
        self.write_status("starting")

        print()
        print(f"Starting {self.mode} loop...")
        print()

    def handle_signal(self, signum, frame):
        """Handle shutdown signals gracefully."""
        print()
        print(f"Received signal {signum}, shutting down...")
        self.running = False
        if self.current_process:
            self.current_process.terminate()

    def cleanup(self):
        """Clean up on exit."""
        self.clear_status()
        if self.pid_file.exists():
            self.pid_file.unlink()
        print(f"Completed {self.iteration - 1} iterations")

    def rotate_logs(self):
        """Remove old log files to prevent unbounded growth."""
        log_files = sorted(LOG_DIR.glob("*.jsonl"), key=lambda p: p.stat().st_mtime)
        if len(log_files) > MAX_LOG_FILES:
            for f in log_files[:-MAX_LOG_FILES]:
                f.unlink()
            print(f"Rotated logs: removed {len(log_files) - MAX_LOG_FILES} old files")

        # Rotate crash log
        if self.crash_log.exists():
            lines = self.crash_log.read_text().splitlines()
            if len(lines) > MAX_CRASH_LOG_LINES:
                self.crash_log.write_text(
                    "\n".join(lines[-MAX_CRASH_LOG_LINES:]) + "\n"
                )

    def write_status(
        self,
        status: str,
        log_file: Optional[Path] = None,
        extra: Optional[dict[str, Any]] = None,
    ):
        """Write worker status to .worker_status.json for manager visibility."""
        now = datetime.now(timezone.utc).isoformat()
        data = {
            "pid": os.getpid(),
            "mode": self.mode,
            "project": get_project_name(),
            "iteration": self.iteration,
            "status": status,
            "updated_at": now,
            "started_at": getattr(self, "_started_at", now),
        }
        if log_file:
            data["log_file"] = str(log_file)
        if extra:
            data.update(extra)

        # Atomic write
        tmp = self.status_file.with_suffix(".tmp")
        tmp.write_text(json.dumps(data, indent=2))
        tmp.rename(self.status_file)

    def clear_status(self):
        """Remove status file on clean exit."""
        if self.status_file.exists():
            self.status_file.unlink()

    def check_hint(self) -> str:
        """Check for and consume HINT.md file."""
        hint_file = Path("HINT.md")
        if hint_file.exists():
            try:
                hint = hint_file.read_text().strip()
                hint_file.unlink()

                # Log hint
                timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                with open(HINTS_LOG, "a") as f:
                    f.write(f"[{timestamp}] Iteration {self.iteration}: {hint}\n")

                print(f"📝 Applied hint: {hint}")
                return hint
            except Exception as e:
                print(f"Warning: Could not read hint: {e}")
        return ""

    def select_ai_tool(self) -> str:
        """Select which AI tool to use for this iteration."""
        codex_interval = self.config["codex_interval"]
        if (
            codex_interval > 0
            and self.codex_available
            and self.iteration > 1
            and self.iteration % codex_interval == 0
        ):
            return "codex"
        return "claude"

    def run_iteration(self) -> tuple[int, float, str]:
        """Run a single AI iteration. Returns (exit_code, start_time, ai_tool)."""
        hint = self.check_hint()

        # Build prompt
        prompt = f"{hint}\n\n{self.config['prompt']}" if hint else self.config["prompt"]

        # Select AI tool
        ai_tool = self.select_ai_tool()

        print()
        print("=" * 50)
        print(f"=== {self.mode.title()} Iteration {self.iteration}")
        print(f"=== Started at {datetime.now()}")
        print(f"=== Using: {ai_tool.title()}")
        print("=" * 50)
        print()

        # Prepare log file
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        log_file = (
            LOG_DIR / f"{self.mode}_iter_{self.iteration}_{ai_tool}_{timestamp}.jsonl"
        )

        # Update status for manager visibility (include hint if present)
        status_extra: dict[str, Any] = {"ai_tool": ai_tool}
        if hint:
            status_extra["hint"] = hint
        self.write_status("working", log_file, status_extra)

        # Build command
        if ai_tool == "claude":
            cmd = [
                "claude",
                "--dangerously-skip-permissions",
                "-p",
                prompt,
                "--permission-mode",
                "acceptEdits",
                "--output-format",
                "stream-json",
                "--verbose",
            ]
        else:
            # Codex needs explicit commit instruction
            codex_prompt = (
                prompt
                + """

IMPORTANT: After completing the work, YOU MUST create the git commit immediately using the CLAUDE.md commit template. Do NOT ask for permission - just commit. This is headless autonomous mode."""
            )
            cmd = [
                "codex",
                "exec",
                "--dangerously-bypass-approvals-and-sandbox",
                "--json",
                codex_prompt,
            ]

        # Run AI with output piped through json_to_text.py
        timeout_sec = self.config["iteration_timeout"]
        start_time = time.time()
        exit_code = 0
        timed_out = False
        text_proc_alive = True

        try:
            with open(log_file, "w") as log_f:
                ai_proc = subprocess.Popen(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                )
                self.current_process = ai_proc

                text_proc = subprocess.Popen(
                    ["./ai_template_scripts/json_to_text.py"],
                    stdin=subprocess.PIPE,
                    stdout=sys.stdout,
                    stderr=sys.stderr,
                )

                def write_to_text_proc(data: bytes) -> None:
                    """Write to text_proc, handling failures gracefully."""
                    nonlocal text_proc_alive
                    if not text_proc_alive:
                        return
                    try:
                        text_proc.stdin.write(data)
                        text_proc.stdin.flush()
                    except (BrokenPipeError, OSError):
                        # text_proc exited early - continue draining ai_proc
                        # to prevent EPIPE in Claude CLI
                        text_proc_alive = False

                # Stream output with timeout checking
                # CRITICAL: Always drain ai_proc.stdout completely to prevent EPIPE
                # Even if text_proc dies, we must keep reading from ai_proc
                try:
                    while ai_proc.poll() is None:
                        # Check timeout
                        if time.time() - start_time > timeout_sec:
                            print(f"\nTimeout after {timeout_sec // 60} minutes")
                            # Graceful shutdown: SIGTERM first, then SIGKILL
                            ai_proc.terminate()  # SIGTERM
                            try:
                                ai_proc.wait(timeout=10)  # Grace period
                                print("Process terminated gracefully")
                            except subprocess.TimeoutExpired:
                                print("Grace period expired, sending SIGKILL")
                                ai_proc.kill()
                            timed_out = True
                            break

                        # Non-blocking read
                        ready, _, _ = select.select([ai_proc.stdout], [], [], 1.0)
                        if ready:
                            line = ai_proc.stdout.readline()
                            if line:
                                log_f.write(line.decode())
                                log_f.flush()
                                write_to_text_proc(line)

                    # Drain remaining output (always, even after timeout)
                    # Use timeout to prevent hanging on stuck processes
                    drain_timeout = 30  # seconds
                    drain_start = time.time()
                    while time.time() - drain_start < drain_timeout:
                        ready, _, _ = select.select([ai_proc.stdout], [], [], 1.0)
                        if ready:
                            line = ai_proc.stdout.readline()
                            if not line:
                                break  # EOF
                            log_f.write(line.decode())
                            log_f.flush()
                            write_to_text_proc(line)
                        elif ai_proc.poll() is not None:
                            break  # Process exited and no more data
                finally:
                    if text_proc_alive:
                        try:
                            text_proc.stdin.close()
                        except (BrokenPipeError, OSError):
                            pass
                    text_proc.wait()

                exit_code = 124 if timed_out else (ai_proc.returncode or 0)
                self.current_process = None

        except Exception as e:
            print(f"Error running {ai_tool}: {e}")
            exit_code = 1

        print()
        print(
            f"=== {self.mode.title()} Iteration {self.iteration} ({ai_tool}) completed ==="
        )
        print(f"=== Exit code: {exit_code} ===")
        print(f"=== Log saved to: {log_file} ===")
        print()

        return exit_code, start_time, ai_tool

    def check_session_success(self, start_time: float) -> bool:
        """Check if the AI session made a commit during this iteration.

        A session that committed is considered successful even if the exit code
        is non-zero (e.g., EPIPE at the end after work completed).
        """
        try:
            # Get commits from the last iteration window
            # Use --since with a timestamp slightly before start_time
            since_time = int(start_time) - 60  # 1 minute buffer
            result = subprocess.run(
                [
                    "git",
                    "log",
                    "--oneline",
                    f"--since={since_time}",
                    "--author=WORKER",
                    "--author=MANAGER",
                    "-1",
                ],
                capture_output=True,
                text=True,
                timeout=5,
            )
            # If we got a commit hash, the session was successful
            return result.returncode == 0 and bool(result.stdout.strip())
        except Exception:
            return False

    def log_crash(self, exit_code: int, ai_tool: str, session_committed: bool = False):
        """Log crash or exit details.

        Args:
            exit_code: The process exit code
            ai_tool: Which AI tool was used (claude/codex)
            session_committed: Whether the session made a git commit
        """
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        if exit_code > 128:
            signal_num = exit_code - 128
            error_msg = f"{ai_tool} killed by signal {signal_num}"
            is_real_crash = True
        elif exit_code == 124:
            error_msg = f"{ai_tool} timed out"
            is_real_crash = not session_committed  # Timeout after commit = not a crash
        else:
            error_msg = f"{ai_tool} exited with code {exit_code}"
            # Exit code 1 after successful commit = likely EPIPE or graceful exit
            is_real_crash = not session_committed

        if session_committed and not is_real_crash:
            # Session completed work - this is not a crash
            print()
            print(
                f"Note: {ai_tool} exited with code {exit_code} but session committed successfully"
            )
            print()
            return  # Don't log to crashes.log

        with open(self.crash_log, "a") as f:
            f.write(f"[{timestamp}] Iteration {self.iteration}: {error_msg}\n")

        print()
        print("╔" + "═" * 60 + "╗")
        print(f"║ {self.mode.upper()} CRASH DETECTED")
        print("╠" + "═" * 60 + "╣")
        print(f"║ {error_msg}")
        print(f"║ Crash history: {self.crash_log}")
        print("╚" + "═" * 60 + "╝")
        print()

    def run(self):
        """Main loop."""
        self.setup()

        try:
            while self.running:
                exit_code, start_time, ai_tool = self.run_iteration()

                if not self.running:
                    break

                # Determine delay and check for crashes
                if exit_code != 0:
                    # Check if session actually succeeded despite non-zero exit
                    session_committed = self.check_session_success(start_time)
                    self.log_crash(exit_code, ai_tool, session_committed)
                    # Use shorter delay if session committed successfully
                    delay = (
                        self.config["restart_delay"]
                        if session_committed
                        else self.config["error_delay"]
                    )
                else:
                    delay = self.config["restart_delay"]

                # Increment and persist iteration
                self.iteration += 1
                self.iteration_file.write_text(str(self.iteration))

                # Wait before next iteration (skip if no delay)
                if delay > 0:
                    self.write_status("waiting", extra={"next_iteration_in": delay})
                    if delay > 60:
                        print(f"Next iteration in {delay // 60} minutes...")
                    else:
                        print(f"Next iteration in {delay} seconds...")

                    # Interruptible sleep (responds to signals)
                    for _ in range(delay):
                        if not self.running:
                            break
                        time.sleep(1)

        finally:
            self.cleanup()


def main():
    # Default to worker mode if no argument provided
    if len(sys.argv) == 1:
        mode = "worker"
    elif len(sys.argv) == 2 and sys.argv[1] in ("worker", "manager"):
        mode = sys.argv[1]
    else:
        print("Usage: ./run_loop.py [worker|manager]")
        print()
        print("  worker   - Fast autonomous loop (no delay) [default]")
        print("  manager  - Periodic loop (10-min intervals)")
        print()
        print("Hint: echo 'message' > HINT.md")
        sys.exit(1)

    LoopRunner(mode).run()


if __name__ == "__main__":
    main()
