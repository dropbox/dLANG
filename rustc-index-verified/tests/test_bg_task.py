"""Tests for bg_task.py background task management."""

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

import pytest

# Add ai_template_scripts to path
sys.path.insert(0, str(Path(__file__).parent.parent / "ai_template_scripts"))

import bg_task


class TestTaskMeta:
    """Test TaskMeta dataclass."""

    def test_to_dict(self):
        meta = bg_task.TaskMeta(
            task_id="test-task",
            command="sleep 5",
            description="Test",
            issue=42,
            timeout=60,
            status="running",
            started_at="2024-01-01T00:00:00+00:00",
            pid=1234,
        )
        d = meta.to_dict()
        assert d["task_id"] == "test-task"
        assert d["command"] == "sleep 5"
        assert d["issue"] == 42
        assert d["pid"] == 1234

    def test_from_dict(self):
        data = {
            "task_id": "test",
            "command": "echo hello",
            "description": "Test task",
            "issue": None,
            "timeout": 60,
            "status": "completed",
            "started_at": "2024-01-01T00:00:00+00:00",
            "finished_at": "2024-01-01T00:01:00+00:00",
            "pid": 5678,
            "exit_code": 0,
            "machine": "test-host",
            "worker_iteration": 5,
        }
        meta = bg_task.TaskMeta.from_dict(data)
        assert meta.task_id == "test"
        assert meta.exit_code == 0
        assert meta.worker_iteration == 5


class TestIsProcessAlive:
    """Test process liveness check."""

    def test_current_process_is_alive(self):
        assert bg_task.is_process_alive(os.getpid()) is True

    def test_nonexistent_process_is_dead(self):
        # Use a very high PID that's unlikely to exist
        assert bg_task.is_process_alive(999999999) is False


class TestFormatDuration:
    """Test duration formatting."""

    def test_seconds(self):
        assert bg_task.format_duration(30) == "30s"

    def test_minutes(self):
        assert bg_task.format_duration(120) == "2.0m"

    def test_hours(self):
        assert bg_task.format_duration(7200) == "2.0h"


class TestGetGitRoot:
    """Test git root detection."""

    def test_returns_path(self):
        # This test assumes we're in a git repo
        root = bg_task.get_git_root()
        assert root.exists()
        assert (root / ".git").exists()


class TestTaskDirectory:
    """Test task directory operations."""

    def test_get_tasks_dir_creates_directory(self):
        tasks_dir = bg_task.get_tasks_dir()
        assert tasks_dir.exists()
        assert tasks_dir.name == ".background_tasks"

    def test_get_task_dir(self):
        task_dir = bg_task.get_task_dir("my-task")
        assert task_dir.name == "my-task"
        assert task_dir.parent.name == ".background_tasks"


class TestManifest:
    """Test manifest operations."""

    def test_load_empty_manifest(self):
        manifest = bg_task.load_manifest()
        assert "tasks" in manifest

    def test_save_and_load_manifest(self):
        manifest = {"tasks": {"test": {"status": "running"}}}
        bg_task.save_manifest(manifest)
        loaded = bg_task.load_manifest()
        assert loaded["tasks"]["test"]["status"] == "running"


class TestStartTask:
    """Test task starting."""

    def test_start_simple_task(self):
        """Test starting a simple background task."""
        task_id = f"test-{int(time.time())}"

        try:
            meta = bg_task.start_task(
                command=["sleep", "1"],
                task_id=task_id,
                timeout=30,
                description="Test sleep task",
            )

            assert meta.task_id == task_id
            assert meta.status == "running"
            assert meta.pid is not None
            assert meta.pid > 0

            # Verify files created
            task_dir = bg_task.get_task_dir(task_id)
            assert (task_dir / "meta.json").exists()
            assert (task_dir / "pid").exists()

            # Wait for completion
            time.sleep(2)
            updated = bg_task.update_task_status(task_id)
            assert updated.status == "completed"
            assert updated.exit_code == 0

        finally:
            # Cleanup
            bg_task.cleanup_tasks(days=0, force=True)

    def test_start_task_with_issue(self):
        """Test task with issue number."""
        task_id = f"test-issue-{int(time.time())}"

        try:
            meta = bg_task.start_task(
                command=["echo", "test"],
                task_id=task_id,
                issue=42,
                timeout=10,
            )
            assert meta.issue == 42

        finally:
            bg_task.cleanup_tasks(days=0, force=True)

    def test_cannot_start_duplicate_running_task(self):
        """Test that duplicate running tasks are rejected."""
        task_id = f"test-dup-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["sleep", "10"],
                task_id=task_id,
                timeout=30,
            )

            with pytest.raises(ValueError, match="already running"):
                bg_task.start_task(
                    command=["echo", "test"],
                    task_id=task_id,
                    timeout=10,
                )

        finally:
            bg_task.kill_task(task_id)
            bg_task.cleanup_tasks(days=0, force=True)


class TestListTasks:
    """Test task listing."""

    def test_list_running_tasks(self):
        """Test listing only running tasks."""
        task_id = f"test-list-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["sleep", "5"],
                task_id=task_id,
                timeout=30,
            )

            tasks = bg_task.list_tasks(show_all=False)
            assert any(t.task_id == task_id for t in tasks)

        finally:
            bg_task.kill_task(task_id)
            bg_task.cleanup_tasks(days=0, force=True)


class TestTailOutput:
    """Test output tailing."""

    def test_tail_output(self):
        """Test tailing task output."""
        task_id = f"test-tail-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["echo", "hello world"],
                task_id=task_id,
                timeout=10,
            )

            time.sleep(1)
            output = bg_task.tail_output(task_id, lines=50)
            assert "hello world" in output

        finally:
            bg_task.cleanup_tasks(days=0, force=True)

    def test_tail_nonexistent_task(self):
        """Test tailing output of nonexistent task."""
        output = bg_task.tail_output("nonexistent-task", lines=10)
        assert "no output" in output


class TestKillTask:
    """Test task killing."""

    def test_kill_running_task(self):
        """Test killing a running task."""
        task_id = f"test-kill-{int(time.time())}"

        try:
            meta = bg_task.start_task(
                command=["sleep", "60"],
                task_id=task_id,
                timeout=120,
            )
            assert meta.status == "running"

            killed = bg_task.kill_task(task_id)
            assert killed.status == "killed"

            # Verify process is actually dead
            time.sleep(0.5)
            assert not bg_task.is_process_alive(meta.pid)

        finally:
            bg_task.cleanup_tasks(days=0, force=True)


class TestCleanup:
    """Test task cleanup."""

    def test_cleanup_old_tasks(self):
        """Test cleanup removes completed tasks."""
        task_id = f"test-cleanup-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["echo", "test"],
                task_id=task_id,
                timeout=10,
            )

            time.sleep(1)
            removed = bg_task.cleanup_tasks(days=0, force=True)
            assert task_id in removed

        finally:
            pass  # Already cleaned


class TestCLIArgs:
    """Test CLIArgs dataclass."""

    def test_defaults(self):
        """Test CLIArgs default values."""
        args = bg_task.CLIArgs(command="list")
        assert args.command == "list"
        assert args.id is None
        assert args.timeout == bg_task.DEFAULT_TIMEOUT
        assert args.description == ""
        assert args.command_args == []
        assert args.all is False
        assert args.lines == 50
        assert args.follow is False
        assert args.days == 7
        assert args.force is False

    def test_with_values(self):
        """Test CLIArgs with explicit values."""
        args = bg_task.CLIArgs(
            command="start",
            id="test-id",
            issue=42,
            timeout=300,
            description="Test task",
            command_args=["echo", "hello"],
        )
        assert args.command == "start"
        assert args.id == "test-id"
        assert args.issue == 42
        assert args.timeout == 300
        assert args.description == "Test task"
        assert args.command_args == ["echo", "hello"]


class TestBuildParser:
    """Test argument parser construction."""

    def test_parser_returns_argparse(self):
        """Test that build_parser returns an ArgumentParser."""
        parser = bg_task.build_parser()
        assert isinstance(parser, argparse.ArgumentParser)

    def test_parser_has_all_subcommands(self):
        """Test that parser has all expected subcommands."""
        parser = bg_task.build_parser()
        # Verify each subcommand is accepted by the parser
        for cmd in ["list", "cleanup"]:
            args = parser.parse_args([cmd])
            assert args.command == cmd

    def test_start_command_requires_id(self):
        """Test start command requires --id."""
        parser = bg_task.build_parser()
        with pytest.raises(SystemExit):
            parser.parse_args(["start", "--", "echo", "hello"])


class TestNamespaceToCLIArgs:
    """Test namespace conversion to CLIArgs."""

    def test_converts_list_args(self):
        """Test conversion of list command args."""
        parser = bg_task.build_parser()
        ns = parser.parse_args(["list", "--all"])
        args = bg_task.namespace_to_cli_args(ns)
        assert args.command == "list"
        assert args.all is True

    def test_converts_start_args(self):
        """Test conversion of start command args."""
        parser = bg_task.build_parser()
        ns = parser.parse_args(
            ["start", "--id", "test", "--issue", "42", "--", "echo", "hi"]
        )
        args = bg_task.namespace_to_cli_args(ns)
        assert args.command == "start"
        assert args.id == "test"
        assert args.issue == 42
        assert "--" in args.command_args or "echo" in args.command_args

    def test_converts_tail_args(self):
        """Test conversion of tail command args."""
        parser = bg_task.build_parser()
        ns = parser.parse_args(["tail", "my-task", "-n", "100", "-f"])
        args = bg_task.namespace_to_cli_args(ns)
        assert args.command == "tail"
        assert args.task_id == "my-task"
        assert args.lines == 100
        assert args.follow is True

    def test_converts_cleanup_args(self):
        """Test conversion of cleanup command args."""
        parser = bg_task.build_parser()
        ns = parser.parse_args(["cleanup", "--days", "14", "--force"])
        args = bg_task.namespace_to_cli_args(ns)
        assert args.command == "cleanup"
        assert args.days == 14
        assert args.force is True


class TestHandleList:
    """Test _handle_list command handler."""

    def test_returns_zero(self, capsys):
        """Test list handler returns 0."""
        args = bg_task.CLIArgs(command="list", all=False)
        result = bg_task.handle_list(args)
        assert result == 0

    def test_prints_output(self, capsys):
        """Test list handler prints something."""
        args = bg_task.CLIArgs(command="list", all=True)
        bg_task.handle_list(args)
        captured = capsys.readouterr()
        # Either "No tasks found" or the table header
        assert "task" in captured.out.lower() or "ID" in captured.out


class TestHandleStatus:
    """Test _handle_status command handler."""

    def test_nonexistent_task_returns_1(self, capsys):
        """Test status of nonexistent task returns 1."""
        args = bg_task.CLIArgs(command="status", task_id="nonexistent-task-12345")
        result = bg_task.handle_status(args)
        assert result == 1
        captured = capsys.readouterr()
        assert "not found" in captured.err


class TestHandleKill:
    """Test _handle_kill command handler."""

    def test_nonexistent_task_returns_1(self, capsys):
        """Test kill of nonexistent task returns 1."""
        args = bg_task.CLIArgs(command="kill", task_id="nonexistent-task-12345")
        result = bg_task.handle_kill(args)
        assert result == 1
        captured = capsys.readouterr()
        assert "not found" in captured.err


class TestHandleCleanup:
    """Test _handle_cleanup command handler."""

    def test_cleanup_returns_zero(self, capsys):
        """Test cleanup returns 0."""
        args = bg_task.CLIArgs(command="cleanup", days=7, force=False)
        result = bg_task.handle_cleanup(args)
        assert result == 0


class TestHandleStart:
    """Test _handle_start command handler."""

    def test_no_command_returns_1(self, capsys):
        """Test start without command returns 1."""
        args = bg_task.CLIArgs(command="start", id="test", command_args=[])
        result = bg_task.handle_start(args)
        assert result == 1
        captured = capsys.readouterr()
        assert "No command" in captured.err

    def test_start_with_separator(self):
        """Test start handles -- separator."""
        task_id = f"test-sep-{int(time.time())}"
        try:
            args = bg_task.CLIArgs(
                command="start",
                id=task_id,
                timeout=10,
                command_args=["--", "echo", "hello"],
            )
            result = bg_task.handle_start(args)
            assert result == 0
        finally:
            bg_task.kill_task(task_id)
            bg_task.cleanup_tasks(days=0, force=True)


class TestHandleWait:
    """Test _handle_wait command handler."""

    def test_nonexistent_task_returns_1(self, capsys):
        """Test wait on nonexistent task returns 1."""
        args = bg_task.CLIArgs(
            command="wait", task_id="nonexistent-task-12345", timeout=1
        )
        result = bg_task.handle_wait(args)
        assert result == 1
        captured = capsys.readouterr()
        assert "Error" in captured.err


class TestMain:
    """Test main entry point."""

    def test_no_command_shows_help(self, capsys, monkeypatch):
        """Test no command shows help."""
        monkeypatch.setattr("sys.argv", ["bg_task.py"])
        result = bg_task.main()
        assert result == 1
        captured = capsys.readouterr()
        assert (
            "usage:" in captured.out.lower()
            or "background task" in captured.out.lower()
        )

    def test_list_command_via_main(self, monkeypatch):
        """Test list command through main."""
        monkeypatch.setattr("sys.argv", ["bg_task.py", "list"])
        result = bg_task.main()
        assert result == 0


class TestLoadManifestEdgeCases:
    """Test manifest loading edge cases."""

    def test_load_manifest_no_file(self, tmp_path, monkeypatch):
        """Test load_manifest returns empty tasks dict when file doesn't exist."""
        # Make get_tasks_dir return a fresh directory without manifest.json
        monkeypatch.setattr(
            bg_task, "get_tasks_dir", lambda: tmp_path / ".background_tasks"
        )
        (tmp_path / ".background_tasks").mkdir(parents=True, exist_ok=True)
        # Ensure no manifest.json exists
        manifest_path = tmp_path / ".background_tasks" / "manifest.json"
        if manifest_path.exists():
            manifest_path.unlink()

        result = bg_task.load_manifest()
        assert result == {"tasks": {}}


class TestUpdateTaskStatusEdgeCases:
    """Test update_task_status edge cases."""

    def test_process_died_without_result_file(self, tmp_path, monkeypatch):
        """Test task status when process died without writing result.json."""
        tasks_dir = tmp_path / ".background_tasks"
        tasks_dir.mkdir(parents=True, exist_ok=True)
        monkeypatch.setattr(bg_task, "get_tasks_dir", lambda: tasks_dir)

        task_id = "dead-task"
        task_dir = tasks_dir / task_id
        task_dir.mkdir()

        # Create meta with a PID that doesn't exist (very high number)
        meta = bg_task.TaskMeta(
            task_id=task_id,
            command="sleep 100",
            description="Test",
            issue=None,
            timeout=60,
            status="running",
            started_at="2024-01-01T00:00:00+00:00",
            pid=999999999,  # Doesn't exist
        )
        meta_path = task_dir / "meta.json"
        meta_path.write_text(bg_task.json.dumps(meta.to_dict(), indent=2))

        # Create manifest
        manifest = {"tasks": {task_id: {"status": "running"}}}
        (tasks_dir / "manifest.json").write_text(bg_task.json.dumps(manifest))

        # Update should detect dead process and mark as failed
        updated = bg_task.update_task_status(task_id)
        assert updated.status == "failed"
        assert updated.finished_at is not None


class TestStartTaskEdgeCases:
    """Test start_task edge cases."""

    def test_start_task_with_worker_iteration_env(self, monkeypatch):
        """Test task picks up WORKER_ITERATION from environment."""
        task_id = f"test-env-{int(time.time())}"
        monkeypatch.setenv("WORKER_ITERATION", "42")

        try:
            meta = bg_task.start_task(
                command=["echo", "test"],
                task_id=task_id,
                timeout=10,
            )
            assert meta.worker_iteration == 42
        finally:
            bg_task.kill_task(task_id)
            bg_task.cleanup_tasks(days=0, force=True)


class TestWaitForTaskEdgeCases:
    """Test wait_for_task edge cases."""

    def test_wait_for_task_success(self):
        """Test waiting for a task that completes successfully."""
        task_id = f"test-wait-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["echo", "done"],
                task_id=task_id,
                timeout=10,
            )

            # Wait for it to complete
            meta = bg_task.wait_for_task(task_id, timeout=30, poll_interval=1)
            assert meta.status == "completed"
            assert meta.exit_code == 0
        finally:
            bg_task.cleanup_tasks(days=0, force=True)

    def test_wait_for_task_timeout(self):
        """Test wait_for_task times out properly."""
        task_id = f"test-timeout-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["sleep", "60"],
                task_id=task_id,
                timeout=120,
            )

            # Wait with short timeout - should raise TimeoutError
            with pytest.raises(TimeoutError, match="Timeout waiting"):
                bg_task.wait_for_task(task_id, timeout=2, poll_interval=1)
        finally:
            bg_task.kill_task(task_id)
            bg_task.cleanup_tasks(days=0, force=True)


class TestKillTaskEdgeCases:
    """Test kill_task edge cases."""

    def test_kill_task_already_completed(self):
        """Test killing a task that's already completed."""
        task_id = f"test-kill-done-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["echo", "fast"],
                task_id=task_id,
                timeout=10,
            )
            # Wait for completion
            time.sleep(1)
            bg_task.update_task_status(task_id)

            # Try to kill completed task
            meta = bg_task.kill_task(task_id)
            # Should return meta but not change status to killed
            assert meta is not None
            assert meta.status in ("completed", "failed")  # Already finished
        finally:
            bg_task.cleanup_tasks(days=0, force=True)

    def test_kill_task_with_sigkill_fallback(self):
        """Test kill_task uses SIGKILL when SIGTERM doesn't work."""
        task_id = f"test-sigkill-{int(time.time())}"

        try:
            # Start a task that ignores SIGTERM by trapping it
            bg_task.start_task(
                command=[
                    "bash",
                    "-c",
                    "trap '' TERM; sleep 60",
                ],
                task_id=task_id,
                timeout=120,
            )

            time.sleep(0.5)  # Let it start

            # Kill should escalate to SIGKILL
            meta = bg_task.kill_task(task_id)
            assert meta.status == "killed"

            # Verify actually dead
            time.sleep(1.5)
            assert not bg_task.is_process_alive(meta.pid)
        finally:
            bg_task.cleanup_tasks(days=0, force=True)


class TestCleanupTasksEdgeCases:
    """Test cleanup_tasks edge cases."""

    def test_cleanup_skips_running_tasks(self):
        """Test cleanup doesn't remove running tasks without force."""
        task_id = f"test-cleanup-run-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["sleep", "60"],
                task_id=task_id,
                timeout=120,
            )

            # Cleanup without force should NOT remove running task
            removed = bg_task.cleanup_tasks(days=0, force=False)
            assert task_id not in removed

            # Task should still exist
            meta = bg_task.get_status(task_id)
            assert meta is not None
            assert meta.status == "running"
        finally:
            bg_task.kill_task(task_id)
            bg_task.cleanup_tasks(days=0, force=True)

    def test_cleanup_skips_missing_meta(self, tmp_path, monkeypatch):
        """Test cleanup handles directories without meta.json."""
        tasks_dir = tmp_path / ".background_tasks"
        tasks_dir.mkdir(parents=True, exist_ok=True)
        monkeypatch.setattr(bg_task, "get_tasks_dir", lambda: tasks_dir)

        # Create directory without meta.json
        bad_dir = tasks_dir / "bad-task"
        bad_dir.mkdir()

        # Cleanup should not crash
        removed = bg_task.cleanup_tasks(days=0, force=True)
        assert "bad-task" not in removed

    def test_cleanup_handles_invalid_date(self, tmp_path, monkeypatch):
        """Test cleanup handles tasks with invalid date format."""
        tasks_dir = tmp_path / ".background_tasks"
        tasks_dir.mkdir(parents=True, exist_ok=True)
        monkeypatch.setattr(bg_task, "get_tasks_dir", lambda: tasks_dir)

        task_id = "bad-date-task"
        task_dir = tasks_dir / task_id
        task_dir.mkdir()

        # Create meta with invalid date
        meta_data = {
            "task_id": task_id,
            "command": "test",
            "description": "Test",
            "issue": None,
            "timeout": 60,
            "status": "completed",
            "started_at": "not-a-date",  # Invalid!
            "finished_at": None,
            "pid": None,
            "exit_code": 0,
            "machine": "test",
            "worker_iteration": None,
        }
        (task_dir / "meta.json").write_text(bg_task.json.dumps(meta_data))

        # Cleanup should handle gracefully
        removed = bg_task.cleanup_tasks(days=0, force=False)
        # Should not crash, and task not removed due to parsing error
        assert task_id not in removed


class TestPrintTaskTable:
    """Test print_task_table formatting."""

    def test_print_task_table_with_tasks(self, capsys):
        """Test printing table with multiple tasks."""
        tasks = [
            bg_task.TaskMeta(
                task_id="task-1",
                command="echo hello",
                description="Short desc",
                issue=42,
                timeout=60,
                status="running",
                started_at="2024-01-15T10:30:00+00:00",
                pid=1234,
            ),
            bg_task.TaskMeta(
                task_id="task-2",
                command="sleep 100",
                description="A very long description that exceeds forty characters",
                issue=None,
                timeout=120,
                status="completed",
                started_at="2024-01-15T09:00:00+00:00",
                pid=None,
                exit_code=0,
            ),
        ]

        bg_task.print_task_table(tasks)
        captured = capsys.readouterr()

        # Check header
        assert "ID" in captured.out
        assert "STATUS" in captured.out
        assert "ISSUE" in captured.out
        assert "PID" in captured.out

        # Check task-1 row
        assert "task-1" in captured.out
        assert "running" in captured.out
        assert "#42" in captured.out
        assert "1234" in captured.out

        # Check task-2 row
        assert "task-2" in captured.out
        assert "completed" in captured.out
        # Issue should show "-" when None
        # Description should be truncated with "..."
        assert "..." in captured.out

    def test_print_task_table_empty(self, capsys):
        """Test printing empty table."""
        bg_task.print_task_table([])
        captured = capsys.readouterr()
        assert "No tasks found" in captured.out


class TestHandleStartEdgeCases:
    """Test handle_start edge cases."""

    def test_handle_start_duplicate_running_task(self, capsys):
        """Test start handler error when task already running."""
        task_id = f"test-dup-handler-{int(time.time())}"

        try:
            # First start succeeds
            args1 = bg_task.CLIArgs(
                command="start",
                id=task_id,
                timeout=30,
                command_args=["sleep", "60"],
            )
            result1 = bg_task.handle_start(args1)
            assert result1 == 0

            # Second start fails with error
            args2 = bg_task.CLIArgs(
                command="start",
                id=task_id,
                timeout=30,
                command_args=["echo", "fail"],
            )
            result2 = bg_task.handle_start(args2)
            assert result2 == 1
            captured = capsys.readouterr()
            assert "Error" in captured.err
            assert "already running" in captured.err
        finally:
            bg_task.kill_task(task_id)
            bg_task.cleanup_tasks(days=0, force=True)


class TestHandleStatusSuccess:
    """Test handle_status success path."""

    def test_handle_status_existing_task(self, capsys):
        """Test status handler with existing task."""
        task_id = f"test-status-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["echo", "test"],
                task_id=task_id,
                timeout=10,
            )

            args = bg_task.CLIArgs(command="status", task_id=task_id)
            result = bg_task.handle_status(args)
            assert result == 0

            captured = capsys.readouterr()
            # Should print JSON with task_id
            assert task_id in captured.out
            assert '"task_id"' in captured.out
        finally:
            bg_task.cleanup_tasks(days=0, force=True)


class TestHandleTailEdgeCases:
    """Test handle_tail edge cases."""

    def test_handle_tail_without_follow(self, capsys):
        """Test tail handler without follow mode."""
        task_id = f"test-tail-nof-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["echo", "tail test output"],
                task_id=task_id,
                timeout=10,
            )
            time.sleep(1)

            args = bg_task.CLIArgs(
                command="tail", task_id=task_id, lines=50, follow=False
            )
            result = bg_task.handle_tail(args)
            assert result == 0

            captured = capsys.readouterr()
            assert "tail test output" in captured.out
        finally:
            bg_task.cleanup_tasks(days=0, force=True)


class TestTailFollow:
    """Test tail_follow function."""

    def test_tail_follow_completes_when_task_done(self, monkeypatch):
        """Test tail_follow exits when task completes."""
        task_id = f"test-follow-{int(time.time())}"

        # Mock os.system to avoid clearing terminal
        cleared = []
        monkeypatch.setattr(os, "system", lambda cmd: cleared.append(cmd))

        try:
            bg_task.start_task(
                command=["echo", "follow output"],
                task_id=task_id,
                timeout=10,
            )

            # tail_follow should return after task completes
            bg_task.tail_follow(task_id, lines=50)

            # Should have called clear at least once
            assert any("clear" in str(c) for c in cleared)
        finally:
            bg_task.cleanup_tasks(days=0, force=True)

    def test_tail_follow_handles_keyboard_interrupt(self, monkeypatch):
        """Test tail_follow exits cleanly on KeyboardInterrupt."""
        task_id = f"test-follow-int-{int(time.time())}"

        # Track clear calls and raise KeyboardInterrupt after first iteration
        call_count = []

        def mock_system(cmd):
            call_count.append(cmd)
            if len(call_count) > 1:
                raise KeyboardInterrupt

        monkeypatch.setattr(os, "system", mock_system)

        try:
            bg_task.start_task(
                command=["sleep", "60"],
                task_id=task_id,
                timeout=120,
            )

            # tail_follow should exit cleanly on KeyboardInterrupt
            bg_task.tail_follow(task_id, lines=50)

            # Should have exited after interrupt
            assert len(call_count) >= 1
        finally:
            bg_task.kill_task(task_id)
            bg_task.cleanup_tasks(days=0, force=True)


class TestHandleTailWithFollow:
    """Test handle_tail with follow=True."""

    def test_handle_tail_with_follow(self, monkeypatch):
        """Test tail handler with follow mode."""
        task_id = f"test-tail-follow-{int(time.time())}"

        # Mock os.system to avoid clearing terminal
        cleared = []
        monkeypatch.setattr(os, "system", lambda cmd: cleared.append(cmd))

        try:
            bg_task.start_task(
                command=["echo", "quick"],
                task_id=task_id,
                timeout=10,
            )

            args = bg_task.CLIArgs(
                command="tail", task_id=task_id, lines=50, follow=True
            )
            result = bg_task.handle_tail(args)
            assert result == 0
        finally:
            bg_task.cleanup_tasks(days=0, force=True)


class TestHandleWaitSuccess:
    """Test handle_wait success path."""

    def test_handle_wait_success_path(self, capsys):
        """Test wait handler when task completes successfully."""
        task_id = f"test-wait-handler-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["echo", "done"],
                task_id=task_id,
                timeout=10,
            )

            args = bg_task.CLIArgs(command="wait", task_id=task_id, timeout=30)
            result = bg_task.handle_wait(args)
            assert result == 0

            captured = capsys.readouterr()
            assert "completed" in captured.out
            assert "Exit code: 0" in captured.out
        finally:
            bg_task.cleanup_tasks(days=0, force=True)

    def test_handle_wait_failed_task(self, capsys):
        """Test wait handler when task fails."""
        task_id = f"test-wait-fail-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["false"],  # Exit code 1
                task_id=task_id,
                timeout=10,
            )

            args = bg_task.CLIArgs(command="wait", task_id=task_id, timeout=30)
            result = bg_task.handle_wait(args)
            assert result == 1  # Non-zero because task failed

            captured = capsys.readouterr()
            assert "failed" in captured.out
        finally:
            bg_task.cleanup_tasks(days=0, force=True)


class TestHandleKillSuccess:
    """Test handle_kill success path."""

    def test_handle_kill_success_path(self, capsys):
        """Test kill handler when task is successfully killed."""
        task_id = f"test-kill-handler-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["sleep", "60"],
                task_id=task_id,
                timeout=120,
            )

            args = bg_task.CLIArgs(command="kill", task_id=task_id)
            result = bg_task.handle_kill(args)
            assert result == 0

            captured = capsys.readouterr()
            assert "killed" in captured.out
        finally:
            bg_task.cleanup_tasks(days=0, force=True)


class TestHandleCleanupWithRemovals:
    """Test handle_cleanup when tasks are removed."""

    def test_handle_cleanup_with_removals(self, capsys):
        """Test cleanup handler when it actually removes tasks."""
        task_id = f"test-cleanup-handler-{int(time.time())}"

        try:
            bg_task.start_task(
                command=["echo", "done"],
                task_id=task_id,
                timeout=10,
            )
            time.sleep(1)  # Let it complete

            args = bg_task.CLIArgs(command="cleanup", days=0, force=True)
            result = bg_task.handle_cleanup(args)
            assert result == 0

            captured = capsys.readouterr()
            assert "Removed" in captured.out
            assert task_id in captured.out
        finally:
            pass  # Already cleaned


class TestCLI:
    """Test CLI interface."""

    def test_help(self):
        """Test help output."""
        result = subprocess.run(
            [sys.executable, "ai_template_scripts/bg_task.py", "--help"],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0
        assert "background task" in result.stdout.lower()

    def test_list_command(self):
        """Test list command."""
        result = subprocess.run(
            [sys.executable, "ai_template_scripts/bg_task.py", "list"],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0

    def test_status_nonexistent(self):
        """Test status command with nonexistent task."""
        result = subprocess.run(
            [
                sys.executable,
                "ai_template_scripts/bg_task.py",
                "status",
                "nonexistent-12345",
            ],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 1
        assert "not found" in result.stderr

    def test_cleanup_command(self):
        """Test cleanup command."""
        result = subprocess.run(
            [sys.executable, "ai_template_scripts/bg_task.py", "cleanup"],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0
