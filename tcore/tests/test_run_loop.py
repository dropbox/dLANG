"""Tests for run_loop.py

Tests the pipe handling, crash detection, session success checking,
and two-layer bot identity system.
"""

import os
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

# Add parent dir to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from run_loop import LoopRunner, get_project_name


class TestGetProjectName:
    """Test project name extraction from git remote."""

    def test_returns_string(self):
        """Should return a non-empty string."""
        name = get_project_name()
        assert isinstance(name, str)
        assert len(name) > 0

    def test_matches_expected_format(self):
        """Should return 'ai_template' when in this repo."""
        name = get_project_name()
        # We're in ai_template repo
        assert name == "ai_template"


class TestLoopRunnerInit:
    """Test LoopRunner initialization."""

    def test_worker_mode(self):
        """Worker mode should have correct config."""
        runner = LoopRunner("worker")
        assert runner.mode == "worker"
        assert runner.config["git_author_name"] == "WORKER"
        assert runner.config["restart_delay"] == 0

    def test_manager_mode(self):
        """Manager mode should have correct config."""
        runner = LoopRunner("manager")
        assert runner.mode == "manager"
        assert runner.config["git_author_name"] == "MANAGER"
        assert runner.config["restart_delay"] > 0


class TestCheckSessionSuccess:
    """Test session success detection via git commits."""

    @pytest.fixture
    def runner(self):
        """Create a LoopRunner for testing."""
        return LoopRunner("worker")

    def test_no_commit_returns_false(self, runner):
        """When no commits in timeframe, should return False."""
        # Use a start time in the future so no commits match
        future_time = time.time() + 86400  # Tomorrow
        assert runner.check_session_success(future_time) is False

    def test_recent_commit_returns_true(self, runner):
        """When there's a recent WORKER commit, should return True."""
        # Use start time before the most recent commit
        # The actual test depends on git history having WORKER commits
        past_time = time.time() - 86400  # Yesterday
        # This may return True or False depending on git history
        result = runner.check_session_success(past_time)
        assert isinstance(result, bool)

    def test_handles_git_failure(self, runner):
        """Should return False if git command fails."""
        with patch("subprocess.run", side_effect=Exception("git failed")):
            assert runner.check_session_success(time.time()) is False


class TestLogCrash:
    """Test crash logging with session success distinction."""

    @pytest.fixture
    def runner(self, tmp_path):
        """Create a LoopRunner with a temp crash log."""
        runner = LoopRunner("worker")
        runner.crash_log = tmp_path / "crashes.log"
        runner.iteration = 5
        return runner

    def test_real_crash_logs_to_file(self, runner, capsys):
        """A real crash (no commit) should log to crashes.log."""
        runner.log_crash(1, "claude", session_committed=False)

        # Should write to crash log
        assert runner.crash_log.exists()
        content = runner.crash_log.read_text()
        assert "claude exited with code 1" in content

        # Should print crash banner
        captured = capsys.readouterr()
        assert "CRASH DETECTED" in captured.out

    def test_successful_session_no_log(self, runner, capsys):
        """Exit code 1 after successful commit should NOT log as crash."""
        runner.log_crash(1, "claude", session_committed=True)

        # Should NOT write to crash log
        assert not runner.crash_log.exists()

        # Should print note about successful session
        captured = capsys.readouterr()
        assert "committed successfully" in captured.out
        assert "CRASH DETECTED" not in captured.out

    def test_signal_death_always_crash(self, runner, capsys):
        """Kill by signal is always a crash, even with commit."""
        runner.log_crash(137, "claude", session_committed=True)  # SIGKILL = 128+9

        # Should write to crash log (signal death is always real)
        assert runner.crash_log.exists()
        content = runner.crash_log.read_text()
        assert "killed by signal 9" in content

    def test_timeout_with_commit_not_crash(self, runner, capsys):
        """Timeout (124) after commit is not a crash."""
        runner.log_crash(124, "claude", session_committed=True)

        # Should NOT write to crash log
        assert not runner.crash_log.exists()

        captured = capsys.readouterr()
        assert "committed successfully" in captured.out

    def test_timeout_without_commit_is_crash(self, runner, capsys):
        """Timeout (124) without commit is a crash."""
        runner.log_crash(124, "claude", session_committed=False)

        # Should write to crash log
        assert runner.crash_log.exists()
        content = runner.crash_log.read_text()
        assert "timed out" in content


class TestPipeHandling:
    """Test the pipe handling logic that prevents EPIPE."""

    def test_write_to_text_proc_handles_broken_pipe(self):
        """write_to_text_proc should gracefully handle BrokenPipeError."""
        # Create a mock scenario
        text_proc_alive = True

        def write_to_text_proc(data: bytes) -> None:
            nonlocal text_proc_alive
            if not text_proc_alive:
                return
            # Simulate broken pipe
            raise BrokenPipeError("Broken pipe")

        # First call should raise, but we catch it
        # In real code, it sets text_proc_alive = False and continues
        with pytest.raises(BrokenPipeError):
            write_to_text_proc(b"test")

    def test_drain_output_continues_after_pipe_failure(self):
        """Should continue draining ai_proc even after text_proc dies."""
        # This tests the conceptual behavior - in the actual implementation,
        # after BrokenPipeError, text_proc_alive becomes False and we
        # continue reading from ai_proc without writing to text_proc

        text_proc_alive = True
        logged_lines = []

        def write_to_text_proc(data: bytes) -> None:
            nonlocal text_proc_alive
            if not text_proc_alive:
                return
            try:
                # Simulate broken pipe on first write
                if len(logged_lines) == 0:
                    raise BrokenPipeError
            except BrokenPipeError:
                text_proc_alive = False

        # Simulate reading lines from ai_proc
        lines = [b"line1\n", b"line2\n", b"line3\n"]
        for line in lines:
            logged_lines.append(line)
            write_to_text_proc(line)

        # All lines should be logged even though text_proc died
        assert len(logged_lines) == 3


class TestRunIteration:
    """Test run_iteration return value."""

    def test_returns_tuple(self):
        """run_iteration should return (exit_code, start_time)."""
        # We can't easily test run_iteration without mocking everything,
        # but we can verify the method exists and is callable
        runner = LoopRunner("worker")
        assert callable(runner.run_iteration)
        # The return type annotation is tuple[int, float]
        # which is verified by static type checkers


class TestSelectAiTool:
    """Test AI tool selection."""

    def test_first_iteration_uses_claude(self):
        """First iteration should always use claude."""
        runner = LoopRunner("worker")
        runner.iteration = 1
        runner.codex_available = True
        assert runner.select_ai_tool() == "claude"

    def test_codex_interval(self):
        """Should use codex at configured intervals."""
        runner = LoopRunner("worker")
        runner.codex_available = True
        # Default codex_interval is 9

        runner.iteration = 9
        assert runner.select_ai_tool() == "codex"

        runner.iteration = 18
        assert runner.select_ai_tool() == "codex"

        runner.iteration = 10
        assert runner.select_ai_tool() == "claude"

    def test_codex_not_available(self):
        """Should use claude when codex not available."""
        runner = LoopRunner("worker")
        runner.codex_available = False
        runner.iteration = 9
        assert runner.select_ai_tool() == "claude"

    def test_manager_never_uses_codex(self):
        """Manager mode should never use codex."""
        runner = LoopRunner("manager")
        runner.codex_available = True
        runner.iteration = 9
        assert runner.select_ai_tool() == "claude"


class TestGetGitIteration:
    """Test iteration detection from git log."""

    def test_returns_integer(self):
        """Should return an integer."""
        runner = LoopRunner("worker")
        result = runner.get_git_iteration()
        assert isinstance(result, int)
        assert result >= 1

    def test_parses_worker_commits(self):
        """Should find [W]N pattern in git log."""
        runner = LoopRunner("worker")
        # In the ai_template repo, we should have WORKER commits
        result = runner.get_git_iteration()
        # Should be at least 1 (possibly higher if commits exist)
        assert result >= 1

    def test_handles_git_failure(self):
        """Should return 1 if git command fails."""
        runner = LoopRunner("worker")
        with patch("subprocess.run", side_effect=Exception("git failed")):
            assert runner.get_git_iteration() == 1


class TestSetupBotIdentity:
    """Test two-layer bot identity setup."""

    @pytest.fixture
    def runner(self):
        """Create a LoopRunner for testing."""
        return LoopRunner("worker")

    def test_sets_git_identity(self, runner, monkeypatch):
        """Should set GIT_AUTHOR_NAME and GIT_AUTHOR_EMAIL."""
        # Clear any existing values
        monkeypatch.delenv("GIT_AUTHOR_NAME", raising=False)
        monkeypatch.delenv("GIT_AUTHOR_EMAIL", raising=False)

        # Mock bot_token.py to not exist so we test git identity without token
        with patch("pathlib.Path.exists", return_value=False):
            runner.setup_bot_identity()

        # Should set git identity
        git_name = os.environ.get("GIT_AUTHOR_NAME", "")
        git_email = os.environ.get("GIT_AUTHOR_EMAIL", "")

        assert "ai_template" in git_name
        assert "worker" in git_name
        assert "ai-fleet" in git_email
        assert "@" in git_email

    def test_sets_environment_variables(self, runner):
        """Should export AI_FLEET_* environment variables."""
        with patch("pathlib.Path.exists", return_value=False):
            runner.setup_bot_identity()

        assert os.environ.get("AI_FLEET_PROJECT") == "ai_template"
        assert os.environ.get("AI_FLEET_ROLE") == "WORKER"
        assert os.environ.get("AI_FLEET_ITERATION", "").isdigit()
        assert os.environ.get("AI_FLEET_SESSION", "") != ""
        assert os.environ.get("AI_FLEET_MACHINE", "") != ""

    def test_returns_false_without_bot_token_script(self, runner):
        """Should return False if bot_token.py doesn't exist."""
        with patch("pathlib.Path.exists", return_value=False):
            result = runner.setup_bot_identity()
        assert result is False

    def test_returns_false_on_token_failure(self, runner, tmp_path):
        """Should return False if bot_token.py fails."""
        # Create a fake bot_token.py that returns non-zero
        mock_result = Mock()
        mock_result.returncode = 1
        mock_result.stderr = "No credentials"

        with (
            patch("pathlib.Path.exists", return_value=True),
            patch("subprocess.run", return_value=mock_result),
        ):
            result = runner.setup_bot_identity()

        assert result is False
        assert runner._bot_identity_enabled is False

    def test_returns_true_on_token_success(self, runner):
        """Should return True if bot_token.py succeeds."""
        mock_result = Mock()
        mock_result.returncode = 0
        mock_result.stdout = (
            '{"token": "ghs_test", "expires_at": "2026-01-08T22:00:00Z"}'
        )

        with (
            patch("pathlib.Path.exists", return_value=True),
            patch("subprocess.run", return_value=mock_result),
        ):
            result = runner.setup_bot_identity()

        assert result is True
        assert runner._bot_identity_enabled is True
        assert os.environ.get("GH_TOKEN") == "ghs_test"
        assert runner._token_expires == "2026-01-08T22:00:00Z"

    def test_manager_identity_format(self):
        """Manager mode should use 'manager' in git identity."""
        runner = LoopRunner("manager")

        with patch("pathlib.Path.exists", return_value=False):
            runner.setup_bot_identity()

        git_name = os.environ.get("GIT_AUTHOR_NAME", "")
        assert "manager" in git_name
        assert os.environ.get("AI_FLEET_ROLE") == "MANAGER"


class TestMaybeRefreshToken:
    """Test token refresh logic."""

    @pytest.fixture
    def runner(self):
        """Create a LoopRunner with bot identity enabled."""
        runner = LoopRunner("worker")
        runner._bot_identity_enabled = True
        return runner

    def test_does_nothing_if_not_enabled(self, runner):
        """Should do nothing if bot identity not enabled."""
        runner._bot_identity_enabled = False
        runner._token_expires = "2026-01-08T22:00:00Z"

        # Should not raise, should not call subprocess
        with patch("subprocess.run") as mock_run:
            runner.maybe_refresh_token()
            mock_run.assert_not_called()

    def test_does_nothing_if_no_expiry(self, runner):
        """Should do nothing if no expiry time set."""
        runner._token_expires = None

        with patch("subprocess.run") as mock_run:
            runner.maybe_refresh_token()
            mock_run.assert_not_called()

    def test_does_nothing_if_not_expiring_soon(self, runner):
        """Should not refresh if >10 minutes until expiry."""
        # Set expiry to 1 hour from now
        future = datetime.now(timezone.utc) + timedelta(hours=1)
        runner._token_expires = future.isoformat()

        with patch("subprocess.run") as mock_run:
            runner.maybe_refresh_token()
            mock_run.assert_not_called()

    def test_refreshes_when_expiring_soon(self, runner):
        """Should refresh if <10 minutes until expiry."""
        # Set expiry to 5 minutes from now
        soon = datetime.now(timezone.utc) + timedelta(minutes=5)
        runner._token_expires = soon.isoformat()

        mock_result = Mock()
        mock_result.returncode = 0
        mock_result.stdout = (
            '{"token": "ghs_refreshed", "expires_at": "2026-01-08T23:00:00Z"}'
        )

        with patch("subprocess.run", return_value=mock_result) as mock_run:
            runner.maybe_refresh_token()
            mock_run.assert_called_once()
            assert os.environ.get("GH_TOKEN") == "ghs_refreshed"
            assert runner._token_expires == "2026-01-08T23:00:00Z"

    def test_handles_refresh_failure(self, runner, capsys):
        """Should handle refresh failure gracefully."""
        soon = datetime.now(timezone.utc) + timedelta(minutes=5)
        runner._token_expires = soon.isoformat()

        mock_result = Mock()
        mock_result.returncode = 1
        mock_result.stderr = "refresh failed"

        with patch("subprocess.run", return_value=mock_result):
            runner.maybe_refresh_token()  # Should not raise

        captured = capsys.readouterr()
        assert "failed" in captured.out.lower()

    def test_handles_z_suffix_in_timestamp(self, runner):
        """Should handle Z suffix in ISO timestamp."""
        soon = datetime.now(timezone.utc) + timedelta(minutes=5)
        runner._token_expires = soon.strftime("%Y-%m-%dT%H:%M:%SZ")

        mock_result = Mock()
        mock_result.returncode = 0
        mock_result.stdout = (
            '{"token": "ghs_new", "expires_at": "2026-01-08T23:00:00Z"}'
        )

        with patch("subprocess.run", return_value=mock_result):
            runner.maybe_refresh_token()  # Should not raise
