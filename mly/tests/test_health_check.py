"""Tests for health_check.py system health monitoring."""

import json
import subprocess
import sys
from datetime import datetime, timedelta
from pathlib import Path
from unittest.mock import MagicMock

# Add ai_template_scripts to path
sys.path.insert(0, str(Path(__file__).parent.parent / "ai_template_scripts"))

import health_check


class TestCrashEntry:
    """Test CrashEntry dataclass."""

    def test_creation(self):
        entry = health_check.CrashEntry(
            timestamp=datetime(2026, 1, 8, 15, 30, 45),
            iteration=5,
            message="claude exited with code 1",
        )
        assert entry.iteration == 5
        assert entry.message == "claude exited with code 1"
        assert entry.timestamp.year == 2026


class TestHealthReport:
    """Test HealthReport dataclass."""

    def test_creation(self):
        report = health_check.HealthReport(
            total_iterations=100,
            total_crashes=10,
            recent_crashes=2,
            failure_rate=0.02,
            status="healthy",
            crash_patterns={"timeout": 1, "exit_error": 1},
            recommendation="System operating normally.",
        )
        assert report.total_iterations == 100
        assert report.status == "healthy"
        assert report.crash_patterns["timeout"] == 1


class TestParseCrashesLog:
    """Test crash log parsing."""

    def test_empty_file(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text("")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        entries = health_check.parse_crashes_log()
        assert entries == []

    def test_nonexistent_file(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "nonexistent.log"
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        entries = health_check.parse_crashes_log()
        assert entries == []

    def test_single_entry(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text(
            "[2026-01-08 15:30:45] Iteration 5: claude exited with code 1\n",
        )
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        entries = health_check.parse_crashes_log()
        assert len(entries) == 1
        assert entries[0].iteration == 5
        assert entries[0].message == "claude exited with code 1"

    def test_multiple_entries(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text(
            "[2026-01-08 10:00:00] Iteration 1: claude timed out\n"
            "[2026-01-08 11:00:00] Iteration 2: claude killed by signal 9\n"
            "[2026-01-08 12:00:00] Iteration 3: claude exited with code 1\n",
        )
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        entries = health_check.parse_crashes_log()
        assert len(entries) == 3
        # Sorted newest first
        assert entries[0].iteration == 3
        assert entries[1].iteration == 2
        assert entries[2].iteration == 1

    def test_filter_by_since(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text(
            "[2026-01-07 10:00:00] Iteration 1: old crash\n"
            "[2026-01-08 10:00:00] Iteration 2: recent crash\n",
        )
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        # Filter to only crashes after Jan 8
        since = datetime(2026, 1, 8, 0, 0, 0)
        entries = health_check.parse_crashes_log(since=since)
        assert len(entries) == 1
        assert entries[0].iteration == 2

    def test_malformed_lines_ignored(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text(
            "not a valid line\n"
            "[2026-01-08 15:30:45] Iteration 5: valid crash\n"
            "another invalid line\n",
        )
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        entries = health_check.parse_crashes_log()
        assert len(entries) == 1
        assert entries[0].iteration == 5


class TestCountIterationsSince:
    """Test git iteration counting."""

    def test_counts_worker_commits(self, monkeypatch):
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "[W]1: First\n[W]2: Second\n[W]3: Third\n"

        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        since = datetime.now() - timedelta(hours=24)
        count = health_check.count_iterations_since(since)
        assert count == 3

    def test_handles_git_error(self, monkeypatch):
        mock_result = MagicMock()
        mock_result.returncode = 1
        mock_result.stdout = ""

        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        since = datetime.now()
        count = health_check.count_iterations_since(since)
        assert count == 0

    def test_handles_empty_output(self, monkeypatch):
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = ""

        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        since = datetime.now()
        count = health_check.count_iterations_since(since)
        assert count == 0

    def test_handles_exception(self, monkeypatch):
        def raise_error(*args, **kwargs):
            raise subprocess.TimeoutExpired("git", 10)

        monkeypatch.setattr(subprocess, "run", raise_error)

        since = datetime.now()
        count = health_check.count_iterations_since(since)
        assert count == 0


class TestAnalyzeCrashPatterns:
    """Test crash pattern analysis."""

    def test_empty_list(self):
        patterns = health_check.analyze_crash_patterns([])
        assert patterns == {}

    def test_signal_kills(self):
        crashes = [
            health_check.CrashEntry(datetime.now(), 1, "claude killed by signal 9"),
            health_check.CrashEntry(datetime.now(), 2, "claude killed by signal 15"),
        ]
        patterns = health_check.analyze_crash_patterns(crashes)
        assert patterns["signal_kill"] == 2

    def test_timeouts(self):
        crashes = [
            health_check.CrashEntry(datetime.now(), 1, "claude timed out"),
        ]
        patterns = health_check.analyze_crash_patterns(crashes)
        assert patterns["timeout"] == 1

    def test_exit_errors(self):
        crashes = [
            health_check.CrashEntry(datetime.now(), 1, "claude exited with code 1"),
            health_check.CrashEntry(datetime.now(), 2, "claude exited with code 137"),
        ]
        patterns = health_check.analyze_crash_patterns(crashes)
        assert patterns["exit_error"] == 2

    def test_mixed_patterns(self):
        crashes = [
            health_check.CrashEntry(datetime.now(), 1, "claude killed by signal 9"),
            health_check.CrashEntry(datetime.now(), 2, "claude timed out"),
            health_check.CrashEntry(datetime.now(), 3, "claude exited with code 1"),
            health_check.CrashEntry(datetime.now(), 4, "some unknown error"),
        ]
        patterns = health_check.analyze_crash_patterns(crashes)
        assert patterns["signal_kill"] == 1
        assert patterns["timeout"] == 1
        assert patterns["exit_error"] == 1
        assert patterns["unknown"] == 1


class TestGetHealthReport:
    """Test health report generation."""

    def test_healthy_status(self, tmp_path, monkeypatch):
        # No crashes, 10 iterations = healthy
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text("")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "\n".join([f"[W]{i}: work" for i in range(10)])
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        report = health_check.get_health_report(hours=24)
        assert report.status == "healthy"
        assert report.failure_rate == 0.0
        assert "operating normally" in report.recommendation

    def test_warning_status(self, tmp_path, monkeypatch):
        # Set up: 3 crashes, 7 successful = 30% failure rate
        crash_log = tmp_path / "crashes.log"
        now = datetime.now()
        lines = []
        for i in range(3):
            ts = (now - timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
            lines.append(f"[{ts}] Iteration {i}: claude exited with code 1")
        crash_log.write_text("\n".join(lines) + "\n")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "\n".join([f"[W]{i}: work" for i in range(7)])
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        report = health_check.get_health_report(hours=24)
        assert report.status == "warning"
        assert 0.25 <= report.failure_rate < 0.50
        assert "Monitor" in report.recommendation

    def test_critical_status(self, tmp_path, monkeypatch):
        # Set up: 6 crashes, 4 successful = 60% failure rate
        crash_log = tmp_path / "crashes.log"
        now = datetime.now()
        lines = []
        for i in range(6):
            ts = (now - timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
            lines.append(f"[{ts}] Iteration {i}: claude exited with code 1")
        crash_log.write_text("\n".join(lines) + "\n")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "\n".join([f"[W]{i}: work" for i in range(4)])
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        report = health_check.get_health_report(hours=24)
        assert report.status == "critical"
        assert report.failure_rate >= 0.50
        assert "ESCALATE" in report.recommendation

    def test_no_attempts(self, tmp_path, monkeypatch):
        # No crashes, no iterations = healthy (0/0 = 0%)
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text("")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = ""
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        report = health_check.get_health_report(hours=24)
        assert report.status == "healthy"
        assert report.failure_rate == 0.0


class TestFormatReport:
    """Test report formatting."""

    def test_healthy_format(self):
        report = health_check.HealthReport(
            total_iterations=100,
            total_crashes=5,
            recent_crashes=0,
            failure_rate=0.0,
            status="healthy",
            crash_patterns={},
            recommendation="System operating normally.",
        )
        formatted = health_check.format_report(report, hours=24)
        assert "[OK]" in formatted
        assert "100 successful" in formatted
        assert "0.0%" in formatted

    def test_warning_format(self):
        report = health_check.HealthReport(
            total_iterations=70,
            total_crashes=30,
            recent_crashes=10,
            failure_rate=0.30,
            status="warning",
            crash_patterns={"timeout": 5, "exit_error": 5},
            recommendation="Monitor.",
        )
        formatted = health_check.format_report(report, hours=24)
        assert "[WARN]" in formatted
        assert "30.0%" in formatted
        assert "timeout: 5" in formatted

    def test_critical_format(self):
        report = health_check.HealthReport(
            total_iterations=40,
            total_crashes=60,
            recent_crashes=30,
            failure_rate=0.60,
            status="critical",
            crash_patterns={"signal_kill": 20, "timeout": 10},
            recommendation="ESCALATE.",
        )
        formatted = health_check.format_report(report, hours=24)
        assert "[CRITICAL]" in formatted
        assert "60.0%" in formatted


class TestMain:
    """Test main CLI entry point."""

    def test_healthy_returns_zero(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text("")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "[W]1: work\n[W]2: work\n"
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        monkeypatch.setattr(sys, "argv", ["health_check.py"])
        exit_code = health_check.main()
        assert exit_code == 0

    def test_warning_returns_one(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "crashes.log"
        now = datetime.now()
        lines = []
        for i in range(3):
            ts = (now - timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
            lines.append(f"[{ts}] Iteration {i}: crash")
        crash_log.write_text("\n".join(lines) + "\n")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "\n".join([f"[W]{i}: work" for i in range(7)])
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        monkeypatch.setattr(sys, "argv", ["health_check.py"])
        exit_code = health_check.main()
        assert exit_code == 1

    def test_critical_returns_two(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "crashes.log"
        now = datetime.now()
        lines = []
        for i in range(6):
            ts = (now - timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
            lines.append(f"[{ts}] Iteration {i}: crash")
        crash_log.write_text("\n".join(lines) + "\n")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "\n".join([f"[W]{i}: work" for i in range(4)])
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        monkeypatch.setattr(sys, "argv", ["health_check.py"])
        exit_code = health_check.main()
        assert exit_code == 2

    def test_quiet_mode_healthy(self, tmp_path, monkeypatch, capsys):
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text("")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "[W]1: work\n"
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        monkeypatch.setattr(sys, "argv", ["health_check.py", "--quiet"])
        exit_code = health_check.main()
        assert exit_code == 0
        captured = capsys.readouterr()
        assert captured.out == ""  # No output in quiet mode when healthy

    def test_json_output(self, tmp_path, monkeypatch, capsys):
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text("")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "[W]1: work\n"
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        monkeypatch.setattr(sys, "argv", ["health_check.py", "--json"])
        exit_code = health_check.main()
        assert exit_code == 0
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        assert "status" in data
        assert "failure_rate" in data
        assert data["status"] == "healthy"

    def test_hours_parameter(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text("")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = ""
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        monkeypatch.setattr(sys, "argv", ["health_check.py", "--hours", "48"])
        exit_code = health_check.main()
        assert exit_code == 0


class TestEdgeCases:
    """Test edge cases and boundary conditions."""

    def test_exactly_25_percent_is_warning(self, tmp_path, monkeypatch):
        # 1 crash, 3 successful = 25% exactly
        crash_log = tmp_path / "crashes.log"
        now = datetime.now()
        ts = (now - timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
        crash_log.write_text(f"[{ts}] Iteration 1: crash\n")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "\n".join([f"[W]{i}: work" for i in range(3)])
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        report = health_check.get_health_report(hours=24)
        assert report.status == "warning"
        assert abs(report.failure_rate - 0.25) < 0.01

    def test_exactly_50_percent_is_critical(self, tmp_path, monkeypatch):
        # 5 crashes, 5 successful = 50% exactly
        crash_log = tmp_path / "crashes.log"
        now = datetime.now()
        lines = []
        for i in range(5):
            ts = (now - timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
            lines.append(f"[{ts}] Iteration {i}: crash")
        crash_log.write_text("\n".join(lines) + "\n")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "\n".join([f"[W]{i}: work" for i in range(5)])
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        report = health_check.get_health_report(hours=24)
        assert report.status == "critical"
        assert abs(report.failure_rate - 0.50) < 0.01

    def test_all_crashes_no_success(self, tmp_path, monkeypatch):
        # 5 crashes, 0 successful = 100%
        crash_log = tmp_path / "crashes.log"
        now = datetime.now()
        lines = []
        for i in range(5):
            ts = (now - timedelta(hours=1)).strftime("%Y-%m-%d %H:%M:%S")
            lines.append(f"[{ts}] Iteration {i}: crash")
        crash_log.write_text("\n".join(lines) + "\n")
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = ""
        monkeypatch.setattr(subprocess, "run", lambda *args, **kwargs: mock_result)

        report = health_check.get_health_report(hours=24)
        assert report.status == "critical"
        assert report.failure_rate == 1.0

    def test_unicode_in_crash_message(self, tmp_path, monkeypatch):
        crash_log = tmp_path / "crashes.log"
        crash_log.write_text(
            "[2026-01-08 15:30:45] Iteration 5: error with unicode \u2192\n",
        )
        monkeypatch.setattr(health_check, "CRASHES_LOG", crash_log)

        entries = health_check.parse_crashes_log()
        assert len(entries) == 1
        assert "\u2192" in entries[0].message
