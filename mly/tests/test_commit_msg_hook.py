"""
Tests for commit-msg-hook.sh

Tests the git commit message hook that:
- Adds [W]N or [M]N prefix
- Warns on missing ## Changes and ## Next sections
- Validates issue links when present
"""

import os
import subprocess
import tempfile
from pathlib import Path

import pytest

HOOK_PATH = Path(__file__).parent.parent / "ai_template_scripts" / "commit-msg-hook.sh"


def run_hook(msg: str, role: str = "WORKER", setup_git: bool = True) -> tuple[int, str, str]:
    """Run the commit-msg hook with a message and return (exit_code, new_msg, stderr)."""
    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir = Path(tmpdir)

        if setup_git:
            # Initialize a git repo so git log works
            subprocess.run(["git", "init"], cwd=tmpdir, capture_output=True)
            subprocess.run(
                ["git", "config", "user.email", "test@test.com"],
                cwd=tmpdir,
                capture_output=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "Test"],
                cwd=tmpdir,
                capture_output=True,
            )

        # Write message to temp file
        msg_file = tmpdir / "COMMIT_MSG"
        msg_file.write_text(msg)

        # Run hook
        env = os.environ.copy()
        env["AI_FLEET_ROLE"] = role

        result = subprocess.run(
            ["bash", str(HOOK_PATH), str(msg_file)],
            cwd=tmpdir,
            capture_output=True,
            text=True,
            env=env,
        )

        new_msg = msg_file.read_text() if msg_file.exists() else ""
        return result.returncode, new_msg, result.stderr


class TestPrefixAddition:
    """Test that [W]N or [M]N prefix is added correctly."""

    def test_worker_prefix_added(self):
        """Worker commits get [W]N: prefix."""
        exit_code, new_msg, _ = run_hook("Fix the bug\n\n## Changes\nFixed it\n\n## Next\nTest it")
        assert exit_code == 0
        assert new_msg.startswith("[W]1: Fix the bug")

    def test_manager_prefix_added(self):
        """Manager commits get [M]N: prefix."""
        exit_code, new_msg, _ = run_hook(
            "Audit worker progress\n\n## Changes\nReviewed\n\n## Next\nContinue",
            role="MANAGER",
        )
        assert exit_code == 0
        assert new_msg.startswith("[M]1: Audit worker progress")

    def test_existing_prefix_not_duplicated(self):
        """Commits with existing prefix don't get double-prefixed."""
        exit_code, new_msg, _ = run_hook("[W]5: Already prefixed\n\n## Changes\nDone\n\n## Next\nMore")
        assert exit_code == 0
        # Should skip processing entirely
        assert "[W]5: Already prefixed" in new_msg
        assert "[W]1: [W]5:" not in new_msg


class TestStructureWarnings:
    """Test that warnings are issued for missing sections."""

    def test_warning_missing_changes(self):
        """Warning issued when ## Changes is missing."""
        exit_code, _, stderr = run_hook("Fix bug\n\n## Next\nTest it")
        assert exit_code == 0  # Warning, not error
        assert "Missing '## Changes'" in stderr

    def test_warning_missing_next(self):
        """Warning issued when ## Next is missing."""
        exit_code, _, stderr = run_hook("Fix bug\n\n## Changes\nFixed it")
        assert exit_code == 0  # Warning, not error
        assert "Missing '## Next'" in stderr

    def test_no_warning_when_complete(self):
        """No warnings when both sections present."""
        exit_code, _, stderr = run_hook("Fix bug\n\n## Changes\nFixed\n\n## Next\nTest")
        assert exit_code == 0
        assert "Missing" not in stderr

    def test_warning_no_issue_for_worker(self):
        """Worker gets warning when no issue link."""
        exit_code, _, stderr = run_hook("Fix bug\n\n## Changes\nFixed\n\n## Next\nTest")
        assert exit_code == 0
        assert "No issue link" in stderr

    def test_no_issue_warning_for_maintain(self):
        """No issue warning for [maintain] commits."""
        exit_code, _, stderr = run_hook("[maintain] Clean up code\n\n## Changes\nCleaned\n\n## Next\nMore")
        assert exit_code == 0
        assert "No issue link" not in stderr


class TestIssueValidation:
    """Test issue link handling.

    Note: These tests may fail if gh CLI tries to validate issues against
    a real GitHub repo. We test pattern detection, not GitHub API calls.
    """

    def test_fixes_pattern_detected(self):
        """Fixes #N pattern is detected (no issue warning)."""
        # Note: May exit 1 if gh tries to validate non-existent issue
        _, _, stderr = run_hook(
            "Fix bug\n\nFixes #42\n\n## Changes\nFixed\n\n## Next\nTest"
        )
        # The key assertion: no "No issue link" warning because pattern was found
        assert "No issue link" not in stderr

    def test_part_of_pattern_detected(self):
        """Part of #N pattern is detected (no issue warning)."""
        _, _, stderr = run_hook(
            "Add feature\n\nPart of #10\n\n## Changes\nAdded\n\n## Next\nMore"
        )
        assert "No issue link" not in stderr

    def test_re_pattern_detected(self):
        """Re: #N pattern is detected (no issue warning)."""
        _, _, stderr = run_hook(
            "Review work\n\nRe: #55\n\n## Changes\nReviewed\n\n## Next\nContinue",
            role="MANAGER",
        )
        # Manager doesn't get issue warnings anyway, but pattern should be detected
        assert "No issue link" not in stderr


class TestTypeDetection:
    """Test that commit type is detected from keywords."""

    def test_fix_type(self):
        """'fix' keyword detected."""
        _, new_msg, _ = run_hook("Fix the parser\n\n## Changes\nFixed\n\n## Next\nTest")
        assert "Type: fix" in new_msg

    def test_feat_type(self):
        """'add' keyword detected as feat."""
        _, new_msg, _ = run_hook("Add new feature\n\n## Changes\nAdded\n\n## Next\nTest")
        assert "Type: feat" in new_msg

    def test_refactor_type(self):
        """'refactor' keyword detected."""
        _, new_msg, _ = run_hook("Refactor the code\n\n## Changes\nRefactored\n\n## Next\nTest")
        assert "Type: refactor" in new_msg

    def test_docs_type(self):
        """'doc' keyword detected."""
        _, new_msg, _ = run_hook("Document the API\n\n## Changes\nDocumented\n\n## Next\nMore")
        assert "Type: docs" in new_msg

    def test_audit_type(self):
        """'audit' keyword detected."""
        _, new_msg, _ = run_hook(
            "Audit worker commits\n\n## Changes\nAudited\n\n## Next\nContinue",
            role="MANAGER",
        )
        assert "Type: audit" in new_msg

    def test_maintain_type(self):
        """[maintain] tag detected."""
        _, new_msg, _ = run_hook("[maintain] Clean dead code\n\n## Changes\nCleaned\n\n## Next\nMore")
        assert "Type: maintain" in new_msg


class TestTrailers:
    """Test that trailers are added correctly."""

    def test_role_trailer(self):
        """Role trailer added."""
        _, new_msg, _ = run_hook("Fix\n\n## Changes\nX\n\n## Next\nY")
        assert "Role: WORKER" in new_msg

    def test_iteration_trailer(self):
        """Iteration trailer added."""
        _, new_msg, _ = run_hook("Fix\n\n## Changes\nX\n\n## Next\nY")
        assert "Iteration: 1" in new_msg

    def test_timestamp_trailer(self):
        """Timestamp trailer added."""
        _, new_msg, _ = run_hook("Fix\n\n## Changes\nX\n\n## Next\nY")
        assert "Timestamp: " in new_msg


class TestMergeCommits:
    """Test that merge commits are skipped."""

    def test_merge_commit_skipped(self):
        """Merge commits pass through unchanged."""
        original = "Merge branch 'feature' into main"
        exit_code, new_msg, _ = run_hook(original)
        assert exit_code == 0
        assert new_msg == original  # Unchanged
