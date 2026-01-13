"""
Tests for ai-fleet MCP plugin.

Tests core functions with mocked subprocess calls to avoid hitting GitHub API.
"""

import importlib.util
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from unittest.mock import patch


# Load module from specific path to avoid conflicts
def load_module_from_path(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# Load ai-fleet server
ai_fleet_server = load_module_from_path(
    "ai_fleet_server",
    Path(__file__).parent.parent / ".claude/plugins/ai-fleet/server.py",
)

# Import from loaded module
get_project_name = ai_fleet_server.get_project_name
get_current_commit = ai_fleet_server.get_current_commit
get_worker_iteration = ai_fleet_server.get_worker_iteration
get_role = ai_fleet_server.get_role
get_identity = ai_fleet_server.get_identity
validate_issue = ai_fleet_server.validate_issue
has_label = ai_fleet_server.has_label
get_claim_metadata = ai_fleet_server.get_claim_metadata
parse_claim_comment = ai_fleet_server.parse_claim_comment
check_claim_staleness = ai_fleet_server.check_claim_staleness
parse_readme_metadata = ai_fleet_server.parse_readme_metadata
NEWS_TYPE_MAP = ai_fleet_server.NEWS_TYPE_MAP
DIRECTOR_OPTIONS = ai_fleet_server.DIRECTOR_OPTIONS


class TestGetProjectName:
    """Test get_project_name function."""

    def test_extracts_from_git_remote(self):
        """Extracts project name from git remote URL."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (0, "git@github.com:user/my-project.git", "")
            assert get_project_name() == "my-project"

    def test_handles_https_url(self):
        """Handles HTTPS remote URLs."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (0, "https://github.com/user/test-repo.git", "")
            assert get_project_name() == "test-repo"

    def test_falls_back_to_cwd(self):
        """Falls back to current directory name on git failure."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (1, "", "not a git repo")
            # Should return basename of cwd
            result = get_project_name()
            assert result  # Just verify it returns something


class TestGetCurrentCommit:
    """Test get_current_commit function."""

    def test_returns_short_hash(self):
        """Returns short commit hash."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (0, "abc1234", "")
            assert get_current_commit() == "abc1234"

    def test_returns_unknown_on_failure(self):
        """Returns 'unknown' when git command fails."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (1, "", "not a repo")
            assert get_current_commit() == "unknown"


class TestGetWorkerIteration:
    """Test get_worker_iteration function."""

    def test_parses_iteration_from_log(self):
        """Extracts iteration number from git log."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (
                0,
                "abc1234 [W]42: Some work\ndef5678 [W]41: Previous",
                "",
            )
            assert get_worker_iteration() == 42

    def test_returns_zero_when_no_worker_commits(self):
        """Returns 0 when no [W]N commits found."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (
                0,
                "abc1234 Regular commit\ndef5678 Another commit",
                "",
            )
            assert get_worker_iteration() == 0

    def test_returns_zero_on_git_failure(self):
        """Returns 0 when git log fails."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (1, "", "error")
            assert get_worker_iteration() == 0


class TestGetRole:
    """Test get_role function."""

    def test_worker_role_legacy(self):
        """Returns WORKER when GIT_AUTHOR_NAME is WORKER (legacy format)."""
        with patch.dict(os.environ, {"GIT_AUTHOR_NAME": "WORKER"}, clear=True):
            assert get_role() == "WORKER"

    def test_manager_role_legacy(self):
        """Returns MANAGER when GIT_AUTHOR_NAME is MANAGER (legacy format)."""
        with patch.dict(os.environ, {"GIT_AUTHOR_NAME": "MANAGER"}, clear=True):
            assert get_role() == "MANAGER"

    def test_worker_role_new_format(self):
        """Returns WORKER when GIT_AUTHOR_NAME contains -worker-."""
        with patch.dict(
            os.environ, {"GIT_AUTHOR_NAME": "ai_template-worker-17"}, clear=True
        ):
            assert get_role() == "WORKER"

    def test_manager_role_new_format(self):
        """Returns MANAGER when GIT_AUTHOR_NAME contains -manager-."""
        with patch.dict(os.environ, {"GIT_AUTHOR_NAME": "z4-manager-3"}, clear=True):
            assert get_role() == "MANAGER"

    def test_ai_fleet_role_env_var_priority(self):
        """AI_FLEET_ROLE env var takes priority over GIT_AUTHOR_NAME."""
        with patch.dict(
            os.environ,
            {
                "AI_FLEET_ROLE": "WORKER",
                "GIT_AUTHOR_NAME": "z4-manager-3",  # Would parse as MANAGER
            },
            clear=True,
        ):
            assert get_role() == "WORKER"

    def test_user_role_default(self):
        """Returns USER for any other value."""
        with patch.dict(os.environ, {"GIT_AUTHOR_NAME": "John Doe"}, clear=True):
            assert get_role() == "USER"

    def test_user_role_when_unset(self):
        """Returns USER when env vars not set."""
        with patch.dict(os.environ, {}, clear=True):
            assert get_role() == "USER"


class TestGetIdentity:
    """Test get_identity function."""

    def test_returns_all_fields(self):
        """Returns all identity fields."""
        with patch.dict(
            os.environ,
            {
                "AI_FLEET_PROJECT": "z4",
                "AI_FLEET_ROLE": "WORKER",
                "AI_FLEET_ITERATION": "42",
                "AI_FLEET_SESSION": "abc123",
                "AI_FLEET_MACHINE": "mbp1",
                "GIT_AUTHOR_NAME": "z4-worker-42",
                "GIT_AUTHOR_EMAIL": "abc123@mbp1.z4.ai-fleet",
            },
        ):
            identity = get_identity()
            assert identity["project"] == "z4"
            assert identity["role"] == "WORKER"
            assert identity["iteration"] == 42
            assert identity["session"] == "abc123"
            assert identity["machine"] == "mbp1"
            assert identity["git_author"] == "z4-worker-42"
            assert identity["git_email"] == "abc123@mbp1.z4.ai-fleet"

    def test_falls_back_when_env_not_set(self):
        """Falls back to defaults when env vars not set."""
        with patch.dict(os.environ, {}, clear=True):
            identity = get_identity()
            assert identity["project"]  # Should have some value from git or cwd
            assert identity["role"] == "USER"
            assert identity["iteration"] == 0
            assert identity["session"] == ""
            assert identity["machine"]  # Should have hostname


class TestValidateIssue:
    """Test validate_issue function."""

    def test_valid_open_issue(self):
        """Validates open issue successfully."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (
                0,
                '{"number": 42, "title": "Test", "state": "OPEN", "labels": []}',
                "",
            )
            ok, data, err = validate_issue(42)
            assert ok is True
            assert data["number"] == 42
            assert err == ""

    def test_closed_issue_fails(self):
        """Closed issue fails validation."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (
                0,
                '{"number": 42, "state": "CLOSED", "labels": []}',
                "",
            )
            ok, data, err = validate_issue(42)
            assert ok is False
            assert "not open" in err

    def test_not_found_fails(self):
        """Non-existent issue fails validation."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (1, "", "Could not resolve")
            ok, data, err = validate_issue(999)
            assert ok is False
            assert "not found" in err


class TestHasLabel:
    """Test has_label function."""

    def test_finds_existing_label(self):
        """Finds label that exists."""
        data = {"labels": [{"name": "bug"}, {"name": "P1"}]}
        assert has_label(data, "bug") is True
        assert has_label(data, "P1") is True

    def test_missing_label(self):
        """Returns False for missing label."""
        data = {"labels": [{"name": "bug"}]}
        assert has_label(data, "enhancement") is False

    def test_empty_labels(self):
        """Handles empty labels list."""
        data = {"labels": []}
        assert has_label(data, "anything") is False


class TestGetClaimMetadata:
    """Test get_claim_metadata function."""

    def test_returns_required_fields(self):
        """Returns all required metadata fields."""
        with patch.object(
            ai_fleet_server, "get_project_name", return_value="test-project"
        ):
            meta = get_claim_metadata()

        assert "pid" in meta
        assert isinstance(meta["pid"], int)
        assert "machine" in meta
        assert "project" in meta
        assert meta["project"] == "test-project"
        assert "timestamp" in meta
        assert "session_id" in meta

    def test_timestamp_is_iso_format(self):
        """Timestamp is in ISO format."""
        meta = get_claim_metadata()
        # Should parse without error
        datetime.fromisoformat(meta["timestamp"].replace("Z", "+00:00"))


class TestParseClaimComment:
    """Test parse_claim_comment function."""

    def test_parses_full_comment_legacy(self):
        """Parses all fields from legacy claim comment."""
        comment = """**Claimed by WORKER**
- PID: 12345
- Machine: macbook.local
- Project: myproject
- Timestamp: 2026-01-08T10:00:00+00:00
- Session ID: abc12345
- Iteration: #42"""

        result = parse_claim_comment(comment)
        assert result["pid"] == 12345
        assert result["machine"] == "macbook.local"
        assert result["project"] == "myproject"
        assert "2026-01-08" in result["timestamp"]
        assert result["session_id"] == "abc12345"

    def test_parses_new_format_comment(self):
        """Parses all fields from new format claim comment with identity."""
        comment = """**Claimed by WORKER**
- PID: 12345
- Machine: mbp1
- Project: z4
- Timestamp: 2026-01-08T10:00:00+00:00
- Session ID: abc123
- Role: WORKER
- Iteration: #42
- Git Author: z4-worker-42"""

        result = parse_claim_comment(comment)
        assert result["pid"] == 12345
        assert result["machine"] == "mbp1"
        assert result["project"] == "z4"
        assert result["session_id"] == "abc123"
        assert result["role"] == "WORKER"
        assert result["iteration"] == 42
        assert result["git_author"] == "z4-worker-42"

    def test_handles_missing_fields(self):
        """Handles comments with missing fields."""
        comment = "PID: 999\nMachine: test"
        result = parse_claim_comment(comment)
        assert result["pid"] == 999
        assert result["machine"] == "test"
        assert "timestamp" not in result

    def test_empty_comment(self):
        """Handles empty comment."""
        result = parse_claim_comment("")
        assert result == {}


class TestParseReadmeMetadata:
    """Test parse_readme_metadata function."""

    def test_parses_table_format(self):
        """Parses metadata table from README."""
        content = """# Project Name

| Director | Status |
|:--------:|:------:|
| LANG | ACTIVE |

## Description
Some content here.
"""
        result = parse_readme_metadata(content)
        assert result.get("director") == "LANG"
        assert result.get("status") == "ACTIVE"

    def test_handles_missing_table(self):
        """Returns empty dict if no table found."""
        content = "# Project\n\nNo table here."
        result = parse_readme_metadata(content)
        assert result == {}

    def test_handles_list_values(self):
        """Handles comma-separated list values."""
        content = """# Test
| Directors | Tags |
|:-:|:-:|
| LANG, MATH | fast, stable |
"""
        result = parse_readme_metadata(content)
        assert result.get("directors") == ["LANG", "MATH"]
        assert result.get("tags") == ["fast", "stable"]


class TestConstants:
    """Test module constants."""

    def test_news_types(self):
        """NEWS_TYPE_MAP has required types."""
        assert "show" in NEWS_TYPE_MAP
        assert "ask" in NEWS_TYPE_MAP
        assert "bug" in NEWS_TYPE_MAP
        assert "rfc" in NEWS_TYPE_MAP

    def test_director_options(self):
        """DIRECTOR_OPTIONS has all directors."""
        expected = {"LANG", "MATH", "KNOW", "ML", "TOOL", "RS", "APP", "TPM", "VP"}
        assert set(DIRECTOR_OPTIONS.keys()) == expected


class TestCheckClaimStaleness:
    """Test check_claim_staleness function."""

    def test_no_claim_found(self):
        """Returns has_claim=False when no structured claim."""
        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (0, "[]", "")
            result = check_claim_staleness(42)
            assert result["has_claim"] is False

    def test_fresh_claim(self):
        """Fresh claim is not stale."""
        recent_time = datetime.now(timezone.utc).isoformat()
        comment_json = json.dumps(
            [
                {
                    "body": f"Claimed\n- PID: 12345\n- Timestamp: {recent_time}",
                }
            ]
        )

        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (0, comment_json, "")
            result = check_claim_staleness(42)
            assert result["has_claim"] is True
            assert result["is_stale"] is False

    def test_old_claim_is_stale(self):
        """Claim older than 90 minutes is stale."""
        old_time = "2020-01-01T00:00:00+00:00"
        comment_json = json.dumps(
            [
                {
                    "body": f"Claimed\n- PID: 12345\n- Timestamp: {old_time}",
                }
            ]
        )

        with patch.object(ai_fleet_server, "run_cmd") as mock:
            mock.return_value = (0, comment_json, "")
            result = check_claim_staleness(42)
            assert result["has_claim"] is True
            assert result["is_stale"] is True
            assert "minutes old" in result.get("reason", "")
