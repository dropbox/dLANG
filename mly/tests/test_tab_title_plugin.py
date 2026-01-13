"""
Tests for tab-title MCP plugin.

Tests core functions with mocked subprocess calls.
"""

import importlib.util
import os
import subprocess
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch


# Load module from specific path to avoid conflicts
def load_module_from_path(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


# Load tab-title server
tab_title_server = load_module_from_path(
    "tab_title_server",
    Path(__file__).parent.parent / ".claude/plugins/tab-title/server.py",
)

# Import from loaded module
get_project_name = tab_title_server.get_project_name
get_role = tab_title_server.get_role
auto_set_title = tab_title_server.auto_set_title
set_title = tab_title_server.set_title
set_title_applescript = tab_title_server.set_title_applescript
set_title_escape = tab_title_server.set_title_escape
handle_request = tab_title_server.handle_request


class TestGetProjectName:
    """Test get_project_name function."""

    def test_extracts_from_git_remote(self):
        """Extracts project name from git remote URL."""
        with patch("subprocess.run") as mock:
            mock.return_value = MagicMock(
                returncode=0,
                stdout="git@github.com:user/my-project.git\n",
                stderr="",
            )
            assert get_project_name() == "my-project"

    def test_handles_https_url(self):
        """Handles HTTPS remote URLs."""
        with patch("subprocess.run") as mock:
            mock.return_value = MagicMock(
                returncode=0,
                stdout="https://github.com/user/test-repo.git\n",
                stderr="",
            )
            assert get_project_name() == "test-repo"

    def test_strips_trailing_slash(self):
        """Strips trailing slash from URL."""
        with patch("subprocess.run") as mock:
            mock.return_value = MagicMock(
                returncode=0,
                stdout="https://github.com/user/repo/\n",
                stderr="",
            )
            assert get_project_name() == "repo"


class TestGetRole:
    """Test get_role function."""

    def test_worker_role(self):
        """Returns W for WORKER."""
        with patch.dict(os.environ, {"AI_FLEET_ROLE": "WORKER"}):
            assert get_role() == "W"

    def test_worker_role_lowercase(self):
        """Handles lowercase worker (case insensitive)."""
        with patch.dict(os.environ, {"AI_FLEET_ROLE": "worker"}):
            assert get_role() == "W"

    def test_manager_role(self):
        """Returns M for MANAGER."""
        with patch.dict(os.environ, {"AI_FLEET_ROLE": "MANAGER"}):
            assert get_role() == "M"

    def test_user_role_default(self):
        """Returns U for any other value."""
        with patch.dict(os.environ, {"AI_FLEET_ROLE": "UNKNOWN"}, clear=False):
            assert get_role() == "U"

    def test_user_role_when_unset(self):
        """Returns U when env var not set."""
        env = os.environ.copy()
        env.pop("AI_FLEET_ROLE", None)
        with patch.dict(os.environ, env, clear=True):
            assert get_role() == "U"


class TestSetTitleEscape:
    """Test set_title_escape function."""

    def test_returns_false_without_tty(self):
        """Returns False when no TTY available."""
        with patch("builtins.open", side_effect=OSError("No TTY")):
            result = set_title_escape("test")
            assert result is False

    def test_writes_escape_sequences(self):
        """Writes escape sequences to TTY."""
        mock_tty = MagicMock()
        with patch("builtins.open", return_value=mock_tty):
            mock_tty.__enter__ = MagicMock(return_value=mock_tty)
            mock_tty.__exit__ = MagicMock(return_value=False)

            set_title_escape("Test Title")
            # Should write OSC escape sequences
            calls = mock_tty.write.call_args_list
            assert len(calls) >= 1


class TestSetTitleApplescript:
    """Test set_title_applescript function."""

    def test_escapes_quotes(self):
        """Properly escapes quotes in title."""
        with patch("subprocess.run") as mock:
            mock.return_value = MagicMock(returncode=0)
            set_title_applescript('Test "quoted" title')
            # Check the script was called
            assert mock.called

    def test_returns_true_on_success(self):
        """Returns True when AppleScript succeeds."""
        with patch("subprocess.run") as mock:
            mock.return_value = MagicMock(returncode=0)
            assert set_title_applescript("Test") is True

    def test_returns_false_on_failure(self):
        """Returns False when AppleScript fails."""
        with patch("subprocess.run") as mock:
            mock.return_value = MagicMock(returncode=1)
            assert set_title_applescript("Test") is False

    def test_handles_timeout(self):
        """Handles subprocess timeout."""
        with patch("subprocess.run", side_effect=subprocess.TimeoutExpired("cmd", 10)):
            assert set_title_applescript("Test") is False


class TestSetTitle:
    """Test set_title function."""

    def test_tries_multiple_methods(self):
        """Tries both AppleScript and escape sequences."""
        with patch.object(
            tab_title_server, "set_title_applescript", return_value=True
        ) as mock_apple:
            with patch.object(
                tab_title_server, "set_title_escape", return_value=True
            ) as mock_escape:
                result = set_title("Test")

                assert mock_apple.called
                assert mock_escape.called
                assert result["applescript"] is True
                assert result["escape_seq"] is True

    def test_returns_title_in_result(self):
        """Includes title in result dict."""
        with patch.object(
            tab_title_server, "set_title_applescript", return_value=False
        ):
            with patch.object(tab_title_server, "set_title_escape", return_value=False):
                result = set_title("My Title")
                assert result["title"] == "My Title"


class TestAutoSetTitle:
    """Test auto_set_title function."""

    def test_generates_formatted_title(self):
        """Generates [ROLE]project title format."""
        with patch.object(tab_title_server, "get_role", return_value="W"):
            with patch.object(
                tab_title_server, "get_project_name", return_value="myproject"
            ):
                with patch.object(tab_title_server, "set_title") as mock_set:
                    auto_set_title()
                    mock_set.assert_called_once_with("[W]myproject")

    def test_uses_current_role(self):
        """Uses role from environment."""
        with patch.object(tab_title_server, "get_role", return_value="M"):
            with patch.object(
                tab_title_server, "get_project_name", return_value="test"
            ):
                with patch.object(tab_title_server, "set_title") as mock_set:
                    auto_set_title()
                    mock_set.assert_called_once_with("[M]test")


class TestMCPProtocol:
    """Test MCP protocol handling."""

    def test_initialize_response(self):
        """Returns proper initialize response."""
        request = {"method": "initialize", "id": 1}
        response = handle_request(request)

        assert response["jsonrpc"] == "2.0"
        assert response["id"] == 1
        assert "result" in response
        assert "protocolVersion" in response["result"]

    def test_tools_list(self):
        """Returns tool list with set_tab_title."""
        request = {"method": "tools/list", "id": 2}
        response = handle_request(request)

        tools = response["result"]["tools"]
        tool_names = [t["name"] for t in tools]
        assert "set_tab_title" in tool_names

    def test_notifications_initialized(self):
        """Handles notifications/initialized."""
        with patch.object(tab_title_server, "auto_set_title") as mock:
            request = {"method": "notifications/initialized"}
            response = handle_request(request)

            # Should call auto_set_title and return None
            mock.assert_called_once()
            assert response is None

    def test_tool_call_set_title(self):
        """Handles set_tab_title tool call."""
        with patch.object(
            tab_title_server,
            "set_title",
            return_value={
                "title": "test",
                "applescript": True,
                "escape_seq": True,
                "session_id": "x",
            },
        ):
            request = {
                "method": "tools/call",
                "id": 3,
                "params": {
                    "name": "set_tab_title",
                    "arguments": {"title": "Custom Title"},
                },
            }
            response = handle_request(request)

            assert response["id"] == 3
            assert "result" in response
            content = response["result"]["content"][0]["text"]
            assert "Custom Title" in content

    def test_tool_call_auto_title(self):
        """Generates title when not provided."""
        with patch.object(tab_title_server, "get_role", return_value="U"):
            with patch.object(
                tab_title_server, "get_project_name", return_value="proj"
            ):
                with patch.object(
                    tab_title_server,
                    "set_title",
                    return_value={
                        "title": "[U]proj",
                        "applescript": True,
                        "escape_seq": True,
                        "session_id": "x",
                    },
                ):
                    request = {
                        "method": "tools/call",
                        "id": 4,
                        "params": {
                            "name": "set_tab_title",
                            "arguments": {},
                        },
                    }
                    response = handle_request(request)
                    content = response["result"]["content"][0]["text"]
                    assert "[U]proj" in content

    def test_unknown_tool_error(self):
        """Returns error for unknown tool."""
        request = {
            "method": "tools/call",
            "id": 5,
            "params": {"name": "unknown_tool", "arguments": {}},
        }
        response = handle_request(request)

        assert "error" in response
        assert response["error"]["code"] == -32601
