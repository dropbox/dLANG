"""
Tests for json_to_text.py

Tests the formatting and parsing functions without requiring actual CLI streams.
"""

import io
import os
import subprocess
import sys
from contextlib import redirect_stdout
from pathlib import Path

# Add parent dir to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "ai_template_scripts"))

# Disable colors for consistent test output
os.environ["FORCE_COLOR"] = "0"

from json_to_text import (
    CLAUDE_MSG_HANDLERS,
    CODEX_EVENT_HANDLERS,
    CODEX_ITEM_HANDLERS,
    ERROR_PATTERNS,
    TOOL_DESC_FORMATTERS,
    CodexFormatter,
    MessageFormatter,
    _build_tool_description,
    _desc_bash,
    _desc_edit,
    _desc_glob,
    _desc_grep,
    _desc_lsp,
    _desc_read,
    _desc_task,
    _desc_todo_write,
    _desc_web_fetch,
    _desc_web_search,
    _desc_write,
    _extract_result_text,
    _extract_role_and_content,
    _handle_error,
    _handle_init,
    _handle_item_event,
    _handle_result,
    _handle_text_block,
    _handle_thinking_block,
    _handle_thread_started,
    _handle_tool_result_block,
    _handle_turn_completed,
    _handle_turn_failed,
    _handle_turn_started,
    _is_error_result,
    _print_claude_stats,
    _print_usage_stats,
    _process_content_block,
    _store_tool_use,
    _truncate,
    clean_output,
    codex_formatter,
    format_tool_output,
    is_codex_event,
    pending_tool_uses,
    process_codex_event,
    process_message,
)


class TestCleanOutput:
    """Test clean_output function."""

    def test_removes_co_authored_by(self):
        """Co-Authored-By lines are removed."""
        text = (
            "Some content\nCo-Authored-By: Claude <noreply@anthropic.com>\nMore content"
        )
        result = clean_output(text)
        assert "Co-Authored-By" not in result
        assert "Some content" in result
        assert "More content" in result

    def test_removes_generated_with(self):
        """Generated with lines are removed."""
        text = "Content here\n🤖 Generated with Claude Code\nMore"
        result = clean_output(text)
        assert "Generated with" not in result

    def test_removes_system_reminders(self):
        """System reminder blocks are removed."""
        text = """Before
<system-reminder>
This should be hidden
</system-reminder>
After"""
        result = clean_output(text)
        assert "should be hidden" not in result
        assert "Before" in result
        assert "After" in result

    def test_removes_malware_warnings(self):
        """Malware check reminder lines are removed."""
        text = "Code here\nyou should consider whether it would be considered malware\nMore code"
        result = clean_output(text)
        assert "malware" not in result.lower()

    def test_handles_none(self):
        """None input returns empty string."""
        assert clean_output(None) == ""

    def test_preserves_normal_content(self):
        """Normal content is preserved."""
        text = "Normal line 1\nNormal line 2"
        result = clean_output(text)
        assert result == text


class TestFormatToolOutput:
    """Test format_tool_output function."""

    def test_empty_returns_none(self):
        """Empty content returns None."""
        assert format_tool_output("", "Bash") is None
        assert format_tool_output("   \n  ", "Bash") is None

    def test_bash_short_output(self):
        """Bash with short output shows all lines."""
        result = format_tool_output("line1\nline2", "Bash")
        assert len(result) == 2

    def test_bash_long_output_truncated(self):
        """Bash with long output is truncated."""
        lines = "\n".join([f"line{i}" for i in range(10)])
        result = format_tool_output(lines, "Bash")
        assert len(result) == 4  # first 2 + ellipsis + last
        assert "more lines" in result[2]

    def test_read_shows_line_count(self):
        """Read tool shows line count only."""
        lines = "\n".join([f"line{i}" for i in range(100)])
        result = format_tool_output(lines, "Read")
        assert len(result) == 1
        assert "100 lines" in result[0]

    def test_write_returns_none(self):
        """Write tool returns None (success confirmed elsewhere)."""
        assert format_tool_output("success", "Write") is None

    def test_edit_returns_none(self):
        """Edit tool returns None (success confirmed elsewhere)."""
        assert format_tool_output("edited", "Edit") is None

    def test_grep_short_output(self):
        """Grep with few matches shows all."""
        result = format_tool_output("match1\nmatch2\nmatch3", "Grep")
        assert len(result) == 3

    def test_grep_long_output_truncated(self):
        """Grep with many matches is truncated."""
        lines = "\n".join([f"match{i}" for i in range(20)])
        result = format_tool_output(lines, "Grep")
        assert len(result) == 6  # 5 + ellipsis
        assert "more matches" in result[-1]

    def test_error_shows_more_context(self):
        """Errors show more lines."""
        lines = "\n".join([f"error line {i}" for i in range(20)])
        result = format_tool_output(lines, "Bash", is_error=True)
        assert len(result) == 16  # 15 + ellipsis
        assert "more lines" in result[-1]


class TestIsCodexEvent:
    """Test Codex event detection."""

    def test_codex_dotted_type(self):
        """Dotted type names are Codex events."""
        assert is_codex_event({"type": "thread.started"}) is True
        assert is_codex_event({"type": "item.completed"}) is True
        assert is_codex_event({"type": "turn.failed"}) is True

    def test_claude_simple_type(self):
        """Simple type names are Claude events."""
        assert is_codex_event({"type": "init"}) is False
        assert is_codex_event({"type": "result"}) is False

    def test_message_field_is_claude(self):
        """Events with message field are Claude."""
        assert is_codex_event({"type": "message", "message": {}}) is False


class TestMessageFormatter:
    """Test MessageFormatter class."""

    def test_format_text_strips_whitespace(self, capsys):
        """Text messages have whitespace stripped."""
        formatter = MessageFormatter()
        formatter.format_text_message("  Hello world  ")
        captured = capsys.readouterr()
        assert "Hello world" in captured.out

    def test_format_text_empty_ignored(self, capsys):
        """Empty text messages produce no output."""
        formatter = MessageFormatter()
        formatter.format_text_message("   ")
        captured = capsys.readouterr()
        assert captured.out == ""

    def test_format_tool_use_bash(self, capsys):
        """Bash tool use is formatted with command."""
        formatter = MessageFormatter()
        formatter.format_tool_use("Bash", {"command": "ls -la"}, "output")
        captured = capsys.readouterr()
        assert "bash:" in captured.out
        assert "ls -la" in captured.out

    def test_format_tool_use_read(self, capsys):
        """Read tool use is formatted with file path."""
        formatter = MessageFormatter()
        formatter.format_tool_use("Read", {"file_path": "/path/to/file.py"}, "content")
        captured = capsys.readouterr()
        assert "read:" in captured.out
        assert "/path/to/file.py" in captured.out

    def test_format_tool_use_grep(self, capsys):
        """Grep tool use is formatted with pattern."""
        formatter = MessageFormatter()
        formatter.format_tool_use(
            "Grep", {"pattern": "TODO", "path": "src/"}, "matches"
        )
        captured = capsys.readouterr()
        assert "grep:" in captured.out
        assert "TODO" in captured.out

    def test_format_tool_use_long_command_truncated(self, capsys):
        """Long commands are truncated."""
        formatter = MessageFormatter()
        long_cmd = "x" * 100
        formatter.format_tool_use("Bash", {"command": long_cmd}, "output")
        captured = capsys.readouterr()
        assert "..." in captured.out
        assert len(captured.out.split("bash:")[1].split("\n")[0]) < 100

    def test_format_tool_use_error_detection(self, capsys):
        """Errors are detected and highlighted."""
        formatter = MessageFormatter()
        formatter.format_tool_use(
            "Bash", {"command": "test"}, "Error: something failed"
        )
        captured = capsys.readouterr()
        # Error marker should appear
        assert "✗" in captured.out

    def test_format_thinking_short_ignored(self, capsys):
        """Short thinking blocks are ignored."""
        formatter = MessageFormatter()
        formatter.format_thinking("brief thought")
        captured = capsys.readouterr()
        assert captured.out == ""

    def test_format_thinking_long_shown(self, capsys):
        """Long thinking blocks show char count."""
        formatter = MessageFormatter()
        formatter.format_thinking("x" * 200)
        captured = capsys.readouterr()
        assert "thinking" in captured.out
        assert "200" in captured.out


class TestCodexFormatter:
    """Test CodexFormatter class."""

    def test_format_agent_message(self, capsys):
        """Agent messages are formatted."""
        formatter = CodexFormatter()
        formatter.format_agent_message({"text": "Hello from Codex"})
        captured = capsys.readouterr()
        assert "Hello from Codex" in captured.out

    def test_format_agent_message_empty_ignored(self, capsys):
        """Empty agent messages produce no output."""
        formatter = CodexFormatter()
        formatter.format_agent_message({"text": ""})
        captured = capsys.readouterr()
        assert captured.out == ""

    def test_format_command_success(self, capsys):
        """Successful commands are formatted."""
        formatter = CodexFormatter()
        formatter.format_command_execution(
            {
                "command": "echo hello",
                "exit_code": 0,
                "aggregated_output": "hello",
            }
        )
        captured = capsys.readouterr()
        assert "bash:" in captured.out
        assert "echo hello" in captured.out

    def test_format_command_failure(self, capsys):
        """Failed commands show error indicator."""
        formatter = CodexFormatter()
        formatter.format_command_execution(
            {
                "command": "false",
                "exit_code": 1,
                "aggregated_output": "error output",
            }
        )
        captured = capsys.readouterr()
        assert "✗" in captured.out
        assert "exit 1" in captured.out

    def test_format_file_change_create(self, capsys):
        """File creation is formatted."""
        formatter = CodexFormatter()
        formatter.format_file_change(
            {
                "file_path": "/path/to/new.py",
                "change_type": "create",
            }
        )
        captured = capsys.readouterr()
        assert "write:" in captured.out

    def test_format_file_change_edit(self, capsys):
        """File edit is formatted."""
        formatter = CodexFormatter()
        formatter.format_file_change(
            {
                "file_path": "/path/to/file.py",
                "change_type": "modify",
            }
        )
        captured = capsys.readouterr()
        assert "edit:" in captured.out

    def test_format_reasoning_short_ignored(self, capsys):
        """Short reasoning is ignored."""
        formatter = CodexFormatter()
        formatter.format_reasoning({"text": "brief"})
        captured = capsys.readouterr()
        assert captured.out == ""

    def test_format_reasoning_long_shown(self, capsys):
        """Long reasoning shows indicator."""
        formatter = CodexFormatter()
        formatter.format_reasoning({"text": "x" * 100})
        captured = capsys.readouterr()
        assert "thinking" in captured.out


class TestErrorPatternDetection:
    """Test error pattern detection in tool results."""

    def test_detects_error_prefix(self):
        """Detects 'Error:' prefix."""
        formatter = MessageFormatter()
        # We can test by checking the formatting differs
        f = io.StringIO()
        with redirect_stdout(f):
            formatter.format_tool_use("Bash", {"command": "test"}, "Error: failed")
        assert "✗" in f.getvalue()

    def test_detects_traceback(self):
        """Detects Python traceback."""
        formatter = MessageFormatter()
        f = io.StringIO()
        with redirect_stdout(f):
            formatter.format_tool_use(
                "Bash", {"command": "python"}, "Traceback (most recent call last):"
            )
        assert "✗" in f.getvalue()

    def test_detects_permission_denied(self):
        """Detects permission denied."""
        formatter = MessageFormatter()
        f = io.StringIO()
        with redirect_stdout(f):
            formatter.format_tool_use("Bash", {"command": "test"}, "Permission denied")
        assert "✗" in f.getvalue()

    def test_no_false_positive_on_normal_output(self):
        """Normal output is not flagged as error."""
        formatter = MessageFormatter()
        f = io.StringIO()
        with redirect_stdout(f):
            formatter.format_tool_use("Bash", {"command": "echo"}, "Hello world")
        # Should use bullet point, not X
        assert "•" in f.getvalue()


class TestTruncate:
    """Test _truncate helper."""

    def test_short_text_unchanged(self):
        """Text shorter than max is unchanged."""
        assert _truncate("hello", 10) == "hello"

    def test_exact_length_unchanged(self):
        """Text at exact max is unchanged."""
        assert _truncate("hello", 5) == "hello"

    def test_long_text_truncated(self):
        """Text longer than max is truncated with ellipsis."""
        result = _truncate("hello world", 8)
        assert result == "hello..."
        assert len(result) == 8

    def test_very_short_max(self):
        """Very short max still works."""
        result = _truncate("hello", 4)
        assert result == "h..."


class TestIsErrorResult:
    """Test _is_error_result helper."""

    def test_none_returns_false(self):
        """None input returns False."""
        assert _is_error_result(None) is False

    def test_empty_returns_false(self):
        """Empty string returns False."""
        assert _is_error_result("") is False

    def test_detects_error_prefix(self):
        """Detects Error: prefix."""
        assert _is_error_result("Error: something failed") is True

    def test_detects_traceback(self):
        """Detects Python traceback."""
        assert _is_error_result("Traceback (most recent call last):") is True

    def test_detects_permission_denied(self):
        """Detects permission denied."""
        assert _is_error_result("permission denied: /etc/passwd") is True

    def test_detects_not_found(self):
        """Detects not found."""
        assert _is_error_result("file not found") is True

    def test_detects_json_error_flag(self):
        """Detects JSON error flag."""
        assert _is_error_result('{"is_error": true}') is True
        assert _is_error_result('{"is_error":true}') is True

    def test_normal_output_not_error(self):
        """Normal output is not flagged as error."""
        assert _is_error_result("Hello world") is False
        assert _is_error_result("Success!") is False

    def test_case_insensitive(self):
        """Error detection is case insensitive."""
        assert _is_error_result("ERROR: failed") is True
        assert _is_error_result("TRACEBACK") is True


class TestToolDescFormatters:
    """Test individual tool description formatters."""

    def test_desc_read(self):
        """Read tool description."""
        result = _desc_read({"file_path": "/path/to/file.py"})
        assert result == "read: /path/to/file.py"

    def test_desc_read_empty(self):
        """Read with missing path."""
        result = _desc_read({})
        assert result == "read: "

    def test_desc_write(self):
        """Write tool description includes size."""
        result = _desc_write({"file_path": "/path/file.py", "content": "hello"})
        assert result == "write: /path/file.py (5 chars)"

    def test_desc_write_empty_content(self):
        """Write with no content shows 0 chars."""
        result = _desc_write({"file_path": "/path/file.py"})
        assert "(0 chars)" in result

    def test_desc_edit(self):
        """Edit tool description."""
        result = _desc_edit({"file_path": "/path/to/file.py"})
        assert result == "edit: /path/to/file.py"

    def test_desc_bash_short(self):
        """Bash with short command."""
        result = _desc_bash({"command": "ls -la"})
        assert result == "bash: ls -la"

    def test_desc_bash_long_truncated(self):
        """Bash with long command is truncated."""
        long_cmd = "x" * 100
        result = _desc_bash({"command": long_cmd})
        assert len(result) < 90
        assert "..." in result

    def test_desc_grep(self):
        """Grep tool description."""
        result = _desc_grep({"pattern": "TODO", "path": "src/"})
        assert result == "grep: 'TODO' in src/"

    def test_desc_grep_default_path(self):
        """Grep with no path uses default."""
        result = _desc_grep({"pattern": "TODO"})
        assert result == "grep: 'TODO' in ."

    def test_desc_glob(self):
        """Glob tool description."""
        result = _desc_glob({"pattern": "**/*.py"})
        assert result == "glob: **/*.py"

    def test_desc_todo_write(self):
        """TodoWrite tool description."""
        result = _desc_todo_write({"todos": [1, 2, 3]})
        assert result == "todo: update (3 items)"

    def test_desc_todo_write_empty(self):
        """TodoWrite with no todos."""
        result = _desc_todo_write({})
        assert result == "todo: update (0 items)"

    def test_desc_task_with_description(self):
        """Task with description."""
        result = _desc_task({"subagent_type": "Explore", "description": "find files"})
        assert result == "task: Explore → find files"

    def test_desc_task_without_description(self):
        """Task without description."""
        result = _desc_task({"subagent_type": "Bash"})
        assert result == "task: spawn Bash"

    def test_desc_task_default_agent(self):
        """Task with no subagent type."""
        result = _desc_task({})
        assert result == "task: spawn agent"

    def test_desc_web_fetch(self):
        """WebFetch tool description."""
        result = _desc_web_fetch({"url": "https://example.com"})
        assert result == "fetch: https://example.com"

    def test_desc_web_fetch_long_url(self):
        """WebFetch with long URL is truncated."""
        long_url = "https://example.com/" + "x" * 100
        result = _desc_web_fetch({"url": long_url})
        assert len(result) < 70
        assert "..." in result

    def test_desc_web_search(self):
        """WebSearch tool description."""
        result = _desc_web_search({"query": "python tutorial"})
        assert result == "search: python tutorial"

    def test_desc_web_search_long_query(self):
        """WebSearch with long query is truncated."""
        long_query = "x" * 100
        result = _desc_web_search({"query": long_query})
        assert "..." in result

    def test_desc_lsp(self):
        """LSP tool description."""
        result = _desc_lsp({"operation": "definition", "filePath": "/path/file.py"})
        assert result == "lsp: definition in /path/file.py"


class TestBuildToolDescription:
    """Test _build_tool_description dispatcher."""

    def test_known_tool(self):
        """Known tool uses its formatter."""
        result = _build_tool_description("Bash", {"command": "echo hi"})
        assert result == "bash: echo hi"

    def test_unknown_tool(self):
        """Unknown tool returns lowercase name."""
        result = _build_tool_description("MyCustomTool", {})
        assert result == "mycustomtool"

    def test_all_formatters_registered(self):
        """All expected formatters are registered."""
        expected = {
            "Read",
            "Write",
            "Edit",
            "Bash",
            "Grep",
            "Glob",
            "TodoWrite",
            "Task",
            "WebFetch",
            "WebSearch",
            "LSP",
        }
        assert set(TOOL_DESC_FORMATTERS.keys()) == expected


class TestErrorPatterns:
    """Test ERROR_PATTERNS constant."""

    def test_patterns_are_lowercase(self):
        """All patterns should be lowercase for comparison."""
        for pattern in ERROR_PATTERNS:
            assert pattern == pattern.lower(), f"Pattern '{pattern}' is not lowercase"

    def test_expected_patterns_present(self):
        """Key error patterns are present."""
        patterns_str = " ".join(ERROR_PATTERNS)
        assert "error:" in patterns_str
        assert "traceback" in patterns_str
        assert "permission denied" in patterns_str
        assert "not found" in patterns_str


# ============================================================================
# Tests for newly extracted Codex event handlers
# ============================================================================


class TestHandleThreadStarted:
    """Test _handle_thread_started helper."""

    def test_prints_session_header(self, capsys):
        """Prints Codex session started header."""
        _handle_thread_started({})
        captured = capsys.readouterr()
        assert "Codex Session Started" in captured.out

    def test_prints_thread_id_if_present(self, capsys):
        """Prints thread ID when provided."""
        _handle_thread_started({"thread_id": "abc123"})
        captured = capsys.readouterr()
        assert "abc123" in captured.out

    def test_sets_formatter_in_session(self):
        """Sets codex_formatter.in_session to True."""
        codex_formatter.in_session = False
        _handle_thread_started({})
        assert codex_formatter.in_session is True


class TestHandleTurnStarted:
    """Test _handle_turn_started helper."""

    def test_is_noop(self, capsys):
        """turn.started is a no-op, produces no output."""
        _handle_turn_started({})
        captured = capsys.readouterr()
        assert captured.out == ""


class TestPrintUsageStats:
    """Test _print_usage_stats helper."""

    def test_prints_token_counts(self, capsys):
        """Prints input and output token counts."""
        _print_usage_stats({"input_tokens": 100, "output_tokens": 50})
        captured = capsys.readouterr()
        assert "100" in captured.out
        assert "50" in captured.out

    def test_prints_cached_tokens_if_present(self, capsys):
        """Prints cached token count when provided."""
        _print_usage_stats(
            {
                "input_tokens": 100,
                "output_tokens": 50,
                "cached_input_tokens": 30,
            }
        )
        captured = capsys.readouterr()
        assert "cached: 30" in captured.out

    def test_no_cached_if_zero(self, capsys):
        """Does not print cached if zero."""
        _print_usage_stats({"input_tokens": 100, "output_tokens": 50})
        captured = capsys.readouterr()
        assert "cached" not in captured.out


class TestHandleTurnCompleted:
    """Test _handle_turn_completed helper."""

    def test_prints_turn_complete(self, capsys):
        """Prints turn complete message."""
        _handle_turn_completed({})
        captured = capsys.readouterr()
        assert "Turn Complete" in captured.out

    def test_sets_formatter_not_in_session(self):
        """Sets codex_formatter.in_session to False."""
        codex_formatter.in_session = True
        _handle_turn_completed({})
        assert codex_formatter.in_session is False

    def test_prints_usage_if_present(self, capsys):
        """Prints usage stats when provided."""
        _handle_turn_completed({"usage": {"input_tokens": 500, "output_tokens": 100}})
        captured = capsys.readouterr()
        assert "500" in captured.out
        assert "100" in captured.out


class TestHandleTurnFailed:
    """Test _handle_turn_failed helper."""

    def test_prints_failure_message(self, capsys):
        """Prints turn failed with error message."""
        _handle_turn_failed({"error": {"message": "API timeout"}})
        captured = capsys.readouterr()
        assert "Turn Failed" in captured.out
        assert "API timeout" in captured.out

    def test_handles_string_error(self, capsys):
        """Handles error as string."""
        _handle_turn_failed({"error": "simple error"})
        captured = capsys.readouterr()
        assert "simple error" in captured.out

    def test_handles_missing_message(self, capsys):
        """Handles missing error message."""
        _handle_turn_failed({"error": {}})
        captured = capsys.readouterr()
        assert "Unknown error" in captured.out


class TestHandleError:
    """Test _handle_error helper."""

    def test_delegates_to_formatter(self, capsys):
        """Delegates to codex_formatter.format_error."""
        _handle_error({"error": {"message": "test error"}})
        captured = capsys.readouterr()
        assert "Error" in captured.out
        assert "test error" in captured.out


class TestHandleItemEvent:
    """Test _handle_item_event helper."""

    def test_item_completed_agent_message(self, capsys):
        """item.completed with agent_message is formatted."""
        _handle_item_event(
            {"item": {"type": "agent_message", "text": "Hello"}},
            "item.completed",
        )
        captured = capsys.readouterr()
        assert "Hello" in captured.out

    def test_item_started_agent_message_shown(self, capsys):
        """item.started with agent_message is shown for streaming."""
        _handle_item_event(
            {"item": {"type": "agent_message", "text": "Streaming"}},
            "item.started",
        )
        captured = capsys.readouterr()
        assert "Streaming" in captured.out

    def test_item_started_non_agent_ignored(self, capsys):
        """item.started with non-agent_message is ignored."""
        _handle_item_event(
            {"item": {"type": "command_execution", "command": "ls"}},
            "item.started",
        )
        captured = capsys.readouterr()
        assert captured.out == ""

    def test_item_completed_command_execution(self, capsys):
        """item.completed with command_execution is formatted."""
        _handle_item_event(
            {
                "item": {
                    "type": "command_execution",
                    "command": "ls -la",
                    "exit_code": 0,
                }
            },
            "item.completed",
        )
        captured = capsys.readouterr()
        assert "bash:" in captured.out
        assert "ls -la" in captured.out

    def test_item_completed_file_change(self, capsys):
        """item.completed with file_change is formatted."""
        _handle_item_event(
            {
                "item": {
                    "type": "file_change",
                    "file_path": "/test.py",
                    "change_type": "create",
                }
            },
            "item.completed",
        )
        captured = capsys.readouterr()
        assert "write:" in captured.out

    def test_unknown_item_type_ignored(self, capsys):
        """Unknown item type produces no output."""
        _handle_item_event(
            {"item": {"type": "unknown_type"}},
            "item.completed",
        )
        captured = capsys.readouterr()
        assert captured.out == ""


class TestCodexEventHandlers:
    """Test CODEX_EVENT_HANDLERS dispatch table."""

    def test_all_handlers_registered(self):
        """Expected handlers are registered."""
        expected = {
            "thread.started",
            "turn.started",
            "turn.completed",
            "turn.failed",
            "error",
        }
        assert set(CODEX_EVENT_HANDLERS.keys()) == expected

    def test_all_handlers_callable(self):
        """All handlers are callable."""
        for name, handler in CODEX_EVENT_HANDLERS.items():
            assert callable(handler), f"Handler for {name} is not callable"


class TestCodexItemHandlers:
    """Test CODEX_ITEM_HANDLERS dispatch table."""

    def test_all_handlers_registered(self):
        """Expected item handlers are registered."""
        expected = {
            "agent_message",
            "command_execution",
            "file_change",
            "reasoning",
            "mcp_tool_call",
            "web_search",
            "todo_list",
        }
        assert set(CODEX_ITEM_HANDLERS.keys()) == expected

    def test_all_handlers_callable(self):
        """All item handlers are callable."""
        for name, handler in CODEX_ITEM_HANDLERS.items():
            assert callable(handler), f"Handler for {name} is not callable"


class TestProcessCodexEvent:
    """Test process_codex_event integration."""

    def test_thread_started_event(self, capsys):
        """thread.started event is processed."""
        process_codex_event({"type": "thread.started", "thread_id": "test123"})
        captured = capsys.readouterr()
        assert "Codex Session Started" in captured.out

    def test_turn_completed_event(self, capsys):
        """turn.completed event is processed."""
        process_codex_event({"type": "turn.completed"})
        captured = capsys.readouterr()
        assert "Turn Complete" in captured.out

    def test_item_completed_event(self, capsys):
        """item.completed event is processed."""
        process_codex_event(
            {
                "type": "item.completed",
                "item": {"type": "agent_message", "text": "Test message"},
            }
        )
        captured = capsys.readouterr()
        assert "Test message" in captured.out

    def test_unknown_event_ignored(self, capsys):
        """Unknown event type produces no output."""
        process_codex_event({"type": "unknown.event"})
        captured = capsys.readouterr()
        assert captured.out == ""


# ============================================================================
# Tests for newly extracted Claude message handlers
# ============================================================================


class TestExtractRoleAndContent:
    """Test _extract_role_and_content helper."""

    def test_nested_message_dict(self):
        """Extracts from nested message dict."""
        msg = {
            "message": {
                "role": "assistant",
                "content": [{"type": "text", "text": "hi"}],
            }
        }
        role, content = _extract_role_and_content(msg)
        assert role == "assistant"
        assert content == [{"type": "text", "text": "hi"}]

    def test_nested_message_string(self):
        """Handles nested message as string."""
        msg = {"message": "Hello world"}
        role, content = _extract_role_and_content(msg)
        assert role == "assistant"
        assert content == [{"type": "text", "text": "Hello world"}]

    def test_flat_message(self):
        """Extracts from flat message."""
        msg = {"role": "user", "content": "test"}
        role, content = _extract_role_and_content(msg)
        assert role == "user"
        assert content == "test"

    def test_missing_role(self):
        """Returns None for missing role."""
        msg = {"content": []}
        role, content = _extract_role_and_content(msg)
        assert role is None


class TestHandleInit:
    """Test _handle_init helper."""

    def test_prints_session_header(self, capsys):
        """Prints Claude session started header."""
        _handle_init({})
        captured = capsys.readouterr()
        assert "Claude Session Started" in captured.out

    def test_clears_pending_tools(self):
        """Clears pending_tool_uses."""
        pending_tool_uses.clear()  # Use .clear() on the actual dict
        pending_tool_uses["test"] = {"name": "test"}
        _handle_init({})
        assert len(pending_tool_uses) == 0


class TestPrintClaudeStats:
    """Test _print_claude_stats helper."""

    def test_prints_token_counts(self, capsys):
        """Prints input and output token counts."""
        _print_claude_stats({"input_tokens": 200, "output_tokens": 80})
        captured = capsys.readouterr()
        assert "200" in captured.out
        assert "80" in captured.out

    def test_prints_cached_tokens_if_present(self, capsys):
        """Prints cached token count when provided."""
        _print_claude_stats(
            {
                "input_tokens": 200,
                "output_tokens": 80,
                "cache_read_input_tokens": 50,
            }
        )
        captured = capsys.readouterr()
        assert "cached: 50" in captured.out


class TestHandleResult:
    """Test _handle_result helper."""

    def test_prints_session_complete(self, capsys):
        """Prints session complete message."""
        _handle_result({})
        captured = capsys.readouterr()
        assert "Session Complete" in captured.out

    def test_prints_stats_if_present(self, capsys):
        """Prints stats when provided."""
        _handle_result({"stats": {"input_tokens": 1000, "output_tokens": 500}})
        captured = capsys.readouterr()
        assert "1,000" in captured.out
        assert "500" in captured.out


class TestHandleTextBlock:
    """Test _handle_text_block helper."""

    def test_assistant_text_formatted(self, capsys):
        """Assistant text is formatted."""
        _handle_text_block({"text": "Hello"}, "assistant")
        captured = capsys.readouterr()
        assert "Hello" in captured.out

    def test_user_text_ignored(self, capsys):
        """User text is not formatted."""
        _handle_text_block({"text": "User message"}, "user")
        captured = capsys.readouterr()
        assert captured.out == ""

    def test_empty_text_ignored(self, capsys):
        """Empty text is not formatted."""
        _handle_text_block({"text": "   "}, "assistant")
        captured = capsys.readouterr()
        assert captured.out == ""


class TestHandleThinkingBlock:
    """Test _handle_thinking_block helper."""

    def test_delegates_to_formatter(self, capsys):
        """Delegates to formatter.format_thinking."""
        _handle_thinking_block({"thinking": "x" * 200})
        captured = capsys.readouterr()
        assert "thinking" in captured.out


class TestStoreToolUse:
    """Test _store_tool_use helper."""

    def test_stores_tool_info(self):
        """Stores tool use info in pending_tool_uses."""
        pending_tool_uses.clear()
        _store_tool_use({"id": "tool123", "name": "Bash", "input": {"command": "ls"}})
        assert "tool123" in pending_tool_uses
        assert pending_tool_uses["tool123"]["name"] == "Bash"
        assert pending_tool_uses["tool123"]["input"]["command"] == "ls"

    def test_evicts_oldest_when_full(self):
        """Evicts oldest tool when at capacity."""
        pending_tool_uses.clear()
        # Fill with 100 tools
        for i in range(100):
            pending_tool_uses[f"tool{i}"] = {"name": f"Tool{i}"}
        # Add one more
        _store_tool_use({"id": "new_tool", "name": "NewTool", "input": {}})
        assert "new_tool" in pending_tool_uses
        assert "tool0" not in pending_tool_uses  # First one evicted


class TestExtractResultText:
    """Test _extract_result_text helper."""

    def test_list_content(self):
        """Extracts text from list content."""
        content = [
            {"type": "text", "text": "line1"},
            {"type": "text", "text": "line2"},
        ]
        result = _extract_result_text(content)
        assert result == "line1\nline2"

    def test_string_content(self):
        """Handles string content."""
        result = _extract_result_text("simple string")
        assert result == "simple string"

    def test_filters_non_text(self):
        """Filters out non-text items."""
        content = [
            {"type": "text", "text": "keep"},
            {"type": "image", "data": "..."},
        ]
        result = _extract_result_text(content)
        assert result == "keep"


class TestHandleToolResultBlock:
    """Test _handle_tool_result_block helper."""

    def test_matches_pending_tool(self, capsys):
        """Matches tool result with pending tool use."""
        pending_tool_uses.clear()
        pending_tool_uses["tool456"] = {"name": "Bash", "input": {"command": "echo hi"}}
        _handle_tool_result_block({"tool_use_id": "tool456", "content": "hi"})
        captured = capsys.readouterr()
        assert "bash:" in captured.out
        assert "tool456" not in pending_tool_uses  # Removed after matching

    def test_orphan_tool_result(self, capsys):
        """Handles orphan tool result."""
        pending_tool_uses.clear()
        _handle_tool_result_block({"tool_use_id": "unknown123", "content": "result"})
        captured = capsys.readouterr()
        assert "orphan" in captured.err


class TestProcessContentBlock:
    """Test _process_content_block helper."""

    def test_text_block(self, capsys):
        """Processes text block."""
        _process_content_block({"type": "text", "text": "Hello"}, "assistant")
        captured = capsys.readouterr()
        assert "Hello" in captured.out

    def test_thinking_block(self, capsys):
        """Processes thinking block."""
        _process_content_block({"type": "thinking", "thinking": "x" * 200}, "assistant")
        captured = capsys.readouterr()
        assert "thinking" in captured.out

    def test_tool_use_block(self):
        """Processes tool_use block."""
        pending_tool_uses.clear()
        _process_content_block(
            {"type": "tool_use", "id": "t1", "name": "Read", "input": {}},
            "assistant",
        )
        assert "t1" in pending_tool_uses

    def test_tool_result_block(self, capsys):
        """Processes tool_result block."""
        pending_tool_uses.clear()
        pending_tool_uses["t2"] = {"name": "Bash", "input": {"command": "ls"}}
        _process_content_block(
            {"type": "tool_result", "tool_use_id": "t2", "content": "output"},
            "user",
        )
        captured = capsys.readouterr()
        assert "bash:" in captured.out

    def test_unknown_block_ignored(self, capsys):
        """Unknown block type is ignored."""
        _process_content_block({"type": "unknown"}, "assistant")
        captured = capsys.readouterr()
        assert captured.out == ""


class TestClaudeMsgHandlers:
    """Test CLAUDE_MSG_HANDLERS dispatch table."""

    def test_all_handlers_registered(self):
        """Expected handlers are registered."""
        expected = {"init", "result"}
        assert set(CLAUDE_MSG_HANDLERS.keys()) == expected

    def test_all_handlers_callable(self):
        """All handlers are callable."""
        for name, handler in CLAUDE_MSG_HANDLERS.items():
            assert callable(handler), f"Handler for {name} is not callable"


class TestProcessMessage:
    """Test process_message integration."""

    def test_init_message(self, capsys):
        """init message is processed."""
        process_message({"type": "init"})
        captured = capsys.readouterr()
        assert "Claude Session Started" in captured.out

    def test_result_message(self, capsys):
        """result message is processed."""
        process_message({"type": "result", "stats": {}})
        captured = capsys.readouterr()
        assert "Session Complete" in captured.out

    def test_content_message(self, capsys):
        """Content message is processed."""
        process_message(
            {
                "message": {
                    "role": "assistant",
                    "content": [{"type": "text", "text": "Response text"}],
                },
            }
        )
        captured = capsys.readouterr()
        assert "Response text" in captured.out

    def test_string_content_normalized(self, capsys):
        """String content is normalized to list."""
        process_message(
            {
                "role": "assistant",
                "content": "Direct string content",
            }
        )
        captured = capsys.readouterr()
        assert "Direct string content" in captured.out

    def test_tool_use_and_result(self, capsys):
        """Tool use followed by result."""
        pending_tool_uses.clear()
        # Tool use
        process_message(
            {
                "message": {
                    "role": "assistant",
                    "content": [
                        {
                            "type": "tool_use",
                            "id": "t999",
                            "name": "Grep",
                            "input": {"pattern": "TODO"},
                        }
                    ],
                },
            }
        )
        # Tool result
        process_message(
            {
                "role": "user",
                "content": [
                    {
                        "type": "tool_result",
                        "tool_use_id": "t999",
                        "content": "src/main.py:10: TODO",
                    }
                ],
            }
        )
        captured = capsys.readouterr()
        assert "grep:" in captured.out


# ============================================================================
# Tests for uncovered edge cases
# ============================================================================


class TestUseColors:
    """Test USE_COLORS branch (lines 26-34)."""

    def test_colors_with_force_color_env(self):
        """FORCE_COLOR=1 enables colors even without TTY."""
        # Run a subprocess that checks if colors are enabled
        code = """
import os
os.environ["FORCE_COLOR"] = "1"
import sys
sys.path.insert(0, "ai_template_scripts")
# Force re-import with new env
import importlib
import json_to_text
importlib.reload(json_to_text)
print(f"BLUE={repr(json_to_text.BLUE)}")
"""
        result = subprocess.run(
            ["python3", "-c", code],
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent),
        )
        # When FORCE_COLOR=1, BLUE should be an ANSI escape sequence
        # \x1b is the hex escape character (same as \033 octal)
        assert "\\x1b[94m" in result.stdout or "\\033[94m" in result.stdout


class TestFormatToolOutputGenericFallback:
    """Test format_tool_output generic fallback for unknown tools (lines 117-119)."""

    def test_generic_tool_two_lines_shows_all(self):
        """Generic tool with 2 lines shows all."""
        result = format_tool_output("line1\nline2", "UnknownTool")
        assert result == ["line1", "line2"]

    def test_generic_tool_many_lines_truncated(self):
        """Generic tool with many lines shows first + ellipsis."""
        lines = "\n".join([f"line{i}" for i in range(10)])
        result = format_tool_output(lines, "UnknownTool")
        assert len(result) == 2
        assert result[0] == "line0"
        assert "more lines" in result[1]


class TestMessageFormatterParagraphs:
    """Test MessageFormatter empty paragraph handling (lines 281, 288, 295)."""

    def test_format_text_multiple_paragraphs(self, capsys):
        """Multiple paragraphs are indented properly."""
        formatter = MessageFormatter()
        formatter.format_text_message("Paragraph one.\n\nParagraph two.")
        captured = capsys.readouterr()
        assert "Paragraph one." in captured.out
        assert "Paragraph two." in captured.out

    def test_format_text_empty_paragraph_skipped(self, capsys):
        """Empty paragraphs between content are skipped."""
        formatter = MessageFormatter()
        formatter.format_text_message("First\n\n\n\nSecond")
        captured = capsys.readouterr()
        assert "First" in captured.out
        assert "Second" in captured.out

    def test_format_text_only_empty_paragraphs(self, capsys):
        """Text with only whitespace paragraphs produces no output."""
        formatter = MessageFormatter()
        formatter.format_text_message("   \n\n   \n\n   ")
        captured = capsys.readouterr()
        assert captured.out == ""

    def test_format_tool_use_none_input(self, capsys):
        """format_tool_use handles None input_data (line 295)."""
        formatter = MessageFormatter()
        formatter.format_tool_use("Bash", None, "output")
        captured = capsys.readouterr()
        # Should still format with empty input
        assert "bash:" in captured.out


class TestCodexFormatterParagraphs:
    """Test CodexFormatter empty paragraph handling (lines 345, 351, 355)."""

    def test_format_agent_message_multiple_paragraphs(self, capsys):
        """Multiple paragraphs are formatted with proper indentation."""
        formatter = CodexFormatter()
        formatter.format_agent_message({"text": "Para one.\n\nPara two."})
        captured = capsys.readouterr()
        assert "Para one." in captured.out
        assert "Para two." in captured.out

    def test_format_agent_message_empty_paragraphs_skipped(self, capsys):
        """Empty paragraphs between content are skipped."""
        formatter = CodexFormatter()
        formatter.format_agent_message({"text": "First\n\n\n\nSecond"})
        captured = capsys.readouterr()
        assert "First" in captured.out
        assert "Second" in captured.out

    def test_format_agent_message_cleaned_empty(self, capsys):
        """Agent message that becomes empty after cleaning produces no output."""
        formatter = CodexFormatter()
        # The clean_output function removes Co-Authored-By lines
        formatter.format_agent_message(
            {"text": "Co-Authored-By: Claude <noreply@anthropic.com>"}
        )
        captured = capsys.readouterr()
        assert captured.out == ""

    def test_format_agent_message_content_fallback(self, capsys):
        """Agent message falls back to 'content' field."""
        formatter = CodexFormatter()
        formatter.format_agent_message({"content": "Using content field"})
        captured = capsys.readouterr()
        assert "Using content field" in captured.out


class TestCodexFormatterCommandEdgeCases:
    """Test CodexFormatter command execution edge cases (lines 368, 386-388)."""

    def test_format_command_long_truncated(self, capsys):
        """Long command is truncated (line 368)."""
        formatter = CodexFormatter()
        long_cmd = "x" * 100
        formatter.format_command_execution(
            {
                "command": long_cmd,
                "exit_code": 0,
                "aggregated_output": "",
            }
        )
        captured = capsys.readouterr()
        assert "..." in captured.out
        # The truncated command should be less than 100 chars
        assert len(captured.out.split("bash:")[1].split("\n")[0]) < 90

    def test_format_command_long_output(self, capsys):
        """Long output shows first, ellipsis, and last line (lines 386-388)."""
        formatter = CodexFormatter()
        lines = "\n".join([f"line{i}" for i in range(10)])
        formatter.format_command_execution(
            {
                "command": "echo test",
                "exit_code": 0,
                "aggregated_output": lines,
            },
            status="completed",
        )
        captured = capsys.readouterr()
        assert "line0" in captured.out
        assert "more lines" in captured.out
        assert "line9" in captured.out


class TestCodexFormatterFileChangeDelete:
    """Test CodexFormatter file change delete (line 400)."""

    def test_format_file_change_delete(self, capsys):
        """File deletion is formatted with delete: prefix."""
        formatter = CodexFormatter()
        formatter.format_file_change(
            {
                "file_path": "/path/to/deleted.py",
                "change_type": "delete",
            }
        )
        captured = capsys.readouterr()
        assert "delete:" in captured.out
        assert "/path/to/deleted.py" in captured.out


class TestCodexFormatterMCPWebSearchTodoList:
    """Test CodexFormatter MCP/web_search/todo_list (lines 416-430)."""

    def test_format_mcp_tool_call(self, capsys):
        """MCP tool call is formatted (lines 416-418)."""
        formatter = CodexFormatter()
        formatter.format_mcp_tool_call({"tool_name": "my_mcp_tool"})
        captured = capsys.readouterr()
        assert "mcp:" in captured.out
        assert "my_mcp_tool" in captured.out

    def test_format_mcp_tool_call_name_fallback(self, capsys):
        """MCP tool call falls back to 'name' field."""
        formatter = CodexFormatter()
        formatter.format_mcp_tool_call({"name": "fallback_name"})
        captured = capsys.readouterr()
        assert "mcp:" in captured.out
        assert "fallback_name" in captured.out

    def test_format_web_search(self, capsys):
        """Web search is formatted (lines 422-424)."""
        formatter = CodexFormatter()
        formatter.format_web_search({"query": "test query"})
        captured = capsys.readouterr()
        assert "search:" in captured.out
        assert "test query" in captured.out

    def test_format_web_search_long_truncated(self, capsys):
        """Long web search query is truncated."""
        formatter = CodexFormatter()
        long_query = "x" * 100
        formatter.format_web_search({"query": long_query})
        captured = capsys.readouterr()
        assert "search:" in captured.out
        assert "..." in captured.out

    def test_format_todo_list(self, capsys):
        """Todo list is formatted (lines 428-430)."""
        formatter = CodexFormatter()
        formatter.format_todo_list({"todos": [1, 2, 3]})
        captured = capsys.readouterr()
        assert "todo:" in captured.out
        assert "3 items" in captured.out

    def test_format_todo_list_empty(self, capsys):
        """Empty todo list is formatted."""
        formatter = CodexFormatter()
        formatter.format_todo_list({})
        captured = capsys.readouterr()
        assert "todo:" in captured.out
        assert "0 items" in captured.out


class TestIsCodexEventErrorCase:
    """Test is_codex_event error case (line 564)."""

    def test_error_without_item_or_message_is_codex(self):
        """Error event without 'item' or 'message' is Codex (line 564)."""
        # This tests the specific condition on line 564
        assert is_codex_event({"type": "error"}) is True

    def test_error_with_message_is_not_codex(self):
        """Error event with 'message' is Claude."""
        assert is_codex_event({"type": "error", "message": {}}) is False

    def test_error_with_item_is_not_codex(self):
        """Error event with 'item' is Claude."""
        assert is_codex_event({"type": "error", "item": {}}) is False


class TestMainFunction:
    """Test main() function (lines 713-737, 741)."""

    def test_main_processes_json_lines(self):
        """main() processes JSON lines from stdin."""
        code = """
import sys
sys.path.insert(0, "ai_template_scripts")
from json_to_text import main
main()
"""
        result = subprocess.run(
            ["python3", "-c", code],
            input='{"type": "init"}\n',
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent),
        )
        assert "Claude Session Started" in result.stdout

    def test_main_handles_invalid_json(self):
        """main() handles invalid JSON by printing it."""
        code = """
import sys
sys.path.insert(0, "ai_template_scripts")
from json_to_text import main
main()
"""
        result = subprocess.run(
            ["python3", "-c", code],
            input="not json\n",
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent),
        )
        assert "not json" in result.stdout

    def test_main_skips_empty_lines(self):
        """main() skips empty lines."""
        code = """
import sys
sys.path.insert(0, "ai_template_scripts")
from json_to_text import main
main()
"""
        result = subprocess.run(
            ["python3", "-c", code],
            input='\n\n{"type": "init"}\n\n',
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent),
        )
        assert "Claude Session Started" in result.stdout

    def test_main_handles_codex_events(self):
        """main() dispatches Codex events correctly."""
        code = """
import sys
sys.path.insert(0, "ai_template_scripts")
from json_to_text import main
main()
"""
        result = subprocess.run(
            ["python3", "-c", code],
            input='{"type": "thread.started"}\n',
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent),
        )
        assert "Codex Session Started" in result.stdout

    def test_main_keyboard_interrupt(self):
        """main() handles KeyboardInterrupt gracefully."""
        code = """
import sys
import signal
sys.path.insert(0, "ai_template_scripts")

# Set up a handler that raises KeyboardInterrupt after first line
import json_to_text
original_stdin = sys.stdin

class InterruptingStdin:
    def __init__(self):
        self.first_read = True
    def __iter__(self):
        return self
    def __next__(self):
        if self.first_read:
            self.first_read = False
            return '{"type": "init"}'
        raise KeyboardInterrupt()

sys.stdin = InterruptingStdin()
json_to_text.main()
"""
        result = subprocess.run(
            ["python3", "-c", code],
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent),
        )
        assert result.returncode == 0
        assert "Interrupted" in result.stdout

    def test_main_broken_pipe(self):
        """main() handles BrokenPipeError gracefully."""
        code = """
import sys
sys.path.insert(0, "ai_template_scripts")

import json_to_text

# Mock stdin that raises BrokenPipeError on iteration
class BrokenPipeStdin:
    def __iter__(self):
        return self
    def __next__(self):
        raise BrokenPipeError()

sys.stdin = BrokenPipeStdin()
json_to_text.main()
"""
        result = subprocess.run(
            ["python3", "-c", code],
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent),
        )
        assert result.returncode == 0

    def test_main_as_script(self):
        """Running json_to_text.py as script executes main (line 741)."""
        result = subprocess.run(
            ["python3", "ai_template_scripts/json_to_text.py"],
            input='{"type": "init"}\n',
            capture_output=True,
            text=True,
            cwd=str(Path(__file__).parent.parent),
        )
        assert "Claude Session Started" in result.stdout
