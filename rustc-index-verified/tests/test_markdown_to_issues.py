"""
Tests for markdown_to_issues.py

Tests the Parser class and utility functions without hitting GitHub API.
"""

import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

# Add parent dir to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "ai_template_scripts"))

from markdown_to_issues import (
    PRIORITIES,
    STANDARD_LABELS,
    Issue,
    Parser,
    ValidationResult,
    categorize_issues,
    close_issue,
    create_issue,
    execute_changes,
    export_issues,
    gh,
    gh_json,
    gh_list_all,
    log,
    main,
    print_dry_run,
    print_results,
    priority_sort_key,
    report_warnings,
    setup_labels,
    update_issue,
    validate_issues,
)


class TestIssueDataclass:
    """Test Issue dataclass methods."""

    def test_labels_str_basic(self):
        """Labels string with simple labels."""
        issue = Issue(title="Test", labels=["bug", "task"])
        assert issue.labels_str() == "bug,task"

    def test_labels_str_with_priority(self):
        """Priority is appended if not already in labels."""
        issue = Issue(title="Test", labels=["task"], priority="P1")
        assert issue.labels_str() == "task,P1"

    def test_labels_str_priority_not_duplicated(self):
        """Priority not duplicated if already in labels."""
        issue = Issue(title="Test", labels=["task", "P1"], priority="P1")
        assert issue.labels_str() == "task,P1"

    def test_full_body_without_depends(self):
        """Body without depends field."""
        issue = Issue(title="Test", body="Description here")
        assert issue.full_body() == "Description here"

    def test_full_body_with_depends(self):
        """Body with depends field appended."""
        issue = Issue(title="Test", body="Description", depends="#42")
        assert "**Depends on:** #42" in issue.full_body()
        assert "Description" in issue.full_body()


class TestParser:
    """Test markdown parsing."""

    def parse_markdown(self, content: str) -> list[Issue]:
        """Helper to parse markdown content."""
        path = Path("/tmp/test_roadmap.md")
        path.write_text(content)
        try:
            parser = Parser(path)
            return parser.parse()
        finally:
            path.unlink()

    def test_parse_simple_issue(self):
        """Parse a simple issue."""
        md = """
## Fix the bug
**Labels:** bug
**Priority:** P1

This is the description.
"""
        issues = self.parse_markdown(md)
        assert len(issues) == 1
        assert issues[0].title == "Fix the bug"
        assert issues[0].labels == ["bug"]
        assert issues[0].priority == "P1"
        assert "description" in issues[0].body.lower()

    def test_parse_multiple_issues(self):
        """Parse multiple issues separated by ---."""
        md = """
## First task
**Labels:** task
**Priority:** P1

Description one.

---

## Second task
**Labels:** enhancement
**Priority:** P2

Description two.
"""
        issues = self.parse_markdown(md)
        assert len(issues) == 2
        assert issues[0].title == "First task"
        assert issues[1].title == "Second task"

    def test_parse_existing_issue_number(self):
        """Parse issue with existing number for update."""
        md = """
## #42: Update existing
**Labels:** task

Updated description.
"""
        issues = self.parse_markdown(md)
        assert len(issues) == 1
        assert issues[0].existing_number == 42
        assert issues[0].title == "Update existing"

    def test_parse_done_marker(self):
        """Parse issue with [DONE] marker."""
        md = """
## [DONE] Completed task
**Labels:** task

This is done.
"""
        issues = self.parse_markdown(md)
        assert len(issues) == 1
        assert issues[0].status == "done"
        assert issues[0].title == "Completed task"

    def test_parse_closed_marker(self):
        """Parse issue with [CLOSED] marker."""
        md = """
## [CLOSED] Also done
**Labels:** task

Closed.
"""
        issues = self.parse_markdown(md)
        assert len(issues) == 1
        assert issues[0].status == "done"

    def test_parse_wip_marker(self):
        """Parse issue with [WIP] marker."""
        md = """
## [WIP] In progress
**Labels:** task

Working on it.
"""
        issues = self.parse_markdown(md)
        assert len(issues) == 1
        assert issues[0].status == "wip"

    def test_parse_milestone(self):
        """Parse milestone field."""
        md = """
## Feature
**Labels:** task
**Milestone:** v1.0

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].milestone == "v1.0"

    def test_parse_assignee(self):
        """Parse assignee field with @ prefix."""
        md = """
## Task
**Labels:** task
**Assignee:** @username

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].assignee == "username"

    def test_parse_depends(self):
        """Parse depends field."""
        md = """
## Task
**Labels:** task
**Depends on:** #12, #34

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].depends == "#12, #34"

    def test_strip_html_comments(self):
        """HTML comments are stripped from content."""
        md = """
## Task
**Labels:** task

<!-- This comment should be removed -->
Visible description.
<!-- Another comment -->
"""
        issues = self.parse_markdown(md)
        assert "comment" not in issues[0].body.lower()
        assert "Visible description" in issues[0].body

    def test_ignore_h1_and_blockquotes(self):
        """H1 headers and blockquotes are not parsed as issues."""
        md = """
# Main title

> This is a note

## Actual task
**Labels:** task

Description.
"""
        issues = self.parse_markdown(md)
        assert len(issues) == 1
        assert issues[0].title == "Actual task"

    def test_case_insensitive_fields(self):
        """Field names are case-insensitive."""
        md = """
## Task
**labels:** task
**PRIORITY:** P1

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].labels == ["task"]
        assert issues[0].priority == "P1"

    def test_multiple_labels(self):
        """Parse comma-separated labels."""
        md = """
## Task
**Labels:** task, bug, enhancement

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].labels == ["task", "bug", "enhancement"]


class TestParserValidation:
    """Test parser validation and warnings."""

    def parse_with_warnings(self, content: str) -> tuple[list[Issue], list[str]]:
        """Helper that returns both issues and warnings."""
        path = Path("/tmp/test_roadmap.md")
        path.write_text(content)
        try:
            parser = Parser(path)
            issues = parser.parse()
            return issues, parser.warnings
        finally:
            path.unlink()

    def test_warning_short_title(self):
        """Warning for title less than 3 chars."""
        md = """
## AB
**Labels:** task

Description here.
"""
        issues, warnings = self.parse_with_warnings(md)
        assert any("Title too short" in w for w in warnings)

    def test_warning_short_body(self):
        """Warning for body less than 5 chars."""
        md = """
## Valid title
**Labels:** task

Hi
"""
        issues, warnings = self.parse_with_warnings(md)
        assert any("Body too short" in w for w in warnings)

    def test_warning_invalid_priority(self):
        """Warning for invalid priority value."""
        md = """
## Task
**Labels:** task
**Priority:** HIGH

Description here.
"""
        issues, warnings = self.parse_with_warnings(md)
        assert any("Invalid priority" in w for w in warnings)

    def test_valid_priorities(self):
        """All valid priorities are accepted."""
        for priority in PRIORITIES:
            md = f"""
## Task
**Labels:** task
**Priority:** {priority}

Description here.
"""
            issues, warnings = self.parse_with_warnings(md)
            assert not any("Invalid priority" in w for w in warnings)
            assert issues[0].priority == priority


class TestPrioritySortKey:
    """Test priority sorting."""

    def test_p0_first(self):
        """P0 has lowest sort key (highest priority)."""
        issue = {"labels": [{"name": "P0"}]}
        assert priority_sort_key(issue) == 0

    def test_p3_last(self):
        """P3 has highest sort key among priorities."""
        issue = {"labels": [{"name": "P3"}]}
        assert priority_sort_key(issue) == 3

    def test_no_priority_last(self):
        """Issues without priority sort last."""
        issue = {"labels": [{"name": "task"}]}
        assert priority_sort_key(issue) == 99

    def test_empty_labels(self):
        """Issues with no labels sort last."""
        issue = {"labels": []}
        assert priority_sort_key(issue) == 99

    def test_mixed_labels(self):
        """Priority extracted from mixed labels."""
        issue = {"labels": [{"name": "task"}, {"name": "P2"}, {"name": "bug"}]}
        assert priority_sort_key(issue) == 2


class TestTitleParsing:
    """Test _parse_title edge cases."""

    def parse_title(self, raw: str) -> tuple:
        """Helper to parse a title string."""
        path = Path("/tmp/dummy.md")
        path.write_text("## test\n**Labels:** task\n\ndesc")
        try:
            parser = Parser(path)
            return parser._parse_title(raw)  # noqa: SLF001
        finally:
            path.unlink()

    def test_plain_title(self):
        """Plain title without markers."""
        title, num, status = self.parse_title("Simple title")
        assert title == "Simple title"
        assert num is None
        assert status is None

    def test_issue_number_with_colon(self):
        """Issue number with colon separator."""
        title, num, status = self.parse_title("#123: Updated title")
        assert title == "Updated title"
        assert num == 123
        assert status is None

    def test_issue_number_without_colon(self):
        """Issue number without colon."""
        title, num, status = self.parse_title("#456 Title here")
        assert title == "Title here"
        assert num == 456

    def test_done_before_number(self):
        """[DONE] marker before issue number."""
        title, num, status = self.parse_title("[DONE] #42: Finished")
        assert title == "Finished"
        assert num == 42
        assert status == "done"

    def test_done_after_number(self):
        """[DONE] marker after issue number."""
        title, num, status = self.parse_title("#42: [DONE] Finished")
        assert title == "Finished"
        assert num == 42
        assert status == "done"

    def test_in_progress_marker(self):
        """[IN-PROGRESS] marker."""
        title, num, status = self.parse_title("[IN-PROGRESS] Working")
        assert title == "Working"
        assert status == "wip"

    def test_case_insensitive_markers(self):
        """Markers are case-insensitive."""
        title, num, status = self.parse_title("[done] Lower case")
        assert title == "Lower case"
        assert status == "done"

    def test_closed_marker(self):
        """[CLOSED] marker."""
        title, num, status = self.parse_title("[CLOSED] Task")
        assert title == "Task"
        assert status == "done"


class TestParserStatusField:
    """Test status field parsing."""

    def parse_markdown(self, content: str) -> list[Issue]:
        """Helper to parse markdown content."""
        path = Path("/tmp/test_roadmap.md")
        path.write_text(content)
        try:
            parser = Parser(path)
            return parser.parse()
        finally:
            path.unlink()

    def test_status_done(self):
        """Status: done field."""
        md = """
## Task
**Labels:** task
**Status:** done

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].status == "done"

    def test_status_closed(self):
        """Status: closed maps to done."""
        md = """
## Task
**Labels:** task
**Status:** closed

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].status == "done"

    def test_status_complete(self):
        """Status: complete maps to done."""
        md = """
## Task
**Labels:** task
**Status:** complete

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].status == "done"


class TestParserEdgeCases:
    """Test parser edge cases."""

    def parse_markdown(self, content: str) -> list[Issue]:
        """Helper to parse markdown content."""
        path = Path("/tmp/test_roadmap.md")
        path.write_text(content)
        try:
            parser = Parser(path)
            return parser.parse()
        finally:
            path.unlink()

    def test_list_style_fields(self):
        """Fields with list-style prefixes (- or *)."""
        md = """
## Task
- Labels: task, bug
- Priority: P2

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].labels == ["task", "bug"]
        assert issues[0].priority == "P2"

    def test_depends_without_on(self):
        """Depends without 'on' suffix."""
        md = """
## Task
**Labels:** task
**Depends:** #42

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].depends == "#42"

    def test_default_label(self):
        """Default label is 'task' when not specified."""
        md = """
## Task without labels

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].labels == ["task"]

    def test_whitespace_in_labels(self):
        """Whitespace in labels is trimmed."""
        md = """
## Task
**Labels:**   task  ,  bug  ,  enhancement

Description.
"""
        issues = self.parse_markdown(md)
        assert issues[0].labels == ["task", "bug", "enhancement"]

    def test_multiple_issues_at_end(self):
        """Last issue is properly finalized."""
        md = """
## First
**Labels:** task

First description.

## Second
**Labels:** bug

Second description.
"""
        issues = self.parse_markdown(md)
        assert len(issues) == 2
        assert issues[1].title == "Second"
        assert "Second description" in issues[1].body


class TestIssueEdgeCases:
    """Test Issue dataclass edge cases."""

    def test_empty_body_with_depends(self):
        """Empty body with depends still works."""
        issue = Issue(title="Test", body="  ", depends="#42")
        body = issue.full_body()
        assert "**Depends on:** #42" in body

    def test_no_labels_no_priority(self):
        """Empty labels without priority."""
        issue = Issue(title="Test", labels=[])
        assert issue.labels_str() == ""

    def test_no_labels_with_priority(self):
        """No labels but has priority."""
        issue = Issue(title="Test", labels=[], priority="P0")
        assert issue.labels_str() == "P0"


class TestCategorizeIssues:
    """Test issue categorization helper."""

    def test_categorize_new_issues(self):
        """Issues without existing_number are new."""
        issues = [
            Issue(title="New one"),
            Issue(title="New two"),
        ]
        new, update, close = categorize_issues(issues)
        assert len(new) == 2
        assert len(update) == 0
        assert len(close) == 0

    def test_categorize_update_issues(self):
        """Issues with existing_number but not done are updates."""
        issues = [
            Issue(title="Update me", existing_number=42),
            Issue(title="Update too", existing_number=43),
        ]
        new, update, close = categorize_issues(issues)
        assert len(new) == 0
        assert len(update) == 2
        assert len(close) == 0

    def test_categorize_close_issues(self):
        """Issues with existing_number and status=done are closes."""
        issues = [
            Issue(title="Done", existing_number=42, status="done"),
        ]
        new, update, close = categorize_issues(issues)
        assert len(new) == 0
        assert len(update) == 0
        assert len(close) == 1

    def test_categorize_mixed(self):
        """Mix of new, update, and close issues."""
        issues = [
            Issue(title="New"),
            Issue(title="Update", existing_number=10),
            Issue(title="Close", existing_number=20, status="done"),
        ]
        new, update, close = categorize_issues(issues)
        assert len(new) == 1
        assert new[0].title == "New"
        assert len(update) == 1
        assert update[0].title == "Update"
        assert len(close) == 1
        assert close[0].title == "Close"


class TestReportWarnings:
    """Test warning report helper."""

    def test_report_parser_warnings(self, capsys):
        """Parser warnings are logged."""
        validation = ValidationResult(duplicates={}, bad_labels=[], existing_titles={})
        count = report_warnings(["Title too short", "Body too short"], validation)
        assert count == 2
        captured = capsys.readouterr()
        assert "Title too short" in captured.err
        assert "Body too short" in captured.err

    def test_report_duplicates(self, capsys):
        """Duplicate warnings are logged."""
        validation = ValidationResult(
            duplicates={"My Task": 42},
            bad_labels=[],
            existing_titles={"my task": 42},
        )
        count = report_warnings([], validation)
        assert count == 1
        captured = capsys.readouterr()
        assert "duplicates #42" in captured.err

    def test_report_bad_labels(self, capsys):
        """Bad label warnings are logged."""
        validation = ValidationResult(
            duplicates={},
            bad_labels=[("My Task", "unknown-label")],
            existing_titles={},
        )
        count = report_warnings([], validation)
        assert count == 1
        captured = capsys.readouterr()
        assert "Unknown label 'unknown-label'" in captured.err

    def test_report_combined_count(self, capsys):
        """Total count includes all warning types."""
        validation = ValidationResult(
            duplicates={"Task A": 1, "Task B": 2},
            bad_labels=[("Task C", "bad1"), ("Task D", "bad2"), ("Task E", "bad3")],
            existing_titles={},
        )
        count = report_warnings(["parser warn"], validation)
        assert count == 6  # 1 parser + 2 dupes + 3 bad labels


class TestValidationResult:
    """Test ValidationResult dataclass."""

    def test_empty_validation(self):
        """Empty validation result."""
        result = ValidationResult(duplicates={}, bad_labels=[], existing_titles={})
        assert len(result.duplicates) == 0
        assert len(result.bad_labels) == 0
        assert len(result.existing_titles) == 0

    def test_validation_with_data(self):
        """Validation result with data."""
        result = ValidationResult(
            duplicates={"Task": 42},
            bad_labels=[("Task", "invalid")],
            existing_titles={"task": 42, "other": 43},
        )
        assert result.duplicates["Task"] == 42
        assert result.bad_labels[0] == ("Task", "invalid")
        assert len(result.existing_titles) == 2


# Tests requiring mocked gh calls


class TestGhFunction:
    """Test gh helper function."""

    @patch("markdown_to_issues.subprocess.run")
    def test_gh_runs_command(self, mock_run):
        """gh runs command with gh prefix."""
        mock_run.return_value = MagicMock(returncode=0, stdout="output", stderr="")
        result = gh(["issue", "list"])
        mock_run.assert_called_once_with(
            ["gh", "issue", "list"], check=False, capture_output=True, text=True
        )
        assert result.returncode == 0


class TestGhJsonFunction:
    """Test gh_json helper function."""

    @patch("markdown_to_issues.gh")
    def test_gh_json_success(self, mock_gh):
        """gh_json returns stdout on success."""
        mock_gh.return_value = MagicMock(returncode=0, stdout='[{"id": 1}]', stderr="")
        result = gh_json(["issue", "list"])
        assert result == '[{"id": 1}]'

    @patch("markdown_to_issues.gh")
    def test_gh_json_failure_returns_default(self, mock_gh, capsys):
        """gh_json returns default on failure and logs error."""
        mock_gh.return_value = MagicMock(
            returncode=1, stdout="", stderr="API rate limit"
        )
        result = gh_json(["issue", "list"], default="[]")
        assert result == "[]"
        captured = capsys.readouterr()
        assert "API rate limit" in captured.err

    @patch("markdown_to_issues.gh")
    def test_gh_json_empty_stdout_returns_default(self, mock_gh):
        """gh_json returns default when stdout is empty."""
        mock_gh.return_value = MagicMock(returncode=0, stdout="", stderr="")
        result = gh_json(["issue", "list"], default="[]")
        assert result == "[]"

    @patch("markdown_to_issues.gh")
    def test_gh_json_failure_unknown_error(self, mock_gh, capsys):
        """gh_json logs 'unknown error' when stderr is empty."""
        mock_gh.return_value = MagicMock(returncode=1, stdout="", stderr="")
        gh_json(["issue", "list"])
        captured = capsys.readouterr()
        assert "unknown error" in captured.err


class TestGhListAll:
    """Test gh_list_all function."""

    @patch("markdown_to_issues.gh")
    def test_gh_list_all_success(self, mock_gh):
        """gh_list_all returns parsed JSON list."""
        mock_gh.return_value = MagicMock(
            returncode=0,
            stdout='[{"number": 1}, {"number": 2}]',
            stderr="",
        )
        result = gh_list_all(["issue", "list"], "number,title")
        assert len(result) == 2
        assert result[0]["number"] == 1

    @patch("markdown_to_issues.gh")
    def test_gh_list_all_failure_returns_empty(self, mock_gh, capsys):
        """gh_list_all returns empty list on failure."""
        mock_gh.return_value = MagicMock(returncode=1, stdout="", stderr="error")
        result = gh_list_all(["issue", "list"], "number")
        assert result == []
        captured = capsys.readouterr()
        assert "error" in captured.err

    @patch("markdown_to_issues.gh")
    def test_gh_list_all_custom_limit(self, mock_gh):
        """gh_list_all uses custom limit."""
        mock_gh.return_value = MagicMock(returncode=0, stdout="[]", stderr="")
        gh_list_all(["issue", "list"], "number", limit=500)
        call_args = mock_gh.call_args[0][0]
        assert "--limit" in call_args
        assert "500" in call_args


class TestSetupLabels:
    """Test setup_labels function."""

    @patch("markdown_to_issues.gh_json")
    @patch("markdown_to_issues.gh")
    def test_setup_labels_creates_new(self, mock_gh, mock_gh_json, capsys):
        """setup_labels creates new labels."""
        mock_gh_json.return_value = "[]"  # No existing labels
        mock_gh.return_value = MagicMock(returncode=0)
        results = setup_labels(dry_run=False)
        assert results["created"] == len(STANDARD_LABELS)
        assert results["failed"] == 0

    @patch("markdown_to_issues.gh_json")
    @patch("markdown_to_issues.gh")
    def test_setup_labels_updates_existing(self, mock_gh, mock_gh_json):
        """setup_labels updates existing labels."""
        mock_gh_json.return_value = '[{"name": "P0"}, {"name": "P1"}]'
        mock_gh.return_value = MagicMock(returncode=0)
        results = setup_labels(dry_run=False)
        assert results["updated"] == 2
        assert results["created"] == len(STANDARD_LABELS) - 2

    @patch("markdown_to_issues.gh_json")
    def test_setup_labels_dry_run(self, mock_gh_json, capsys):
        """setup_labels dry run only logs."""
        mock_gh_json.return_value = "[]"
        results = setup_labels(dry_run=True)
        assert results["created"] == 0
        assert results["updated"] == 0
        captured = capsys.readouterr()
        assert "Would create" in captured.err

    @patch("markdown_to_issues.gh_json")
    @patch("markdown_to_issues.gh")
    def test_setup_labels_failure(self, mock_gh, mock_gh_json, capsys):
        """setup_labels counts failures."""
        mock_gh_json.return_value = "[]"
        mock_gh.return_value = MagicMock(returncode=1)
        results = setup_labels(dry_run=False)
        assert results["failed"] == len(STANDARD_LABELS)
        captured = capsys.readouterr()
        assert "Failed" in captured.err


class TestExportIssues:
    """Test export_issues function."""

    @patch("markdown_to_issues.gh_list_all")
    def test_export_issues_basic(self, mock_list_all):
        """export_issues formats issues as markdown."""
        mock_list_all.return_value = [
            {
                "number": 1,
                "title": "Test Issue",
                "body": "Description",
                "labels": [{"name": "task"}, {"name": "P1"}],
                "milestone": None,
                "assignees": [],
                "state": "open",
            }
        ]
        result = export_issues()
        assert "# Issues (open)" in result
        assert "## #1: Test Issue" in result
        assert "Labels: task" in result
        assert "Priority: P1" in result
        assert "Description" in result

    @patch("markdown_to_issues.gh_list_all")
    def test_export_issues_closed(self, mock_list_all):
        """export_issues marks closed issues."""
        mock_list_all.return_value = [
            {
                "number": 42,
                "title": "Done",
                "body": "Body",
                "labels": [],
                "state": "CLOSED",
            }
        ]
        result = export_issues(state="all")
        assert "[CLOSED]" in result

    @patch("markdown_to_issues.gh_list_all")
    def test_export_issues_empty_body(self, mock_list_all):
        """export_issues handles empty body."""
        mock_list_all.return_value = [
            {
                "number": 1,
                "title": "No body",
                "body": "",
                "labels": [],
                "state": "open",
            }
        ]
        result = export_issues()
        assert "*(no description)*" in result

    @patch("markdown_to_issues.gh_list_all")
    def test_export_issues_sorted_by_priority(self, mock_list_all):
        """export_issues sorts by priority."""
        mock_list_all.return_value = [
            {
                "number": 1,
                "title": "Low",
                "body": "",
                "labels": [{"name": "P3"}],
                "state": "open",
            },
            {
                "number": 2,
                "title": "High",
                "body": "",
                "labels": [{"name": "P0"}],
                "state": "open",
            },
        ]
        result = export_issues()
        # P0 should come before P3
        assert result.index("#2: High") < result.index("#1: Low")


class TestCreateIssue:
    """Test create_issue function."""

    @patch("markdown_to_issues.gh")
    def test_create_issue_success(self, mock_gh):
        """create_issue returns issue number on success."""
        mock_gh.return_value = MagicMock(
            returncode=0,
            stdout="https://github.com/owner/repo/issues/42",
            stderr="",
        )
        issue = Issue(title="New Issue", labels=["task"], body="Description")
        result = create_issue(issue)
        assert result == 42

    @patch("markdown_to_issues.gh")
    def test_create_issue_with_milestone_and_assignee(self, mock_gh):
        """create_issue includes milestone and assignee."""
        mock_gh.return_value = MagicMock(
            returncode=0,
            stdout="https://github.com/owner/repo/issues/1",
            stderr="",
        )
        issue = Issue(
            title="Task",
            labels=["task"],
            body="Body",
            milestone="v1.0",
            assignee="user",
        )
        create_issue(issue)
        call_args = mock_gh.call_args[0][0]
        assert "--milestone" in call_args
        assert "v1.0" in call_args
        assert "--assignee" in call_args
        assert "user" in call_args

    @patch("markdown_to_issues.gh")
    def test_create_issue_failure(self, mock_gh, capsys):
        """create_issue returns None on failure."""
        mock_gh.return_value = MagicMock(returncode=1, stdout="", stderr="error")
        issue = Issue(title="Fail", body="Body")
        result = create_issue(issue)
        assert result is None
        captured = capsys.readouterr()
        assert "Failed to create" in captured.err

    @patch("markdown_to_issues.gh")
    def test_create_issue_no_number_in_output(self, mock_gh):
        """create_issue returns None when number not in output."""
        mock_gh.return_value = MagicMock(
            returncode=0, stdout="Created issue", stderr=""
        )
        issue = Issue(title="Test", body="Body")
        result = create_issue(issue)
        assert result is None


class TestUpdateIssue:
    """Test update_issue function."""

    @patch("markdown_to_issues.gh")
    def test_update_issue_success(self, mock_gh):
        """update_issue returns True on success."""
        mock_gh.return_value = MagicMock(returncode=0)
        issue = Issue(title="Updated", labels=["bug"], body="New body")
        result = update_issue(42, issue)
        assert result is True

    @patch("markdown_to_issues.gh")
    def test_update_issue_failure(self, mock_gh):
        """update_issue returns False on failure."""
        mock_gh.return_value = MagicMock(returncode=1)
        issue = Issue(title="Fail", body="Body")
        result = update_issue(42, issue)
        assert result is False

    @patch("markdown_to_issues.gh")
    def test_update_issue_with_milestone_assignee(self, mock_gh):
        """update_issue includes milestone and assignee."""
        mock_gh.return_value = MagicMock(returncode=0)
        issue = Issue(title="Task", body="Body", milestone="sprint1", assignee="dev")
        update_issue(1, issue)
        call_args = mock_gh.call_args[0][0]
        assert "--milestone" in call_args
        assert "--assignee" in call_args


class TestCloseIssue:
    """Test close_issue function."""

    @patch("markdown_to_issues.gh")
    def test_close_issue_success(self, mock_gh):
        """close_issue returns True on success."""
        mock_gh.return_value = MagicMock(returncode=0)
        result = close_issue(42)
        assert result is True
        mock_gh.assert_called_once_with(["issue", "close", "42"])

    @patch("markdown_to_issues.gh")
    def test_close_issue_failure(self, mock_gh):
        """close_issue returns False on failure."""
        mock_gh.return_value = MagicMock(returncode=1)
        result = close_issue(42)
        assert result is False


class TestValidateIssues:
    """Test validate_issues function."""

    @patch("markdown_to_issues.gh_json")
    @patch("markdown_to_issues.gh_list_all")
    def test_validate_finds_duplicates(self, mock_list_all, mock_gh_json):
        """validate_issues finds duplicate titles."""
        mock_list_all.return_value = [
            {"number": 10, "title": "Existing Task"},
        ]
        mock_gh_json.return_value = '[{"name": "task"}]'
        issues = [Issue(title="Existing Task", body="Body")]
        result = validate_issues(issues)
        assert "Existing Task" in result.duplicates
        assert result.duplicates["Existing Task"] == 10

    @patch("markdown_to_issues.gh_json")
    @patch("markdown_to_issues.gh_list_all")
    def test_validate_finds_bad_labels(self, mock_list_all, mock_gh_json):
        """validate_issues finds unknown labels."""
        mock_list_all.return_value = []
        mock_gh_json.return_value = '[{"name": "task"}, {"name": "bug"}]'
        issues = [Issue(title="Task", labels=["task", "unknown"], body="Body")]
        result = validate_issues(issues)
        assert ("Task", "unknown") in result.bad_labels

    @patch("markdown_to_issues.gh_json")
    @patch("markdown_to_issues.gh_list_all")
    def test_validate_ignores_existing_updates(self, mock_list_all, mock_gh_json):
        """validate_issues ignores issues marked for update."""
        mock_list_all.return_value = [{"number": 42, "title": "Existing"}]
        mock_gh_json.return_value = '[{"name": "task"}]'
        # Issue has existing_number, so it's an update, not duplicate
        issues = [Issue(title="Existing", existing_number=42, body="Body")]
        result = validate_issues(issues)
        assert len(result.duplicates) == 0

    @patch("markdown_to_issues.gh_json")
    @patch("markdown_to_issues.gh_list_all")
    def test_validate_bad_priority(self, mock_list_all, mock_gh_json):
        """validate_issues finds unknown priority labels."""
        mock_list_all.return_value = []
        mock_gh_json.return_value = '[{"name": "task"}]'
        issues = [Issue(title="Task", labels=["task"], priority="P5", body="Body")]
        result = validate_issues(issues)
        assert ("Task", "P5") in result.bad_labels


class TestPrintDryRun:
    """Test print_dry_run function."""

    def test_print_dry_run_new_issues(self, capsys):
        """print_dry_run shows create commands for new issues."""
        new = [Issue(title="New One"), Issue(title="New Two")]
        print_dry_run(new, [], [], sync=False)
        captured = capsys.readouterr()
        assert 'gh issue create --title "New One"' in captured.out
        assert 'gh issue create --title "New Two"' in captured.out

    def test_print_dry_run_sync_mode(self, capsys):
        """print_dry_run shows edit/close commands in sync mode."""
        update = [Issue(title="Update", existing_number=10)]
        close = [Issue(title="Close", existing_number=20, status="done")]
        print_dry_run([], update, close, sync=True)
        captured = capsys.readouterr()
        assert "gh issue edit 10" in captured.out
        assert "gh issue close 20" in captured.out

    def test_print_dry_run_no_sync_skips_edit_close(self, capsys):
        """print_dry_run skips edit/close when not in sync mode."""
        update = [Issue(title="Update", existing_number=10)]
        close = [Issue(title="Close", existing_number=20)]
        print_dry_run([], update, close, sync=False)
        captured = capsys.readouterr()
        assert "edit" not in captured.out
        assert "close" not in captured.out


class TestExecuteChanges:
    """Test execute_changes function."""

    @patch("markdown_to_issues.time.sleep")
    @patch("markdown_to_issues.create_issue")
    def test_execute_creates_new_issues(self, mock_create, mock_sleep, capsys):
        """execute_changes creates new issues in publish mode."""
        mock_create.side_effect = [1, 2]
        new = [Issue(title="First"), Issue(title="Second")]
        results = execute_changes(new, [], [], publish=True, sync=False)
        assert results["created"] == [1, 2]
        assert len(results["failed"]) == 0

    @patch("markdown_to_issues.time.sleep")
    @patch("markdown_to_issues.create_issue")
    def test_execute_tracks_failures(self, mock_create, mock_sleep, capsys):
        """execute_changes tracks failed creates."""
        mock_create.return_value = None
        new = [Issue(title="Fail")]
        results = execute_changes(new, [], [], publish=True, sync=False)
        assert results["failed"] == ["Fail"]

    @patch("markdown_to_issues.time.sleep")
    @patch("markdown_to_issues.close_issue")
    @patch("markdown_to_issues.update_issue")
    @patch("markdown_to_issues.create_issue")
    def test_execute_sync_mode(self, mock_create, mock_update, mock_close, mock_sleep):
        """execute_changes handles sync mode with updates and closes."""
        mock_create.return_value = 1
        mock_update.return_value = True
        mock_close.return_value = True

        new = [Issue(title="New")]
        update = [Issue(title="Update", existing_number=10)]
        close = [Issue(title="Close", existing_number=20, status="done")]

        results = execute_changes(new, update, close, publish=False, sync=True)
        assert results["created"] == [1]
        assert results["updated"] == [10]
        assert results["closed"] == [20]

    @patch("markdown_to_issues.time.sleep")
    @patch("markdown_to_issues.close_issue")
    @patch("markdown_to_issues.update_issue")
    def test_execute_sync_failures(self, mock_update, mock_close, mock_sleep):
        """execute_changes tracks update and close failures."""
        mock_update.return_value = False
        mock_close.return_value = False

        update = [Issue(title="Fail Update", existing_number=10)]
        close = [Issue(title="Fail Close", existing_number=20, status="done")]

        results = execute_changes([], update, close, publish=False, sync=True)
        assert "#10" in results["failed"]
        assert "#20" in results["failed"]

    def test_execute_no_action_without_flags(self):
        """execute_changes does nothing without publish or sync flags."""
        new = [Issue(title="New")]
        results = execute_changes(new, [], [], publish=False, sync=False)
        assert results["created"] == []


class TestPrintResults:
    """Test print_results function."""

    def test_print_results_publish_mode(self, capsys):
        """print_results shows execution summary in publish mode."""
        results = {"created": [1, 2], "updated": [], "closed": [], "failed": []}
        print_results(
            results,
            publish=True,
            sync=False,
            issues=[],
            new=[],
            update=[],
            close=[],
            warning_count=0,
        )
        captured = capsys.readouterr()
        assert "RESULT:" in captured.out
        assert "created=2" in captured.out
        assert "Created: #1 #2" in captured.out

    def test_print_results_parse_mode(self, capsys):
        """print_results shows summary in parse-only mode."""
        results = {"created": [], "updated": [], "closed": [], "failed": []}
        issues = [Issue(title="A"), Issue(title="B")]
        new = [Issue(title="A")]
        print_results(
            results,
            publish=False,
            sync=False,
            issues=issues,
            new=new,
            update=[],
            close=[],
            warning_count=3,
        )
        captured = capsys.readouterr()
        assert "SUMMARY:" in captured.out
        assert "total=2" in captured.out
        assert "new=1" in captured.out
        assert "warnings=3" in captured.out


class TestLogFunction:
    """Test log helper function."""

    def test_log_writes_to_stderr(self, capsys):
        """log writes to stderr."""
        log("Test message")
        captured = capsys.readouterr()
        assert captured.out == ""
        assert "Test message" in captured.err


class TestExportIssuesLabel:
    """Test export_issues with label filter."""

    @patch("markdown_to_issues.gh_list_all")
    def test_export_issues_with_label_filter(self, mock_list_all):
        """export_issues passes label filter to gh_list_all."""
        mock_list_all.return_value = []
        export_issues(label="bug")
        call_args = mock_list_all.call_args[0][0]
        assert "--label" in call_args
        assert "bug" in call_args


class TestMainFunction:
    """Test main() function with various CLI args."""

    @patch("markdown_to_issues.setup_labels")
    def test_main_setup_labels(self, mock_setup, monkeypatch):
        """main --setup-labels calls setup_labels."""
        monkeypatch.setattr("sys.argv", ["prog", "--setup-labels"])
        mock_setup.return_value = {"created": 5, "updated": 2, "failed": 0}
        result = main()
        assert result == 0
        mock_setup.assert_called_once_with(False)

    @patch("markdown_to_issues.setup_labels")
    def test_main_setup_labels_dry_run(self, mock_setup, monkeypatch):
        """main --setup-labels --dry-run passes dry_run=True."""
        monkeypatch.setattr("sys.argv", ["prog", "--setup-labels", "--dry-run"])
        mock_setup.return_value = {"created": 0, "updated": 0, "failed": 0}
        main()
        mock_setup.assert_called_once_with(True)

    @patch("markdown_to_issues.export_issues")
    def test_main_export(self, mock_export, monkeypatch):
        """main --export calls export_issues."""
        monkeypatch.setattr("sys.argv", ["prog", "--export"])
        mock_export.return_value = "# Issues\n"
        result = main()
        assert result == 0
        mock_export.assert_called_once()

    @patch("markdown_to_issues.export_issues")
    def test_main_export_with_state_and_label(self, mock_export, monkeypatch):
        """main --export passes state and label filters."""
        monkeypatch.setattr(
            "sys.argv", ["prog", "--export", "--state", "all", "--label", "bug"]
        )
        mock_export.return_value = "# Issues\n"
        main()
        mock_export.assert_called_once_with("all", "bug")

    def test_main_file_not_found(self, monkeypatch, capsys):
        """main returns 1 for non-existent file."""
        monkeypatch.setattr("sys.argv", ["prog", "nonexistent.md"])
        result = main()
        assert result == 1
        captured = capsys.readouterr()
        assert "File not found" in captured.err

    @patch("markdown_to_issues.validate_issues")
    @patch("markdown_to_issues.Parser")
    def test_main_parse_only(self, mock_parser_cls, mock_validate, monkeypatch, capsys):
        """main parse-only mode shows summary."""
        path = Path("/tmp/test_roadmap.md")
        path.write_text("## Task\n**Labels:** task\n\nDescription.")
        try:
            monkeypatch.setattr("sys.argv", ["prog", str(path)])
            mock_parser = MagicMock()
            mock_parser.parse.return_value = [Issue(title="Task", body="Description")]
            mock_parser.warnings = []
            mock_parser_cls.return_value = mock_parser
            mock_validate.return_value = ValidationResult(
                duplicates={}, bad_labels=[], existing_titles={}
            )
            result = main()
            assert result == 0
            captured = capsys.readouterr()
            assert "SUMMARY:" in captured.out
        finally:
            path.unlink()

    @patch("markdown_to_issues.validate_issues")
    @patch("markdown_to_issues.Parser")
    def test_main_warnings_block_publish(
        self, mock_parser_cls, mock_validate, monkeypatch, capsys
    ):
        """main returns 1 when warnings exist and --publish without --force."""
        path = Path("/tmp/test_roadmap.md")
        path.write_text("## AB\n**Labels:** task\n\nDesc.")
        try:
            monkeypatch.setattr("sys.argv", ["prog", str(path), "--publish"])
            mock_parser = MagicMock()
            mock_parser.parse.return_value = [Issue(title="AB", body="Desc")]
            mock_parser.warnings = ["Title too short"]
            mock_parser_cls.return_value = mock_parser
            mock_validate.return_value = ValidationResult(
                duplicates={}, bad_labels=[], existing_titles={}
            )
            result = main()
            assert result == 1
            captured = capsys.readouterr()
            assert "--force" in captured.err
        finally:
            path.unlink()

    @patch("markdown_to_issues.execute_changes")
    @patch("markdown_to_issues.validate_issues")
    @patch("markdown_to_issues.Parser")
    def test_main_publish_with_force(
        self, mock_parser_cls, mock_validate, mock_execute, monkeypatch, capsys
    ):
        """main --publish --force ignores warnings."""
        path = Path("/tmp/test_roadmap.md")
        path.write_text("## Task\n**Labels:** task\n\nDescription here.")
        try:
            monkeypatch.setattr("sys.argv", ["prog", str(path), "--publish", "--force"])
            mock_parser = MagicMock()
            mock_parser.parse.return_value = [Issue(title="Task", body="Description")]
            mock_parser.warnings = ["Some warning"]
            mock_parser_cls.return_value = mock_parser
            mock_validate.return_value = ValidationResult(
                duplicates={}, bad_labels=[], existing_titles={}
            )
            mock_execute.return_value = {
                "created": [1],
                "updated": [],
                "closed": [],
                "failed": [],
            }
            result = main()
            assert result == 0
        finally:
            path.unlink()

    @patch("markdown_to_issues.print_dry_run")
    @patch("markdown_to_issues.validate_issues")
    @patch("markdown_to_issues.Parser")
    def test_main_dry_run(
        self, mock_parser_cls, mock_validate, mock_print_dry, monkeypatch
    ):
        """main --dry-run calls print_dry_run."""
        path = Path("/tmp/test_roadmap.md")
        path.write_text("## Task\n**Labels:** task\n\nDescription.")
        try:
            monkeypatch.setattr("sys.argv", ["prog", str(path), "--dry-run"])
            mock_parser = MagicMock()
            mock_parser.parse.return_value = [Issue(title="Task", body="Description")]
            mock_parser.warnings = []
            mock_parser_cls.return_value = mock_parser
            mock_validate.return_value = ValidationResult(
                duplicates={}, bad_labels=[], existing_titles={}
            )
            result = main()
            assert result == 0
            mock_print_dry.assert_called_once()
        finally:
            path.unlink()

    @patch("markdown_to_issues.execute_changes")
    @patch("markdown_to_issues.validate_issues")
    @patch("markdown_to_issues.Parser")
    def test_main_returns_1_on_failures(
        self, mock_parser_cls, mock_validate, mock_execute, monkeypatch
    ):
        """main returns 1 when there are failed operations."""
        path = Path("/tmp/test_roadmap.md")
        path.write_text("## Task\n**Labels:** task\n\nDescription.")
        try:
            monkeypatch.setattr("sys.argv", ["prog", str(path), "--publish"])
            mock_parser = MagicMock()
            mock_parser.parse.return_value = [Issue(title="Task", body="Description")]
            mock_parser.warnings = []
            mock_parser_cls.return_value = mock_parser
            mock_validate.return_value = ValidationResult(
                duplicates={}, bad_labels=[], existing_titles={}
            )
            mock_execute.return_value = {
                "created": [],
                "updated": [],
                "closed": [],
                "failed": ["Task"],
            }
            result = main()
            assert result == 1
        finally:
            path.unlink()
