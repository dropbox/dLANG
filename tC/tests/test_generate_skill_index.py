"""Tests for generate_skill_index.py skill documentation generator."""

import os
import sys
from pathlib import Path
from unittest.mock import patch

# Add ai_template_scripts to path
sys.path.insert(0, str(Path(__file__).parent.parent / "ai_template_scripts"))

import generate_skill_index


class TestParseSkillFile:
    """Test parse_skill_file function."""

    def test_parses_basic_skill(self, tmp_path: Path):
        skill_file = tmp_path / "test.md"
        skill_file.write_text("""# Test Skill

This is the description.

## You Might Say

- do the thing
- run test

## Execute

Some instructions.
""")
        result = generate_skill_index.parse_skill_file(skill_file)
        assert result is not None
        assert result["name"] == "Test Skill"
        assert result["description"] == "This is the description."
        assert result["filename"] == "test"
        assert result["triggers"] == ["do the thing", "run test"]

    def test_returns_none_without_header(self, tmp_path: Path):
        skill_file = tmp_path / "invalid.md"
        skill_file.write_text("No header here\nJust text")
        result = generate_skill_index.parse_skill_file(skill_file)
        assert result is None

    def test_handles_missing_triggers(self, tmp_path: Path):
        skill_file = tmp_path / "simple.md"
        skill_file.write_text("""# Simple Skill

Description line.
""")
        result = generate_skill_index.parse_skill_file(skill_file)
        assert result is not None
        assert result["triggers"] == []

    def test_skips_example_lines(self, tmp_path: Path):
        skill_file = tmp_path / "skip.md"
        skill_file.write_text("""# Skill With Example

Example: something
Real description here.
""")
        result = generate_skill_index.parse_skill_file(skill_file)
        assert result is not None
        assert result["description"] == "Real description here."

    def test_skips_provide_lines(self, tmp_path: Path):
        skill_file = tmp_path / "provide.md"
        skill_file.write_text("""# Skill With Provide

Provide: argument
The actual description.
""")
        result = generate_skill_index.parse_skill_file(skill_file)
        assert result is not None
        assert result["description"] == "The actual description."

    def test_strips_trigger_quotes(self, tmp_path: Path):
        skill_file = tmp_path / "quotes.md"
        skill_file.write_text("""# Quoted Triggers

Desc.

## You Might Say

- "quoted trigger"
- 'single quoted'
- unquoted
""")
        result = generate_skill_index.parse_skill_file(skill_file)
        assert result is not None
        assert result["triggers"] == ["quoted trigger", "single quoted", "unquoted"]

    def test_stops_triggers_at_next_section(self, tmp_path: Path):
        skill_file = tmp_path / "sections.md"
        skill_file.write_text("""# Section Test

Desc.

## You Might Say

- trigger one

## Execute

- not a trigger
""")
        result = generate_skill_index.parse_skill_file(skill_file)
        assert result is not None
        assert result["triggers"] == ["trigger one"]


class TestCategorizeSkills:
    """Test categorize_skills function."""

    def test_workflow_skills(self):
        skills = [
            {"filename": "w-start", "name": "Start"},
            {"filename": "w-commit", "name": "Commit"},
            {"filename": "handoff", "name": "Handoff"},
        ]
        result = generate_skill_index.categorize_skills(skills)
        assert len(result["Session Workflow"]) == 3
        assert len(result["Task Lifecycle"]) == 0

    def test_lifecycle_skills(self):
        skills = [
            {"filename": "claim", "name": "Claim"},
            {"filename": "complete", "name": "Complete"},
            {"filename": "blocked", "name": "Blocked"},
            {"filename": "verify", "name": "Verify"},
        ]
        result = generate_skill_index.categorize_skills(skills)
        assert len(result["Task Lifecycle"]) == 4

    def test_communication_skills(self):
        skills = [
            {"filename": "crossmsg", "name": "Cross Message"},
            {"filename": "news", "name": "News"},
            {"filename": "news-post", "name": "News Post"},
            {"filename": "mail", "name": "Mail"},
            {"filename": "vote", "name": "Vote"},
        ]
        result = generate_skill_index.categorize_skills(skills)
        assert len(result["Communication"]) == 5

    def test_manager_skills(self):
        skills = [
            {"filename": "m-cycle", "name": "Cycle"},
            {"filename": "directive", "name": "Directive"},
            {"filename": "m-workers", "name": "Workers"},
            {"filename": "m-status", "name": "Status"},
            {"filename": "blockers", "name": "Blockers"},
        ]
        result = generate_skill_index.categorize_skills(skills)
        assert len(result["MANAGER Tools"]) == 5

    def test_utility_skills_default(self):
        skills = [
            {"filename": "debug", "name": "Debug"},
            {"filename": "optimize", "name": "Optimize"},
        ]
        result = generate_skill_index.categorize_skills(skills)
        assert len(result["Utilities"]) == 2

    def test_mixed_skills(self):
        skills = [
            {"filename": "w-start", "name": "Start"},
            {"filename": "claim", "name": "Claim"},
            {"filename": "debug", "name": "Debug"},
        ]
        result = generate_skill_index.categorize_skills(skills)
        assert len(result["Session Workflow"]) == 1
        assert len(result["Task Lifecycle"]) == 1
        assert len(result["Utilities"]) == 1


class TestGenerateSkillsMd:
    """Test generate_skills_md function."""

    def test_generates_header(self):
        categories = {
            "Session Workflow": [],
            "Task Lifecycle": [],
            "Communication": [],
            "MANAGER Tools": [],
            "Utilities": [],
        }
        result = generate_skill_index.generate_skills_md(categories)
        assert "# Skill Index" in result
        assert "Auto-generated" in result

    def test_generates_quick_reference_table(self):
        categories = {
            "Session Workflow": [],
            "Task Lifecycle": [],
            "Communication": [],
            "MANAGER Tools": [],
            "Utilities": [
                {
                    "filename": "debug",
                    "name": "Debug",
                    "description": "Debug things",
                    "triggers": [],
                }
            ],
        }
        result = generate_skill_index.generate_skills_md(categories)
        assert "## Quick Reference" in result
        assert "| Skill | Description |" in result
        assert "| `/debug` | Debug things |" in result

    def test_truncates_long_descriptions(self):
        categories = {
            "Session Workflow": [],
            "Task Lifecycle": [],
            "Communication": [],
            "MANAGER Tools": [],
            "Utilities": [
                {
                    "filename": "long",
                    "name": "Long",
                    "description": "A" * 100,
                    "triggers": [],
                }
            ],
        }
        result = generate_skill_index.generate_skills_md(categories)
        # Should have 60 chars + "..."
        assert "A" * 60 + "..." in result

    def test_generates_category_sections(self):
        categories = {
            "Session Workflow": [
                {
                    "filename": "w-start",
                    "name": "Start",
                    "description": "Start session",
                    "triggers": ["begin"],
                }
            ],
            "Task Lifecycle": [],
            "Communication": [],
            "MANAGER Tools": [],
            "Utilities": [],
        }
        result = generate_skill_index.generate_skills_md(categories)
        assert "## Session Workflow" in result
        assert "### `/w-start` - Start" in result
        assert "Start session" in result

    def test_includes_triggers(self):
        categories = {
            "Session Workflow": [],
            "Task Lifecycle": [],
            "Communication": [],
            "MANAGER Tools": [],
            "Utilities": [
                {
                    "filename": "test",
                    "name": "Test",
                    "description": "Test skill",
                    "triggers": ["do it", "run it", "try it"],
                }
            ],
        }
        result = generate_skill_index.generate_skills_md(categories)
        assert "**You might say:**" in result
        assert "- do it" in result
        assert "- run it" in result
        assert "- try it" in result

    def test_limits_triggers_to_three(self):
        categories = {
            "Session Workflow": [],
            "Task Lifecycle": [],
            "Communication": [],
            "MANAGER Tools": [],
            "Utilities": [
                {
                    "filename": "many",
                    "name": "Many",
                    "description": "Many triggers",
                    "triggers": ["one", "two", "three", "four", "five"],
                }
            ],
        }
        result = generate_skill_index.generate_skills_md(categories)
        assert "- one" in result
        assert "- two" in result
        assert "- three" in result
        assert "- four" not in result
        assert "- five" not in result

    def test_skips_empty_categories(self):
        categories = {
            "Session Workflow": [],
            "Task Lifecycle": [],
            "Communication": [],
            "MANAGER Tools": [],
            "Utilities": [],
        }
        result = generate_skill_index.generate_skills_md(categories)
        assert "## Session Workflow" not in result
        assert "## Task Lifecycle" not in result

    def test_includes_footer(self):
        categories = {
            "Session Workflow": [],
            "Task Lifecycle": [],
            "Communication": [],
            "MANAGER Tools": [],
            "Utilities": [],
        }
        result = generate_skill_index.generate_skills_md(categories)
        assert "*Generated by" in result
        assert "generate_skill_index.py" in result

    def test_sorts_skills_by_filename(self):
        categories = {
            "Session Workflow": [],
            "Task Lifecycle": [],
            "Communication": [],
            "MANAGER Tools": [],
            "Utilities": [
                {"filename": "z-last", "name": "Z", "description": "Z", "triggers": []},
                {
                    "filename": "a-first",
                    "name": "A",
                    "description": "A",
                    "triggers": [],
                },
                {
                    "filename": "m-middle",
                    "name": "M",
                    "description": "M",
                    "triggers": [],
                },
            ],
        }
        result = generate_skill_index.generate_skills_md(categories)
        # Check order in the table - a-first should come before m-middle before z-last
        a_pos = result.find("/a-first")
        m_pos = result.find("/m-middle")
        z_pos = result.find("/z-last")
        assert a_pos < m_pos < z_pos


class TestMain:
    """Test main function."""

    def test_returns_error_without_commands_dir(self, tmp_path: Path, capsys):
        with patch.object(generate_skill_index, "Path") as mock_path:
            mock_commands = mock_path.return_value
            mock_commands.exists.return_value = False
            result = generate_skill_index.main()
        assert result == 1
        captured = capsys.readouterr()
        assert "not found" in captured.out

    def test_returns_error_without_skills(self, tmp_path: Path, capsys):
        commands_dir = tmp_path / ".claude" / "commands"
        commands_dir.mkdir(parents=True)

        # Create an invalid skill file
        (commands_dir / "invalid.md").write_text("no header")

        orig_dir = os.getcwd()
        os.chdir(tmp_path)
        try:
            result = generate_skill_index.main()
        finally:
            os.chdir(orig_dir)

        assert result == 1
        captured = capsys.readouterr()
        assert "No skills found" in captured.out

    def test_generates_output_file(self, tmp_path: Path, capsys):
        commands_dir = tmp_path / ".claude" / "commands"
        commands_dir.mkdir(parents=True)

        (commands_dir / "test.md").write_text("""# Test Skill

Description here.
""")

        orig_dir = os.getcwd()
        os.chdir(tmp_path)
        try:
            result = generate_skill_index.main()
        finally:
            os.chdir(orig_dir)

        assert result == 0
        output = (tmp_path / ".claude" / "SKILLS.md").read_text()
        assert "# Skill Index" in output
        assert "/test" in output
        captured = capsys.readouterr()
        assert "Generated:" in captured.out

    def test_counts_skills(self, tmp_path: Path, capsys):
        commands_dir = tmp_path / ".claude" / "commands"
        commands_dir.mkdir(parents=True)

        for i in range(3):
            (commands_dir / f"skill{i}.md").write_text(f"""# Skill {i}

Desc {i}.
""")

        orig_dir = os.getcwd()
        os.chdir(tmp_path)
        try:
            generate_skill_index.main()
        finally:
            os.chdir(orig_dir)

        captured = capsys.readouterr()
        assert "Found 3 skills" in captured.out
