"""Tests for skill document structure consistency.

Ensures all skill files in .claude/commands/ have required sections.
"""

import re
from pathlib import Path

import pytest

COMMANDS_DIR = Path(__file__).parent.parent / ".claude" / "commands"
REQUIRED_SECTIONS = ["## Execute", "## Report"]
EXAMPLE_LINE_PATTERN = r"^Example:\s+`/.+`$"


def get_skill_files() -> list[Path]:
    """Get all markdown files in the commands directory."""
    if not COMMANDS_DIR.exists():
        return []
    return sorted(COMMANDS_DIR.glob("*.md"))


def get_skill_ids() -> list[str]:
    """Get skill IDs for parameterized tests."""
    return [f.stem for f in get_skill_files()]


class TestSkillStructure:
    """Test that all skills have required structure."""

    @pytest.mark.parametrize("skill_id", get_skill_ids())
    def test_skill_has_h1_header(self, skill_id: str):
        """Every skill must start with an H1 header."""
        skill_file = COMMANDS_DIR / f"{skill_id}.md"
        content = skill_file.read_text()
        lines = content.strip().split("\n")
        assert lines, f"{skill_id}.md is empty"
        assert lines[0].startswith("# "), f"{skill_id}.md must start with H1 header"

    @pytest.mark.parametrize("skill_id", get_skill_ids())
    def test_skill_has_execute_section(self, skill_id: str):
        """Every skill must have an Execute section."""
        skill_file = COMMANDS_DIR / f"{skill_id}.md"
        content = skill_file.read_text()
        assert "## Execute" in content, f"{skill_id}.md missing '## Execute' section"

    @pytest.mark.parametrize("skill_id", get_skill_ids())
    def test_skill_has_report_section(self, skill_id: str):
        """Every skill must have a Report section."""
        skill_file = COMMANDS_DIR / f"{skill_id}.md"
        content = skill_file.read_text()
        assert "## Report" in content, f"{skill_id}.md missing '## Report' section"

    @pytest.mark.parametrize("skill_id", get_skill_ids())
    def test_skill_has_example_line(self, skill_id: str):
        """Every skill must have an Example line showing usage."""
        skill_file = COMMANDS_DIR / f"{skill_id}.md"
        content = skill_file.read_text()
        lines = content.strip().split("\n")

        # Example line should be within first 10 lines, after header and description
        example_found = False
        for line in lines[:10]:
            if re.match(EXAMPLE_LINE_PATTERN, line.strip()):
                example_found = True
                break

        assert example_found, (
            f"{skill_id}.md missing 'Example: `/skill-name`' line near top"
        )

    @pytest.mark.parametrize("skill_id", get_skill_ids())
    def test_skill_has_description(self, skill_id: str):
        """Every skill must have a description after the header."""
        skill_file = COMMANDS_DIR / f"{skill_id}.md"
        content = skill_file.read_text()
        lines = content.strip().split("\n")

        # Find first non-empty line after header
        desc_line = None
        for line in lines[1:]:
            stripped = line.strip()
            if stripped and not stripped.startswith("#"):
                desc_line = stripped
                break

        assert desc_line, f"{skill_id}.md has no description after header"
        # Description should not be a section marker or code block
        assert not desc_line.startswith("```"), (
            f"{skill_id}.md description is a code block"
        )


class TestSkillCount:
    """Test that we have a reasonable number of skills."""

    def test_minimum_skills_exist(self):
        """Ensure we have at least the core skills."""
        skills = get_skill_files()
        # We expect at least 25 skills based on the template
        assert len(skills) >= 25, f"Expected 25+ skills, found {len(skills)}"

    def test_core_skills_exist(self):
        """Ensure core workflow skills exist."""
        core_skills = [
            "w-start",
            "w-commit",
            "claim",
            "complete",
            "blocked",
            "verify",
            "handoff",
        ]
        existing = {f.stem for f in get_skill_files()}
        missing = [s for s in core_skills if s not in existing]
        assert not missing, f"Missing core skills: {missing}"


class TestAllSkills:
    """Aggregate tests for all skills."""

    def test_all_skills_have_required_sections(self):
        """Summary test: all skills have all required sections."""
        missing = {}
        for skill_file in get_skill_files():
            content = skill_file.read_text()
            skill_missing = [s for s in REQUIRED_SECTIONS if s not in content]
            if skill_missing:
                missing[skill_file.stem] = skill_missing

        if missing:
            report = "\n".join(
                f"  {skill}: {sections}" for skill, sections in missing.items()
            )
            pytest.fail(f"Skills missing required sections:\n{report}")
