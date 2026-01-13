# Roadmap: ai_template

> Create issues with `gh issue create`. This file stays in the repo as a record of the roadmap.

<!--
Roadmap Status: COMPLETE (all items implemented as of 2026-01-08)
- Test coverage for Python scripts: #40 CLOSED (tests exist in tests/)
- Test coverage for MCP plugins: #41 CLOSED (tests exist in tests/)
- Two-layer bot identity: Epic #53 CLOSED (implemented in run_loop.py, documented in rules)
- Onboarding documentation: #42 CLOSED (quick-reference.md exists)

See closed issues #37-#60 for full implementation history.
-->

## Test coverage for Python scripts
**Labels:** task, testing
**Priority:** P1

Issue #19 "No test harness for skills/plugins" was closed but only template tests exist. The Python scripts (`json_to_text.py`, `code_stats.py`) have no test coverage.

**What:** Write pytest tests for core scripts:
- `json_to_text.py` - JSON to text conversion, edge cases
- `code_stats.py` - basic functionality

**Why:** Recent closed issues (#20, #34) were bugs in these scripts. Tests prevent regressions and catch edge cases.

**Acceptance criteria:**
- Each script has corresponding test file in `tests/`
- Tests cover happy path and common error cases
- `pytest tests/` passes with >80% coverage on scripts

---

## Test coverage for MCP plugins
**Labels:** task, testing
**Priority:** P2

The MCP plugins (`ai-fleet`, `tab-title`) have no test coverage. These are critical infrastructure used by all WORKER/MANAGER sessions.

**What:** Write tests for MCP plugin functionality:
- ai-fleet: claim_issue, complete_issue, block_issue, get_iteration
- tab-title: set_title, get_role, get_project

**Why:** Bugs in MCP tools can break entire WORKER loops. Tests ensure reliability.

**Acceptance criteria:**
- Test files exist for each plugin
- Core functions have unit tests
- Can run tests without live GitHub API (mock where necessary, document mocks)

---

## Onboarding documentation simplification
**Labels:** task, documentation
**Priority:** P2

The rules files (`.claude/rules/ai_template.md`, `.claude/rules/fleet-context.md`) are comprehensive but long. New AIs spend context reading rules instead of working.

**What:** Create condensed quick-reference:
- Extract most critical rules into 1-page summary
- Keep full rules for edge cases
- Add "first 5 things to know" section

**Why:** Faster onboarding = more productive iterations. Most sessions need 20% of the rules.

**Acceptance criteria:**
- Quick-reference exists (< 50 lines)
- Full rules still available
- WORKER can start productive work faster

---

