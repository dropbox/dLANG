# Roadmap: <Project Name>

> After writing and reviewing, run `./markdown_to_issues.py ROADMAP.md` to parse.
> This file stays in the repo as a record of the original roadmap.

---

## <Issue title - clear, actionable>
**Labels:** task
**Priority:** P0

<What needs to be done. Be specific.>

<Why this matters. Context and motivation.>

<Acceptance criteria: how do we know this is done?>

---

## <Second task>
**Labels:** task
**Priority:** P1

<Description>

---

## <Third task>
**Labels:** task, enhancement
**Priority:** P2

<Description>

---

<!--
FIELD REFERENCE:
  **Labels:** task, bug, enhancement, P0-P3 (comma-separated)
  **Priority:** P0, P1, P2, P3 (adds to labels automatically)
  **Milestone:** v1.0 (optional - milestone must exist in GitHub)
  **Depends:** #42 (optional - use when ADDING to existing issues, not for initial roadmap)

WORKFLOW:
  1. Write roadmap, review 2+ passes, git commit
  2. ./markdown_to_issues.py ROADMAP.md (parse and review draft)
  3. Fix any warnings, re-run parser
  4. ./markdown_to_issues.py ROADMAP.md --publish

WHEN TO RE-RUN THIS WORKFLOW:
  - When all current roadmap items are complete
  - When directed by manager
  - After major scope/direction changes
  - When many ad-hoc requests need consolidation
-->
