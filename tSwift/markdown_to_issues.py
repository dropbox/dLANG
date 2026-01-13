#!/usr/bin/env python3
"""
markdown_to_issues.py - Sync Markdown ↔ GitHub Issues
=====================================================

COMMANDS
────────
  --export, --current Issues → markdown (stdout)
  --setup-labels      Create P0-P3, task, bug labels
  ROADMAP.md          Parse and validate (default)
  --publish           Create new issues
  --sync              Create + update + close all

MODIFIERS
─────────
  --dry-run           Preview without executing
  --force             Ignore warnings
  --state all         Include closed (--export)
  --label LABEL       Filter (--export)

MARKDOWN FORMAT
───────────────
  ## Task title                     → New issue
  ## #42: Task title                → Update #42
  ## [DONE] Task title              → Close (--sync)

  Labels: task, bug
  Priority: P0
  Assignee: @user
  <!-- comments stripped -->

EXAMPLES
────────
  ./markdown_to_issues.py --export > issues.md
  ./markdown_to_issues.py ROADMAP.md --publish
  ./markdown_to_issues.py ROADMAP.md --sync
"""

import argparse
import json
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional

# Rate limit delay between API calls (seconds)
RATE_LIMIT_DELAY = 0.3

# Valid priority labels
PRIORITIES = ('P0', 'P1', 'P2', 'P3')

# Standard labels
STANDARD_LABELS = [
    {"name": "P0", "description": "Critical", "color": "B60205"},
    {"name": "P1", "description": "High priority", "color": "D93F0B"},
    {"name": "P2", "description": "Medium priority", "color": "FBCA04"},
    {"name": "P3", "description": "Low priority", "color": "0E8A16"},
    {"name": "task", "description": "Work item", "color": "1D76DB"},
    {"name": "bug", "description": "Something broken", "color": "B60205"},
    {"name": "enhancement", "description": "Improvement", "color": "A2EEEF"},
    {"name": "in-progress", "description": "Being worked on", "color": "FBCA04"},
    {"name": "blocked", "description": "Waiting", "color": "D93F0B"},
]


def log(msg: str) -> None:
    """Log to stderr (doesn't pollute stdout data)."""
    print(msg, file=sys.stderr)


def gh(args: list[str]) -> subprocess.CompletedProcess:
    """Run gh command."""
    return subprocess.run(["gh"] + args, check=False, capture_output=True, text=True)


def gh_json(args: list[str], default: str = "[]") -> str:
    """Run gh command expecting JSON output. Log errors, return default on failure."""
    result = gh(args)
    if result.returncode != 0:
        log(f"gh {' '.join(args[:2])} failed: {result.stderr.strip() or 'unknown error'}")
        return default
    return result.stdout or default


@dataclass
class Issue:
    title: str
    labels: list[str] = field(default_factory=lambda: ["task"])
    priority: Optional[str] = None
    milestone: Optional[str] = None
    assignee: Optional[str] = None
    depends: Optional[str] = None
    body: str = ""
    line_num: int = 0
    existing_number: Optional[int] = None  # #42: means update
    status: Optional[str] = None  # done = close

    def labels_str(self) -> str:
        extra = [self.priority] if self.priority and self.priority not in self.labels else []
        return ",".join(self.labels + extra)

    def full_body(self) -> str:
        body = self.body.strip()
        if self.depends:
            body += f"\n\n**Depends on:** {self.depends}"
        return body


class Parser:
    """Parse markdown into Issues."""

    FIELDS = {
        'labels': re.compile(r'^[-*]?\s*(?:\*\*)?Labels:\*?\*?\s*(.+)$', re.IGNORECASE),
        'priority': re.compile(r'^[-*]?\s*(?:\*\*)?Priority:\*?\*?\s*(.+)$', re.IGNORECASE),
        'milestone': re.compile(r'^[-*]?\s*(?:\*\*)?Milestone:\*?\*?\s*(.+)$', re.IGNORECASE),
        'assignee': re.compile(r'^[-*]?\s*(?:\*\*)?Assignee?s?:\*?\*?\s*(.+)$', re.IGNORECASE),
        'depends': re.compile(r'^[-*]?\s*(?:\*\*)?Depends(?:\s+on)?:\*?\*?\s*(.+)$', re.IGNORECASE),
        'status': re.compile(r'^[-*]?\s*(?:\*\*)?Status:\*?\*?\s*(.+)$', re.IGNORECASE),
    }

    def __init__(self, path: Path):
        self.path = path
        self.issues: list[Issue] = []
        self.warnings: list[str] = []

    def parse(self) -> list[Issue]:
        content = self.path.read_text()
        content = re.sub(r'<!--.*?-->', '', content, flags=re.DOTALL)  # Strip comments

        current: Optional[Issue] = None
        body_lines: list[str] = []

        for num, line in enumerate(content.split('\n'), 1):
            if line.startswith('## '):
                if current:
                    current.body = '\n'.join(body_lines).strip()
                    self._validate(current)
                    self.issues.append(current)

                title, existing, status = self._parse_title(line[3:].strip())
                current = Issue(title=title, line_num=num, existing_number=existing, status=status)
                body_lines = []
                continue

            if not current or line.startswith(('# ', '>')) or line.strip() == '---':
                continue

            # Check fields
            for name, pattern in self.FIELDS.items():
                if m := pattern.match(line):
                    val = m.group(1).strip()
                    if name == 'labels':
                        current.labels = [lbl.strip() for lbl in val.split(',') if lbl.strip()]
                    elif name == 'priority':
                        current.priority = val.upper()
                    elif name == 'assignee':
                        current.assignee = val.lstrip('@')
                    elif name == 'status':
                        current.status = 'done' if val.lower() in ('done', 'closed', 'complete') else val.lower()
                    else:  # milestone, depends
                        setattr(current, name, val)
                    break
            else:
                body_lines.append(line)

        if current:
            current.body = '\n'.join(body_lines).strip()
            self._validate(current)
            self.issues.append(current)

        return self.issues

    def _parse_title(self, raw: str) -> tuple[str, Optional[int], Optional[str]]:
        """Extract issue number and status from title."""
        status = None
        existing = None

        # [DONE], [CLOSED], [WIP], [IN-PROGRESS] markers
        m = re.match(r'^\[(DONE|CLOSED|WIP|IN-PROGRESS)\]\s*', raw, re.IGNORECASE)
        if m:
            marker = m.group(1).upper()
            status = 'done' if marker in ('DONE', 'CLOSED') else 'wip'
            raw = raw[m.end():]

        # #42: prefix
        m = re.match(r'^#(\d+):?\s*', raw)
        if m:
            existing = int(m.group(1))
            raw = raw[m.end():]

        # Status after number
        m = re.match(r'^\[(DONE|CLOSED|WIP|IN-PROGRESS)\]\s*', raw, re.IGNORECASE)
        if m:
            marker = m.group(1).upper()
            status = 'done' if marker in ('DONE', 'CLOSED') else 'wip'
            raw = raw[m.end():]

        return raw.strip(), existing, status

    def _validate(self, issue: Issue) -> None:
        if len(issue.title) < 3:
            self.warnings.append(f"Line {issue.line_num}: Title too short")
        if len(issue.body.strip()) < 5:
            self.warnings.append(f"Line {issue.line_num}: Body too short for '{issue.title}'")
        if issue.priority and issue.priority not in PRIORITIES:
            self.warnings.append(f"Line {issue.line_num}: Invalid priority '{issue.priority}'")


def setup_labels(dry_run: bool = False) -> dict:
    """Create standard labels."""
    results = {"created": 0, "updated": 0, "failed": 0}
    existing = {lbl["name"] for lbl in json.loads(gh_json(["label", "list", "--json", "name"]))}

    for label in STANDARD_LABELS:
        if dry_run:
            log(f"Would create: {label['name']}")
            continue

        result = gh(["label", "create", label["name"],
                     "--description", label["description"],
                     "--color", label["color"], "--force"])

        if result.returncode == 0:
            if label["name"] in existing:
                results["updated"] += 1
            else:
                results["created"] += 1
                log(f"Created: {label['name']}")
        else:
            results["failed"] += 1
            log(f"Failed: {label['name']}")

    return results


def priority_sort_key(issue: dict) -> int:
    """Sort key: P0=0, P1=1, P2=2, P3=3, no priority=99."""
    labels = {lbl['name'] for lbl in issue.get('labels', [])}
    for idx, priority in enumerate(PRIORITIES):
        if priority in labels:
            return idx
    return 99


def export_issues(state: str = "open", label: Optional[str] = None) -> str:
    """Export issues to markdown."""
    cmd = ["issue", "list", "--state", state, "--limit", "200",
           "--json", "number,title,body,labels,milestone,assignees,state"]
    if label:
        cmd.extend(["--label", label])

    result = gh(cmd)
    if result.returncode != 0:
        return ""

    issues = json.loads(result.stdout)
    lines = [f"# Issues ({state})", f"> Exported: {datetime.now():%Y-%m-%d %H:%M}", ""]

    for issue in sorted(issues, key=priority_sort_key):

        num, title = issue["number"], issue["title"]
        state_mark = "[CLOSED] " if issue.get("state", "").upper() == "CLOSED" else ""
        labels = [lbl["name"] for lbl in issue.get("labels", [])]
        priority = next((lbl for lbl in labels if lbl in PRIORITIES), None)
        other = [lbl for lbl in labels if lbl not in PRIORITIES]

        lines.append(f"## #{num}: {state_mark}{title}")
        if other:
            lines.append(f"Labels: {', '.join(other)}")
        if priority:
            lines.append(f"Priority: {priority}")
        lines.append("")
        lines.append(issue.get("body", "") or "*(no description)*")
        lines.append("\n---\n")

    return "\n".join(lines)


def create_issue(issue: Issue) -> Optional[int]:
    """Create issue, return number."""
    cmd = ["issue", "create", "--title", issue.title,
           "--label", issue.labels_str(), "--body", issue.full_body()]
    if issue.milestone:
        cmd.extend(["--milestone", issue.milestone])
    if issue.assignee:
        cmd.extend(["--assignee", issue.assignee])

    result = gh(cmd)
    if result.returncode != 0:
        log(f"Failed to create: {issue.title}")
        return None

    m = re.search(r'/issues/(\d+)', result.stdout)
    return int(m.group(1)) if m else None


def update_issue(num: int, issue: Issue) -> bool:
    """Update existing issue."""
    cmd = ["issue", "edit", str(num),
           "--title", issue.title, "--body", issue.full_body()]
    # Sync labels by removing all and re-adding
    cmd.extend(["--add-label", issue.labels_str()])
    if issue.milestone:
        cmd.extend(["--milestone", issue.milestone])
    if issue.assignee:
        cmd.extend(["--assignee", issue.assignee])
    result = gh(cmd)
    return result.returncode == 0


def close_issue(num: int) -> bool:
    """Close issue."""
    return gh(["issue", "close", str(num)]).returncode == 0


def main():
    p = argparse.ArgumentParser(description="Sync Markdown ↔ GitHub Issues")
    p.add_argument("roadmap", nargs="?", default="ROADMAP.md")
    p.add_argument("--export", "--current", action="store_true", help="Export issues to markdown")
    p.add_argument("--setup-labels", action="store_true", help="Create standard labels")
    p.add_argument("--publish", action="store_true", help="Create issues")
    p.add_argument("--sync", action="store_true", help="Create + update + close")
    p.add_argument("--dry-run", action="store_true", help="Preview only")
    p.add_argument("--force", action="store_true", help="Ignore warnings")
    p.add_argument("--state", default="open", choices=["open", "closed", "all"])
    p.add_argument("--label", help="Filter by label")
    args = p.parse_args()

    # --setup-labels
    if args.setup_labels:
        results = setup_labels(args.dry_run)
        print(f"RESULT: created={results['created']} updated={results['updated']} failed={results['failed']}")
        return 0

    # --export
    if args.export:
        md = export_issues(args.state, args.label)
        print(md)
        return 0

    # Parse roadmap
    path = Path(args.roadmap)
    if not path.exists():
        log(f"File not found: {args.roadmap}")
        return 1

    parser = Parser(path)
    issues = parser.parse()

    new, update, close = [], [], []
    for i in issues:
        if not i.existing_number:
            new.append(i)
        elif i.status == 'done':
            close.append(i)
        else:
            update.append(i)

    # Check duplicates
    existing = {i["title"].lower(): i["number"]
                for i in json.loads(gh_json(["issue", "list", "--state", "all",
                                             "--limit", "200", "--json", "number,title"]))}
    dupes = {i.title: existing[i.title.lower()] for i in new if i.title.lower() in existing}

    # Validate labels
    repo_labels = {lbl["name"] for lbl in json.loads(gh_json(["label", "list", "--json", "name"]))}
    bad_labels = [(i.title, lbl) for i in issues for lbl in i.labels + ([i.priority] if i.priority else [])
                  if lbl and lbl not in repo_labels]

    # Warnings
    for w in parser.warnings:
        log(f"WARNING: {w}")
    for title, num in dupes.items():
        log(f"WARNING: '{title}' duplicates #{num}")
    for title, label in bad_labels:
        log(f"WARNING: Unknown label '{label}' in '{title}'")

    if (parser.warnings or dupes or bad_labels) and not args.force and (args.publish or args.sync):
        log("Use --force to ignore warnings")
        return 1

    # Dry run
    if args.dry_run:
        for i in new:
            print(f"gh issue create --title \"{i.title}\"")
        if args.sync:
            for i in update:
                print(f"gh issue edit {i.existing_number}")
            for i in close:
                print(f"gh issue close {i.existing_number}")
        return 0

    # Execute
    results = {"created": [], "updated": [], "closed": [], "failed": []}

    if args.publish or args.sync:
        for i in new:
            num = create_issue(i)
            if num:
                log(f"Created #{num}: {i.title}")
                results["created"].append(num)
            else:
                results["failed"].append(i.title)
            time.sleep(RATE_LIMIT_DELAY)

    if args.sync:
        for i in update:
            if update_issue(i.existing_number, i):
                log(f"Updated #{i.existing_number}")
                results["updated"].append(i.existing_number)
            else:
                results["failed"].append(f"#{i.existing_number}")
            time.sleep(RATE_LIMIT_DELAY)

        for i in close:
            if close_issue(i.existing_number):
                log(f"Closed #{i.existing_number}")
                results["closed"].append(i.existing_number)
            else:
                results["failed"].append(f"#{i.existing_number}")
            time.sleep(RATE_LIMIT_DELAY)

    # Summary
    if args.publish or args.sync:
        print(f"RESULT: created={len(results['created'])} updated={len(results['updated'])} "
              f"closed={len(results['closed'])} failed={len(results['failed'])}")
        if results["created"]:
            print(f"Created: {' '.join(f'#{n}' for n in results['created'])}")

    if not (args.publish or args.sync):
        print(f"SUMMARY: total={len(issues)} new={len(new)} update={len(update)} close={len(close)} "
              f"warnings={len(parser.warnings) + len(dupes) + len(bad_labels)}")

    return 1 if results["failed"] else 0


if __name__ == "__main__":
    sys.exit(main())
