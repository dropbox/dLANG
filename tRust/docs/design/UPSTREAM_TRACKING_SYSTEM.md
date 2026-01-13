# tRust Upstream Tracking System Design

## Problem Statement

tRust is a fork of rustc. To be a "real compiler," it must compile all valid Rust code, which requires staying current with upstream rustc. Manual, ad-hoc syncing is error-prone and leads to version lag.

## Requirements

### Functional Requirements

1. **Automatic Detection**: Know when new Rust versions are released within 24 hours
2. **Impact Analysis**: Identify which upstream changes affect tRust integration points
3. **Automated Sync**: Perform rebases with minimal human intervention
4. **Validation**: Comprehensive testing to ensure sync didn't break verification
5. **Reporting**: Clear status of sync state, history, and any issues
6. **Alerting**: Notify when tRust falls behind acceptable threshold

### Non-Functional Requirements

1. **Reliability**: System must work unattended
2. **Recoverability**: Easy rollback if sync fails
3. **Auditability**: Full history of all syncs and their outcomes
4. **Minimal Overhead**: Don't slow down normal development

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                        tRust Upstream Tracking System                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐              │
│  │   Release    │───▶│   Impact     │───▶│    Sync      │              │
│  │   Monitor    │    │   Analyzer   │    │   Pipeline   │              │
│  └──────────────┘    └──────────────┘    └──────────────┘              │
│         │                   │                   │                       │
│         ▼                   ▼                   ▼                       │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐              │
│  │   Release    │    │   Change     │    │    Sync      │              │
│  │   Database   │    │   Database   │    │   History    │              │
│  └──────────────┘    └──────────────┘    └──────────────┘              │
│                                                                          │
│  ┌──────────────────────────────────────────────────────────────────┐  │
│  │                      Worker Integration                           │  │
│  │  - Startup check: Is tRust current?                              │  │
│  │  - Blocking: If >1 release behind, sync before other work        │  │
│  │  - Reporting: Show sync status in worker logs                    │  │
│  └──────────────────────────────────────────────────────────────────┘  │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

## Components

### 1. Release Monitor (`trust-release-monitor`)

**Purpose**: Detect new Rust releases and track their metadata.

**Data Sources**:
- GitHub Releases API: `https://api.github.com/repos/rust-lang/rust/releases`
- Rust Blog RSS: `https://blog.rust-lang.org/feed.xml`
- Git tags: `git ls-remote --tags https://github.com/rust-lang/rust.git`

**Output**: `releases.json` with structured release data

```json
{
  "releases": [
    {
      "version": "1.84.0",
      "release_date": "2025-01-09",
      "tag": "1.84.0",
      "blog_post": "https://blog.rust-lang.org/2025/01/09/Rust-1.84.0.html",
      "changelog_url": "https://github.com/rust-lang/rust/blob/1.84.0/RELEASES.md",
      "stabilized_features": ["ptr_fn_addr_eq", "asm_goto"],
      "breaking_changes": [],
      "compiler_changes": ["MIR optimization X", "Type inference fix Y"]
    }
  ],
  "last_check": "2026-01-02T12:00:00Z",
  "current_stable": "1.91.0"
}
```

**Frequency**: Check every 6 hours (Rust releases on Thursdays)

### 2. Impact Analyzer (`trust-impact-analyzer`)

**Purpose**: Determine which upstream changes might affect tRust.

**tRust Integration Points** (files we modify or depend on):

| File | Risk Level | What We Do |
|------|------------|------------|
| `compiler/rustc_interface/src/passes.rs` | HIGH | Add verification hook |
| `compiler/rustc_feature/src/builtin_attrs.rs` | HIGH | Add verification attributes |
| `compiler/rustc_session/src/options.rs` | MEDIUM | Add -Zverify flag |
| `compiler/rustc_middle/src/ty/` | MEDIUM | Type context access |
| `compiler/rustc_mir_build/` | MEDIUM | MIR generation |
| `compiler/rustc_hir/` | LOW | HIR types |

**Analysis Process**:

1. Fetch upstream diff: `git diff 1.83.0..1.84.0`
2. Filter to integration points
3. Classify changes:
   - **SAFE**: No overlap with tRust
   - **MINOR**: Cosmetic changes (renames, formatting)
   - **MODERATE**: API changes that need adaptation
   - **BREAKING**: Fundamental changes requiring significant work

**Output**: `impact_report.json`

```json
{
  "from_version": "1.83.0",
  "to_version": "1.84.0",
  "analysis_date": "2026-01-02",
  "overall_risk": "MODERATE",
  "affected_files": [
    {
      "path": "compiler/rustc_interface/src/passes.rs",
      "risk": "MODERATE",
      "changes": ["Function signature changed", "New parameter added"],
      "tRust_action": "Update verification hook call"
    }
  ],
  "estimated_effort": "2-3 commits",
  "auto_mergeable": false,
  "conflicts_expected": ["passes.rs line 423"]
}
```

### 3. Sync Pipeline (`trust-sync`)

**Purpose**: Automated rebase with conflict detection and resolution assistance.

**Pipeline Stages**:

```
Stage 1: Prepare
├── Fetch upstream tags
├── Create sync branch
├── Backup current state
└── Generate pre-sync report

Stage 2: Rebase
├── Attempt automatic rebase
├── If conflicts:
│   ├── Identify conflict type
│   ├── Apply auto-resolution rules (if safe)
│   └── Generate manual resolution guide
└── Track all resolution decisions

Stage 3: Adapt
├── Update rustc_verify for API changes
├── Fix compilation errors
└── Apply known migration patterns

Stage 4: Build
├── Build stage1 compiler
├── Track build time and errors
└── Generate build report

Stage 5: Test
├── Run tRust integration tests
├── Run rustc test suite (subset)
├── Compare verification results
└── Generate test report

Stage 6: Finalize
├── Merge to main (if all tests pass)
├── Update version tracking
├── Generate sync report
└── Notify completion
```

**Auto-Resolution Rules**:

For known conflict patterns, apply automatic fixes:

```rust
// Rule: Verification hook in passes.rs
// Pattern: Function signature changed but verification call site is clear
// Action: Re-insert verification hook at correct location

// Rule: Attribute list in builtin_attrs.rs
// Pattern: New attributes added to list
// Action: Append tRust attributes to updated list

// Rule: Options in options.rs
// Pattern: Options struct reorganized
// Action: Find unstable_opts and add -Zverify
```

### 4. Sync History Database

**Purpose**: Track all sync operations for auditability and learning.

**Schema**:

```sql
CREATE TABLE sync_operations (
    id TEXT PRIMARY KEY,
    from_version TEXT NOT NULL,
    to_version TEXT NOT NULL,
    started_at TIMESTAMP NOT NULL,
    completed_at TIMESTAMP,
    status TEXT NOT NULL,  -- 'pending', 'in_progress', 'success', 'failed', 'rolled_back'

    -- Metrics
    conflicts_count INTEGER,
    conflicts_auto_resolved INTEGER,
    conflicts_manual_resolved INTEGER,
    build_time_seconds INTEGER,
    tests_passed INTEGER,
    tests_failed INTEGER,

    -- Artifacts
    impact_report_path TEXT,
    sync_report_path TEXT,
    error_log_path TEXT,

    -- Git
    sync_branch TEXT,
    merge_commit TEXT
);

CREATE TABLE conflict_resolutions (
    id TEXT PRIMARY KEY,
    sync_id TEXT REFERENCES sync_operations(id),
    file_path TEXT NOT NULL,
    conflict_type TEXT NOT NULL,
    resolution_type TEXT NOT NULL,  -- 'auto', 'manual', 'pattern'
    resolution_description TEXT,
    created_at TIMESTAMP NOT NULL
);
```

**Location**: `~/.trust/sync_history.db` (SQLite)

### 5. Worker Integration

**Purpose**: Make AI workers aware of sync requirements.

**Startup Check** (add to CLAUDE.md):

```bash
# At worker startup, check upstream currency
SYNC_STATUS=$(trust-sync status --json)
RELEASES_BEHIND=$(echo "$SYNC_STATUS" | jq '.releases_behind')

if [ "$RELEASES_BEHIND" -gt 1 ]; then
    echo "CRITICAL: tRust is $RELEASES_BEHIND releases behind upstream"
    echo "Run: trust-sync run --to-version <next_version>"
    echo "This MUST be resolved before other work"
    exit 1
elif [ "$RELEASES_BEHIND" -eq 1 ]; then
    echo "WARNING: tRust is 1 release behind upstream"
    echo "Sync should be scheduled soon"
fi
```

**Worker Status Integration**:

```json
// worker_status.json additions
{
  "upstream_sync": {
    "current_base": "1.83.0",
    "latest_stable": "1.91.0",
    "releases_behind": 8,
    "last_sync": "2024-12-30",
    "next_sync_due": "2025-01-15",
    "status": "CRITICAL_BEHIND"
  }
}
```

## Tool Implementation

### Directory Structure

```
tools/upstream-tracker/
├── Cargo.toml
├── src/
│   ├── main.rs              # CLI entry point
│   ├── lib.rs               # Library exports
│   ├── monitor/
│   │   ├── mod.rs
│   │   ├── github.rs        # GitHub API client
│   │   ├── changelog.rs     # Changelog parser
│   │   └── releases.rs      # Release database
│   ├── analyzer/
│   │   ├── mod.rs
│   │   ├── diff.rs          # Git diff analysis
│   │   ├── impact.rs        # Impact classification
│   │   └── integration_points.rs  # tRust touchpoints
│   ├── sync/
│   │   ├── mod.rs
│   │   ├── pipeline.rs      # Sync orchestration
│   │   ├── rebase.rs        # Git rebase operations
│   │   ├── conflict.rs      # Conflict detection/resolution
│   │   └── adapt.rs         # API adaptation
│   ├── test/
│   │   ├── mod.rs
│   │   ├── runner.rs        # Test execution
│   │   └── comparator.rs    # Result comparison
│   └── db/
│       ├── mod.rs
│       └── schema.rs        # SQLite schema
├── tests/
│   └── integration/
└── data/
    ├── integration_points.toml  # tRust touchpoints config
    └── resolution_rules.toml    # Auto-resolution patterns
```

### CLI Interface

```
trust-upstream - tRust Upstream Tracking System

USAGE:
    trust-upstream <COMMAND>

COMMANDS:
    monitor     Check for new Rust releases
    analyze     Analyze impact of upgrading to a version
    sync        Perform upstream sync
    status      Show current sync status
    history     Show sync history
    report      Generate sync report

EXAMPLES:
    trust-upstream status
    trust-upstream monitor --check-now
    trust-upstream analyze 1.84.0
    trust-upstream sync --to 1.84.0 --dry-run
    trust-upstream sync --to 1.84.0
    trust-upstream history --last 5
```

### Configuration

**`tools/upstream-tracker/data/integration_points.toml`**:

```toml
# tRust integration points in rustc
# These files are monitored for changes during upstream syncs

[[integration_point]]
path = "compiler/rustc_interface/src/passes.rs"
risk = "high"
description = "Verification hook insertion point"
pattern = "fn analysis"
tRust_modification = """
    // Add after providers setup:
    rustc_verify::provide(providers);

    // Add in compilation:
    if tcx.sess.opts.unstable_opts.verify {
        rustc_verify::verify_crate(tcx, &config);
    }
"""

[[integration_point]]
path = "compiler/rustc_feature/src/builtin_attrs.rs"
risk = "high"
description = "Verification attribute definitions"
pattern = "gated!"
tRust_modification = """
    // Add to attribute list:
    gated!(requires, Normal, template!(NameValueStr: "condition"), ...),
    gated!(ensures, Normal, template!(NameValueStr: "condition"), ...),
    gated!(invariant, Normal, template!(NameValueStr: "condition"), ...),
    gated!(decreases, Normal, template!(NameValueStr: "expression"), ...),
"""

[[integration_point]]
path = "compiler/rustc_session/src/options.rs"
risk = "medium"
description = "-Zverify flag"
pattern = "unstable_opts"
tRust_modification = """
    // Add to Z options:
    verify: bool = (false, parse_bool, [TRACKED],
        "enable formal verification of code with specifications"),
"""

[[dependency]]
crate = "rustc_middle"
used_by = "rustc_verify"
apis = ["TyCtxt", "Body", "DefId", "Ty"]
risk = "medium"

[[dependency]]
crate = "rustc_hir"
used_by = "rustc_verify"
apis = ["Attribute", "Item"]
risk = "low"
```

**`tools/upstream-tracker/data/resolution_rules.toml`**:

```toml
# Automatic conflict resolution rules
# Applied when safe patterns are detected

[[rule]]
name = "passes_hook_insertion"
file = "compiler/rustc_interface/src/passes.rs"
trigger = "conflict in provider setup"
action = "insert_after_pattern"
pattern = "provide(providers)"
insert = "rustc_verify::provide(providers);"
safe = true

[[rule]]
name = "builtin_attrs_append"
file = "compiler/rustc_feature/src/builtin_attrs.rs"
trigger = "conflict in attribute list"
action = "append_to_list"
list_pattern = "pub static BUILTIN_ATTRIBUTES"
items = ["requires", "ensures", "invariant", "decreases"]
safe = true

[[rule]]
name = "api_rename"
trigger = "identifier not found"
action = "suggest_rename"
safe = false  # Requires manual review
```

## Operational Procedures

### Scheduled Sync (Every 6 Weeks)

```
Week 0 (Rust Release Thursday):
  - Release monitor detects new version
  - Impact analyzer generates report
  - Notification sent: "Rust X.Y.0 released, impact: LOW/MEDIUM/HIGH"

Week 1:
  - AI worker begins sync
  - Resolves conflicts
  - Runs tests

Week 2:
  - Review and merge
  - Update version tracking
  - Close sync cycle
```

### Emergency Sync (User-Requested Feature)

```
1. User reports: "Need feature X from Rust 1.88"
2. Check if already synced: trust-upstream status
3. If not, run expedited sync:
   trust-upstream sync --to 1.88.0 --priority high
4. May skip intermediate versions if no breaking changes
```

### Sync Failure Recovery

```
1. Sync fails at stage N
2. System preserves state:
   - sync branch exists
   - conflict markers in place
   - error log generated
3. AI worker or human reviews:
   trust-upstream history --last 1 --verbose
4. Resume or rollback:
   trust-upstream sync --resume
   trust-upstream sync --rollback
```

## Metrics and Alerting

### Key Metrics

| Metric | Target | Alert Threshold |
|--------|--------|-----------------|
| Releases behind | 0-1 | > 1 |
| Sync success rate | > 95% | < 90% |
| Avg sync time | < 4 hours | > 8 hours |
| Manual interventions | < 10% | > 25% |

### Alerts

```
CRITICAL: tRust is 2+ releases behind upstream
WARNING: Sync to X.Y.0 failed, manual intervention needed
INFO: Rust X.Y.0 released, sync scheduled
```

## Success Criteria

1. **Currency**: tRust always within 1 release of stable
2. **Automation**: > 90% of syncs complete without manual intervention
3. **Reliability**: < 1 sync failure per quarter
4. **Speed**: Sync completes within 1 week of release
5. **Visibility**: Always know current sync status

## Implementation Plan

| Phase | Deliverable | Effort |
|-------|-------------|--------|
| 1 | Release monitor (GitHub API) | 1-2 commits |
| 2 | Impact analyzer (diff + classification) | 3-5 commits |
| 3 | Sync pipeline (rebase + build + test) | 5-8 commits |
| 4 | History database (SQLite) | 2-3 commits |
| 5 | Worker integration | 1-2 commits |
| 6 | Auto-resolution rules | 3-5 commits |

**Total: ~15-25 commits (~3-5 hours of AI work)**
