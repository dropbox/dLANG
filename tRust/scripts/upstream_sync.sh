#!/bin/bash
# upstream_sync.sh - Automated upstream Rust sync for tRust
#
# This script syncs tRust with upstream rustc releases.
# Designed to be run by AI workers or manually.
#
# Usage:
#   ./scripts/upstream_sync.sh check          # Check for new upstream releases
#   ./scripts/upstream_sync.sh sync 1.84.0    # Sync to specific version
#   ./scripts/upstream_sync.sh status         # Show current sync status
#   ./scripts/upstream_sync.sh test           # Run post-sync tests
#
# Environment:
#   TRUST_ROOT          - tRust root directory (default: script's parent)
#   TRUST_UPSTREAM_DIR  - Upstream rustc directory (default: $TRUST_ROOT/upstream/rustc)
#   DRY_RUN             - Set to 1 to preview without making changes

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TRUST_ROOT="${TRUST_ROOT:-$(dirname "$SCRIPT_DIR")}"
UPSTREAM_DIR="${TRUST_UPSTREAM_DIR:-$TRUST_ROOT/upstream/rustc}"
DRY_RUN="${DRY_RUN:-0}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

log_info() { echo -e "${GREEN}[INFO]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }

# Get current tRust base version
get_current_version() {
    if [ -f "$UPSTREAM_DIR/src/version" ]; then
        cat "$UPSTREAM_DIR/src/version"
    else
        echo "unknown"
    fi
}

# Get latest stable Rust version from releases
get_latest_stable() {
    # Fetch from GitHub API (latest release) and extract tag_name.
    # Keep parsing lightweight (no jq dependency).
    curl -fsSL "https://api.github.com/repos/rust-lang/rust/releases/latest" 2>/dev/null | \
        grep -o '"tag_name": "[^"]*"' | \
        head -1 | \
        sed 's/"tag_name": "//;s/"//'
}

# List available versions newer than current
list_available_versions() {
    local current="$1"
    local current_norm
    current_norm=$(normalize_version "$current")

    # Get tags from upstream
    cd "$UPSTREAM_DIR"
    git fetch origin --tags 2>/dev/null || true

    # List version tags newer than current (using portable sort)
    git tag -l '1.*' | grep -E '^1\.[0-9]+\.[0-9]+$' | version_sort | while read -r tag; do
        if version_gt "$tag" "$current_norm"; then
            echo "$tag"
        fi
    done
}

# Portable version sort (no sort -V dependency)
# Reads version strings from stdin, outputs sorted versions
version_sort() {
    # Convert versions to sortable format (zero-padded), sort, then convert back
    while read -r v; do
        local IFS='.'
        read -ra parts <<< "$v"
        # Zero-pad each component to 6 digits for lexicographic sorting
        printf '%06d.%06d.%06d %s\n' "${parts[0]:-0}" "${parts[1]:-0}" "${parts[2]:-0}" "$v"
    done | sort | cut -d' ' -f2
}

# Normalize versions (strip prefixes/suffixes; ensure major.minor.patch)
normalize_version() {
    local v="${1#v}"
    v="${v%%-*}"

    if [[ "$v" =~ ^([0-9]+)\.([0-9]+)$ ]]; then
        echo "${BASH_REMATCH[1]}.${BASH_REMATCH[2]}.0"
        return 0
    fi
    if [[ "$v" =~ ^([0-9]+)\.([0-9]+)\.([0-9]+) ]]; then
        echo "${BASH_REMATCH[1]}.${BASH_REMATCH[2]}.${BASH_REMATCH[3]}"
        return 0
    fi

    echo "$v"
}

# Compare version strings (returns 0 if $1 >= $2, 1 otherwise)
# Portable implementation using numeric comparison (no sort -V dependency)
version_ge() {
    local a
    local b
    a=$(normalize_version "$1")
    b=$(normalize_version "$2")

    if [ "$a" = "$b" ]; then
        return 0
    fi

    # Split versions into major.minor.patch components
    local IFS='.'
    read -ra va <<< "$a"
    read -ra vb <<< "$b"

    # Compare each component numerically
    for i in 0 1 2; do
        local ca="${va[i]:-0}"
        local cb="${vb[i]:-0}"
        if [ "$ca" -gt "$cb" ]; then
            return 0  # a > b, so a >= b
        elif [ "$ca" -lt "$cb" ]; then
            return 1  # a < b
        fi
    done

    return 0  # equal
}

# Compare version strings (returns 0 if $1 > $2, 1 otherwise)
version_gt() {
    local a
    local b
    a=$(normalize_version "$1")
    b=$(normalize_version "$2")

    if [ "$a" = "$b" ]; then
        return 1
    fi

    version_ge "$a" "$b"
}

# Check for new upstream releases
cmd_check() {
    log_info "Checking for upstream Rust releases..."

    local current=$(get_current_version)
    local current_norm
    current_norm=$(normalize_version "$current")
    log_info "Current tRust base: $current_norm"

    local latest
    local latest_norm
    latest=$(get_latest_stable || true)
    if [ -z "$latest" ]; then
        log_error "Failed to fetch latest stable Rust version from GitHub"
        return 2
    fi
    latest_norm=$(normalize_version "$latest")
    log_info "Latest stable Rust: $latest_norm"

    if [ "$current_norm" = "$latest_norm" ]; then
        log_info "tRust is up to date with stable!"
        return 0
    fi

    # Compare versions numerically
    if version_ge "$current_norm" "$latest_norm"; then
        log_info "tRust is ahead of stable (on nightly/dev)"
        return 0
    fi

    log_warn "tRust is behind upstream"
    echo ""
    echo "Available versions to sync:"
    list_available_versions "$current_norm" | while read -r ver; do
        echo "  - $ver"
    done
    echo ""
    echo "Run: ./scripts/upstream_sync.sh sync <version>"

    return 1
}

# Show current sync status
cmd_status() {
    local current=$(get_current_version)

    echo "=== tRust Upstream Sync Status ==="
    echo ""
    echo "Current base version: $current"
    echo "Upstream directory:   $UPSTREAM_DIR"
    echo ""

    cd "$UPSTREAM_DIR"

    # Count tRust-specific changes
    local trust_commits=$(git log --oneline -- compiler/rustc_verify/ 2>/dev/null | wc -l | tr -d ' ')
    local integration_changes=$(git diff HEAD -- compiler/rustc_interface/src/passes.rs 2>/dev/null | wc -l | tr -d ' ')

    echo "tRust-specific commits: $trust_commits"
    echo "Integration point changes: $integration_changes lines"
    echo ""

    # Show modified files (tRust-specific)
    echo "tRust-specific files:"
    echo "  compiler/rustc_verify/ (new crate)"
    echo "  compiler/rustc_interface/src/passes.rs (3 lines added)"
    echo "  compiler/rustc_feature/src/builtin_attrs.rs (verification attributes)"
}

# Perform sync to specific version
cmd_sync() {
    local target_version="$1"

    if [ -z "$target_version" ]; then
        log_error "Usage: $0 sync <version>"
        log_error "Example: $0 sync 1.84.0"
        exit 1
    fi

    local current=$(get_current_version)
    log_info "Syncing from $current to $target_version"

    cd "$UPSTREAM_DIR"

    # Step 1: Fetch upstream
    log_info "Step 1/6: Fetching upstream..."
    if [ "$DRY_RUN" = "1" ]; then
        echo "[DRY RUN] git fetch origin --tags"
    else
        git fetch origin --tags
    fi

    # Step 2: Create sync branch
    local sync_branch="sync/$target_version"
    log_info "Step 2/6: Creating sync branch '$sync_branch'..."
    if [ "$DRY_RUN" = "1" ]; then
        echo "[DRY RUN] git checkout -b $sync_branch"
    else
        git checkout -b "$sync_branch" 2>/dev/null || git checkout "$sync_branch"
    fi

    # Step 3: Rebase onto target version
    log_info "Step 3/6: Rebasing tRust changes onto $target_version..."
    if [ "$DRY_RUN" = "1" ]; then
        echo "[DRY RUN] git rebase $target_version"
    else
        if ! git rebase "$target_version"; then
            log_error "Rebase failed! Manual conflict resolution needed."
            log_error "After resolving conflicts:"
            log_error "  git rebase --continue"
            log_error "  ./scripts/upstream_sync.sh test"
            log_error "  git checkout main && git merge $sync_branch"
            exit 1
        fi
    fi

    # Step 4: Update version file
    log_info "Step 4/6: Updating version file..."
    if [ "$DRY_RUN" = "1" ]; then
        echo "[DRY RUN] echo '$target_version' > src/version"
    else
        echo "$target_version" > src/version
        git add src/version
        git commit --amend --no-edit
    fi

    # Step 5: Build stage1
    log_info "Step 5/6: Building stage1 compiler..."
    if [ "$DRY_RUN" = "1" ]; then
        echo "[DRY RUN] ./x build --stage 1"
    else
        ./x build --stage 1
    fi

    # Step 6: Run tests
    log_info "Step 6/6: Running tRust tests..."
    cmd_test

    log_info "Sync to $target_version complete!"
    log_info "To finalize, merge into main:"
    log_info "  git checkout main"
    log_info "  git merge $sync_branch"
    log_info "  git push origin main"
}

# Run post-sync tests
cmd_test() {
    log_info "Running tRust verification tests..."

    cd "$TRUST_ROOT"

    # Test 1: Compiler builds
    log_info "Test 1: Checking stage1 compiler..."
    if [ ! -x "$TRUST_ROOT/build/host/stage1/bin/rustc" ]; then
        log_error "Stage1 compiler not found!"
        return 1
    fi
    log_info "  Stage1 compiler exists"

    # Test 2: trustc wrapper works
    log_info "Test 2: Checking trustc wrapper..."
    if ! "$TRUST_ROOT/bin/trustc" --version >/dev/null 2>&1; then
        log_error "trustc wrapper failed!"
        return 1
    fi
    log_info "  trustc wrapper works"

    # Test 3: Run integration tests
    log_info "Test 3: Running integration tests..."
    local test_count=0
    local pass_count=0

    # Create temp directory for test outputs (required in rustc 1.91+)
    local test_tmpdir
    test_tmpdir=$(mktemp -d)
    trap "rm -rf '$test_tmpdir'" RETURN

    for test_file in "$TRUST_ROOT"/examples/*_test.rs; do
        [ -f "$test_file" ] || continue
        test_count=$((test_count + 1))
        local test_name
        test_name=$(basename "$test_file" .rs)
        if "$TRUST_ROOT/bin/trustc" "$test_file" --edition 2021 --emit=metadata --crate-type=lib -o "$test_tmpdir/$test_name.rmeta" 2>/dev/null; then
            pass_count=$((pass_count + 1))
        fi
    done

    log_info "  Tests: $pass_count/$test_count passed"

    if [ "$pass_count" -lt "$test_count" ]; then
        log_warn "Some tests failed - manual review needed"
        return 1
    fi

    log_info "All tests passed!"
    return 0
}

# Main command dispatcher
case "${1:-}" in
    check)
        cmd_check
        ;;
    status)
        cmd_status
        ;;
    sync)
        cmd_sync "$2"
        ;;
    test)
        cmd_test
        ;;
    *)
        echo "tRust Upstream Sync Tool"
        echo ""
        echo "Usage: $0 <command> [args]"
        echo ""
        echo "Commands:"
        echo "  check           Check for new upstream releases"
        echo "  status          Show current sync status"
        echo "  sync <version>  Sync to specific version (e.g., 1.84.0)"
        echo "  test            Run post-sync tests"
        echo ""
        echo "Examples:"
        echo "  $0 check"
        echo "  $0 sync 1.84.0"
        echo "  DRY_RUN=1 $0 sync 1.84.0  # Preview without changes"
        ;;
esac
