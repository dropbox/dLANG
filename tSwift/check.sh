#!/bin/bash
# Local quality check script (substitute for CI - GitHub Actions forbidden per CLAUDE.md)
# Run this before committing to ensure code quality
set -e

# Change to script directory so relative paths work
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

USE_COLOR=1
if [ -n "${NO_COLOR:-}" ] || [ ! -t 1 ] || [ "${TERM:-}" = "dumb" ]; then
    USE_COLOR=0
fi

if [ "$USE_COLOR" -eq 0 ]; then
    RED=''
    GREEN=''
    YELLOW=''
    NC=''
fi

echo "=== tSwift Quality Checks ==="
echo ""

# Track failures
FAILURES=0

# 1. Rust formatting check
echo -n "Checking Rust formatting... "
if (cd vc-ir-swift && cargo fmt --check 2>/dev/null); then
    echo -e "${GREEN}OK${NC}"
else
    echo -e "${RED}FAILED${NC}"
    echo "  Run: cd vc-ir-swift && cargo fmt"
    FAILURES=$((FAILURES + 1))
fi

# 2. Clippy lints
echo -n "Running Clippy lints... "
if (cd vc-ir-swift && cargo clippy --quiet --all-targets 2>&1 | grep -q "warning:"); then
    echo -e "${YELLOW}WARNINGS${NC}"
    echo "  Run: cd vc-ir-swift && cargo clippy --all-targets"
    # Not a failure, just warnings
else
    echo -e "${GREEN}OK${NC}"
fi

# 3. Rust tests
echo -n "Running Rust tests... "
TEST_LOG="$(mktemp -t tswift_check_rust_tests.XXXXXX)"
if (cd vc-ir-swift && set -o pipefail && cargo test --quiet 2>/dev/null | tee "$TEST_LOG"); then
    COUNTS="$(
        awk '
            /^test result: ok\./ {
                # POSIX awk: parse fixed-format summary line
                # test result: ok. <passed> passed; <failed> failed; <ignored> ignored; ...
                passed += $4
                failed += $6
                ignored += $8
            }
            END {
                print passed, failed, ignored
            }
        ' "$TEST_LOG"
    )"
    PASSED="$(echo "$COUNTS" | awk '{print $1}')"
    IGNORED="$(echo "$COUNTS" | awk '{print $3}')"
    TOTAL=$((PASSED + IGNORED))
    rm -f "$TEST_LOG"
    echo -e "${GREEN}OK${NC} (${PASSED} passed, ${IGNORED} ignored, ${TOTAL} total)"
else
    rm -f "$TEST_LOG"
    echo -e "${RED}FAILED${NC}"
    echo "  Run: cd vc-ir-swift && cargo test"
    FAILURES=$((FAILURES + 1))
fi

# 4. Roadmap parsing check (if ROADMAP.md exists)
if [ -f "ROADMAP.md" ]; then
    echo -n "Checking ROADMAP.md parsing... "
    # Run in dry-run mode, check for warnings
    # Note: roadmap_to_issues.sh outputs "Warnings: N" and "WARNING:" prefix for actual warnings
    OUTPUT=$(./roadmap_to_issues.sh ROADMAP.md 2>&1 || true)
    # Extract warning count from "Warnings: N" line
    WARNING_COUNT=$(echo "$OUTPUT" | grep -E "^Warnings: [0-9]+" | sed 's/Warnings: //')
    if [ -n "$WARNING_COUNT" ] && [ "$WARNING_COUNT" -gt 0 ]; then
        echo -e "${RED}FAILED${NC}"
        echo "  $WARNING_COUNT warning(s) in ROADMAP.md:"
        # Show actual WARNING: lines from parser output
        echo "$OUTPUT" | grep -E "^.*WARNING:" | sed 's/^/    /'
        FAILURES=$((FAILURES + 1))
    else
        echo -e "${GREEN}OK${NC}"
    fi
else
    echo -e "${YELLOW}Skipping ROADMAP.md check (file not found)${NC}"
fi

echo ""
if [ $FAILURES -eq 0 ]; then
    echo -e "${GREEN}All checks passed!${NC}"
    exit 0
else
    echo -e "${RED}$FAILURES check(s) failed${NC}"
    exit 1
fi
