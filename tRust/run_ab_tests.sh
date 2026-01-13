#!/bin/bash
#
# tRust A/B Test Runner for Z3 vs Z4 Validation
#
# Runs the integration test suite twice (once with Z3, once with Z4) and compares
# per-test PASS/FAIL outcomes.
#
# Environment Variables:
#   TRUST_SOLVER=z3|z4            Select backend (set by this script)
#   TRUST_SOLVER_FALLBACK=0|1     When TRUST_SOLVER=z4, fall back to Z3 on quantified/unknown VCs
#
# Output:
#   - Test results summary
#   - A/B comparison statistics
#   - Any MISMATCH warnings (potential backend behavior differences)
#

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Parse command line arguments
VERBOSE=0
FILTER=""
RAW_COMPARISON=0

while [[ $# -gt 0 ]]; do
    case $1 in
        -v|--verbose)
            VERBOSE=1
            shift
            ;;
        -r|--raw)
            RAW_COMPARISON=1
            shift
            ;;
        -f|--filter)
            FILTER="$2"
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 [options]"
            echo ""
            echo "Options:"
            echo "  -v, --verbose    Show detailed output including all A/B test results"
            echo "  -r, --raw        Disable Z4->Z3 fallback for raw comparison"
            echo "  -f, --filter X   Only run tests whose name contains X"
            echo "  -h, --help       Show this help message"
            echo ""
            echo "Examples:"
            echo "  $0                     # Run all tests with A/B comparison"
            echo "  $0 -v                  # Run with verbose output"
            echo "  $0 -r                  # Raw comparison (no fallback)"
            echo "  $0 -f overflow         # Only run overflow tests"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            echo "Use --help for usage information."
            exit 1
            ;;
    esac
done

echo -e "${BLUE}=== tRust A/B Test: Z3 vs Z4 Validation ===${NC}"
echo ""

if [ "$RAW_COMPARISON" -eq 1 ]; then
    export TRUST_SOLVER_FALLBACK=0
    echo -e "${YELLOW}Raw comparison mode: Z4->Z3 fallback disabled${NC}"
else
    export TRUST_SOLVER_FALLBACK=1
    echo "Fallback mode: Z4 will fall back to Z3 for quantified/unknown queries"
fi

echo ""

if [ ! -x "$SCRIPT_DIR/run_tests.sh" ]; then
    echo "Error: $SCRIPT_DIR/run_tests.sh not found or not executable" >&2
    exit 1
fi

# Create temp files for capturing output
Z3_OUT=$(mktemp)
Z4_OUT=$(mktemp)
COMPARE_OUT=$(mktemp)
trap "rm -f $Z3_OUT $Z4_OUT $COMPARE_OUT" EXIT

echo -e "${BLUE}Running tests with Z3...${NC}"
echo ""

RUN_TESTS_ARGS=()
if [ -n "$FILTER" ]; then
    echo "Filter: $FILTER"
    RUN_TESTS_ARGS+=(--filter "$FILTER")
fi

export TRUST_SOLVER=z3
if [ "$VERBOSE" -eq 1 ]; then
    "$SCRIPT_DIR/run_tests.sh" "${RUN_TESTS_ARGS[@]}" 2>&1 | tee "$Z3_OUT"
else
    "$SCRIPT_DIR/run_tests.sh" "${RUN_TESTS_ARGS[@]}" 2>&1 | tee "$Z3_OUT" | grep -E "(^Results:|PASS|FAIL|SKIPPED)"
fi

echo ""
echo -e "${BLUE}=== A/B Test Summary ===${NC}"

echo ""
echo -e "${BLUE}Running tests with Z4...${NC}"
echo ""

export TRUST_SOLVER=z4
if [ "$VERBOSE" -eq 1 ]; then
    "$SCRIPT_DIR/run_tests.sh" "${RUN_TESTS_ARGS[@]}" 2>&1 | tee "$Z4_OUT"
else
    "$SCRIPT_DIR/run_tests.sh" "${RUN_TESTS_ARGS[@]}" 2>&1 | tee "$Z4_OUT" | grep -E "(^Results:|PASS|FAIL|SKIPPED)"
fi

python3 - <<'PY' "$Z3_OUT" "$Z4_OUT" >"$COMPARE_OUT"
import re
import sys

def parse(path: str):
    status = {}
    line_re = re.compile(r"^([A-Za-z0-9_]+): (PASS|FAIL|SKIPPED)")
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for line in f:
            m = line_re.match(line.strip())
            if not m:
                continue
            name, st = m.group(1), m.group(2)
            status[name] = st
    return status

z3 = parse(sys.argv[1])
z4 = parse(sys.argv[2])

if not z3 or not z4:
    print("No per-test results found to compare.")
    print("Ensure run_tests.sh printed lines like: <test_name>: PASS|FAIL")
    sys.exit(2)

all_names = sorted(set(z3) | set(z4))
both_pass = both_fail = z3_pass_z4_fail = z3_fail_z4_pass = skipped_only = 0
mismatches = []

for name in all_names:
    s3 = z3.get(name)
    s4 = z4.get(name)
    if s3 is None or s4 is None:
        skipped_only += 1
        mismatches.append((name, s3 or "MISSING", s4 or "MISSING"))
        continue
    if s3 == "SKIPPED" or s4 == "SKIPPED":
        if s3 != s4:
            mismatches.append((name, s3, s4))
        continue
    if s3 == "PASS" and s4 == "PASS":
        both_pass += 1
    elif s3 == "FAIL" and s4 == "FAIL":
        both_fail += 1
    elif s3 == "PASS" and s4 == "FAIL":
        z3_pass_z4_fail += 1
        mismatches.append((name, s3, s4))
    elif s3 == "FAIL" and s4 == "PASS":
        z3_fail_z4_pass += 1
        mismatches.append((name, s3, s4))
    else:
        mismatches.append((name, s3, s4))

print(f"Total compared: {len(all_names)}")
print(f"  Both PASS: {both_pass}")
print(f"  Both FAIL: {both_fail}")
print(f"  Z3 PASS / Z4 FAIL: {z3_pass_z4_fail}")
print(f"  Z3 FAIL / Z4 PASS: {z3_fail_z4_pass}")
if skipped_only:
    print(f"  Missing in one run: {skipped_only}")
print("")

if mismatches:
    print("MISMATCHES:")
    for name, s3, s4 in mismatches[:100]:
        print(f"  {name}: Z3={s3} Z4={s4}")
PY

cat "$COMPARE_OUT"

MISMATCHES=$(grep -c "^  .*: Z3=" "$COMPARE_OUT" 2>/dev/null || echo 0)

if [ "$MISMATCHES" -gt 0 ]; then
    echo ""
    echo -e "${RED}MISMATCH: $MISMATCHES differing test outcomes detected.${NC}"
fi

echo ""
echo -e "${BLUE}=== End A/B Test Summary ===${NC}"

if [ "$MISMATCHES" -gt 0 ]; then
    exit 1
fi

exit 0
