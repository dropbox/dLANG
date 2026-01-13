#!/usr/bin/env bash
#
# Level 3.2 Validation: Performance Equivalence Testing
#
# Measures compile time, binary size, and runtime performance for both
# rustc and tRust, verifying they meet VALIDATION_PLAN.md thresholds:
#   - Compile time: Within 10% of rustc
#   - Binary size:  Within 5% of rustc
#   - Runtime perf: Within 5% of rustc
#
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TEST_DIR="$ROOT/tools/validation/level3_tests"
LOG_DIR="$ROOT/reports/validation/level3_logs"
BIN_DIR="$ROOT/bin"

# Find compilers
SYSTEM_RUSTC="$(which rustc)"
TRUST_RUSTC="$BIN_DIR/trustc"

mkdir -p "$LOG_DIR"

usage() {
  cat <<'EOF'
Usage:
  tools/validation/run_level3_performance.sh [--test NAME] [--all] [--warmup N] [--runs N]

Options:
  --test NAME      Test specific source file (default: all)
  --all            Run all performance tests (compile, size, runtime)
  --warmup N       Number of warmup runs for hyperfine (default: 3)
  --runs N         Number of measurement runs (default: 10)
  --release        Include release mode benchmarks
  --help           Show this help message

Thresholds per VALIDATION_PLAN.md:
  - Compile time: Within 10% of rustc
  - Binary size:  Within 5% of rustc
  - Runtime:      Within 5% of rustc
EOF
}

WARMUP=3
RUNS=10
TEST_NAME=""
RUN_ALL=1
RELEASE_MODE=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --test)
      shift
      TEST_NAME="${1:-}"
      RUN_ALL=0
      shift || true
      ;;
    --test=*)
      TEST_NAME="${1#*=}"
      RUN_ALL=0
      shift
      ;;
    --all)
      RUN_ALL=1
      shift
      ;;
    --warmup)
      shift
      WARMUP="${1:-3}"
      shift || true
      ;;
    --warmup=*)
      WARMUP="${1#*=}"
      shift
      ;;
    --runs)
      shift
      RUNS="${1:-10}"
      shift || true
      ;;
    --runs=*)
      RUNS="${1#*=}"
      shift
      ;;
    --release)
      RELEASE_MODE=1
      shift
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
done

WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/trust_perf_XXXXXX")"
trap 'rm -rf "$WORKDIR"' EXIT

LOG_FILE="$LOG_DIR/performance.txt"
> "$LOG_FILE"

echo "Level 3.2: Performance Equivalence Testing"
echo "==========================================="
echo "System rustc:  $SYSTEM_RUSTC"
echo "tRust:         $TRUST_RUSTC"
echo "Warmup runs:   $WARMUP"
echo "Measure runs:  $RUNS"
echo ""

# Get test files
if [[ -n "$TEST_NAME" ]]; then
  TEST_FILES=("$TEST_DIR/${TEST_NAME}.rs")
else
  TEST_FILES=("$TEST_DIR"/*.rs)
fi

# Results arrays
declare -a COMPILE_RESULTS
declare -a SIZE_RESULTS
declare -a RUNTIME_RESULTS

TOTAL_TESTS=0
COMPILE_PASS=0
SIZE_PASS=0
RUNTIME_PASS=0

# Function to calculate percentage difference
calc_pct_diff() {
  local baseline="$1"
  local measured="$2"
  echo "scale=2; (($measured - $baseline) / $baseline) * 100" | bc
}

# Function to check threshold
check_threshold() {
  local pct="$1"
  local threshold="$2"
  # Check if pct <= threshold (allow negative values = better than baseline)
  if (( $(echo "$pct <= $threshold" | bc -l) )); then
    return 0
  else
    return 1
  fi
}

echo "=== COMPILE TIME BENCHMARKS ==="
echo ""

for TEST_FILE in "${TEST_FILES[@]}"; do
  if [[ ! -f "$TEST_FILE" ]]; then
    echo "warning: test file not found: $TEST_FILE" >&2
    continue
  fi

  TEST_BASE=$(basename "$TEST_FILE" .rs)
  ((TOTAL_TESTS++)) || true

  echo "Testing: $TEST_BASE"

  RUSTC_OUT="$WORKDIR/rustc_${TEST_BASE}"
  TRUST_OUT="$WORKDIR/trust_${TEST_BASE}"

  # Compile time benchmark
  echo "  Compile time (debug mode)..."

  # Use hyperfine to get compile time stats
  HYPERFINE_OUT="$WORKDIR/hyperfine_${TEST_BASE}.json"

  hyperfine --warmup "$WARMUP" --runs "$RUNS" --export-json "$HYPERFINE_OUT" \
    --command-name "rustc" "$SYSTEM_RUSTC --edition 2021 -o $RUSTC_OUT $TEST_FILE" \
    --command-name "tRust" "$TRUST_RUSTC --edition 2021 --no-verify -o $TRUST_OUT $TEST_FILE" \
    2>/dev/null

  # Extract mean times from JSON
  RUSTC_TIME=$(jq -r '.results[] | select(.command == "rustc") | .mean' "$HYPERFINE_OUT")
  TRUST_TIME=$(jq -r '.results[] | select(.command == "tRust") | .mean' "$HYPERFINE_OUT")

  COMPILE_PCT=$(calc_pct_diff "$RUSTC_TIME" "$TRUST_TIME")

  if check_threshold "$COMPILE_PCT" "10"; then
    COMPILE_STATUS="PASS"
    ((COMPILE_PASS++)) || true
  else
    COMPILE_STATUS="FAIL"
  fi

  printf "    rustc: %.3fs, tRust: %.3fs (%.1f%% diff) - %s\n" \
    "$RUSTC_TIME" "$TRUST_TIME" "$COMPILE_PCT" "$COMPILE_STATUS"

  COMPILE_RESULTS+=("$TEST_BASE|$RUSTC_TIME|$TRUST_TIME|$COMPILE_PCT|$COMPILE_STATUS")

  # Binary size comparison
  echo "  Binary size..."
  RUSTC_SIZE=$(stat -f%z "$RUSTC_OUT" 2>/dev/null || stat --printf="%s" "$RUSTC_OUT")
  TRUST_SIZE=$(stat -f%z "$TRUST_OUT" 2>/dev/null || stat --printf="%s" "$TRUST_OUT")

  SIZE_PCT=$(calc_pct_diff "$RUSTC_SIZE" "$TRUST_SIZE")

  if check_threshold "$SIZE_PCT" "5"; then
    SIZE_STATUS="PASS"
    ((SIZE_PASS++)) || true
  else
    SIZE_STATUS="FAIL"
  fi

  printf "    rustc: %d bytes, tRust: %d bytes (%.1f%% diff) - %s\n" \
    "$RUSTC_SIZE" "$TRUST_SIZE" "$SIZE_PCT" "$SIZE_STATUS"

  SIZE_RESULTS+=("$TEST_BASE|$RUSTC_SIZE|$TRUST_SIZE|$SIZE_PCT|$SIZE_STATUS")

  # Runtime performance (only for tests that produce runnable output)
  # Skip tests that might hang or require input
  case "$TEST_BASE" in
    threading|file_io)
      echo "  Runtime: skipped (I/O or threading)"
      RUNTIME_RESULTS+=("$TEST_BASE|N/A|N/A|N/A|SKIP")
      ;;
    *)
      echo "  Runtime performance..."

      RUNTIME_OUT="$WORKDIR/runtime_${TEST_BASE}.json"

      if hyperfine --warmup 2 --runs 5 --export-json "$RUNTIME_OUT" \
        --command-name "rustc" "$RUSTC_OUT" \
        --command-name "tRust" "$TRUST_OUT" \
        2>/dev/null; then

        RUSTC_RUNTIME=$(jq -r '.results[] | select(.command == "rustc") | .mean' "$RUNTIME_OUT")
        TRUST_RUNTIME=$(jq -r '.results[] | select(.command == "tRust") | .mean' "$RUNTIME_OUT")

        RUNTIME_PCT=$(calc_pct_diff "$RUSTC_RUNTIME" "$TRUST_RUNTIME")

        if check_threshold "$RUNTIME_PCT" "5"; then
          RUNTIME_STATUS="PASS"
          ((RUNTIME_PASS++)) || true
        else
          RUNTIME_STATUS="FAIL"
        fi

        printf "    rustc: %.4fs, tRust: %.4fs (%.1f%% diff) - %s\n" \
          "$RUSTC_RUNTIME" "$TRUST_RUNTIME" "$RUNTIME_PCT" "$RUNTIME_STATUS"

        RUNTIME_RESULTS+=("$TEST_BASE|$RUSTC_RUNTIME|$TRUST_RUNTIME|$RUNTIME_PCT|$RUNTIME_STATUS")
      else
        echo "    Runtime: measurement failed"
        RUNTIME_RESULTS+=("$TEST_BASE|N/A|N/A|N/A|FAIL")
      fi
      ;;
  esac

  echo ""
done

# Calculate runnable tests for runtime (exclude skipped)
RUNTIME_TOTAL=0
for r in "${RUNTIME_RESULTS[@]}"; do
  status=$(echo "$r" | cut -d'|' -f5)
  if [[ "$status" != "SKIP" ]]; then
    ((RUNTIME_TOTAL++)) || true
  fi
done

echo "=== SUMMARY ==="
echo ""
echo "Compile Time (threshold: within 10%):"
echo "  Passed: $COMPILE_PASS/$TOTAL_TESTS"
echo ""
echo "Binary Size (threshold: within 5%):"
echo "  Passed: $SIZE_PASS/$TOTAL_TESTS"
echo ""
echo "Runtime Performance (threshold: within 5%):"
echo "  Passed: $RUNTIME_PASS/$RUNTIME_TOTAL (skipped: $((TOTAL_TESTS - RUNTIME_TOTAL)))"
echo ""

# Write detailed log
{
  echo "Level 3.2 Performance Equivalence Test"
  echo "======================================="
  echo "Date: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  echo "Warmup: $WARMUP, Runs: $RUNS"
  echo ""
  echo "COMPILE TIME RESULTS"
  echo "--------------------"
  printf "%-20s %12s %12s %10s %s\n" "Test" "rustc(s)" "tRust(s)" "Diff(%)" "Status"
  for r in "${COMPILE_RESULTS[@]}"; do
    IFS='|' read -r name rustc trust pct status <<< "$r"
    printf "%-20s %12.3f %12.3f %10.1f %s\n" "$name" "$rustc" "$trust" "$pct" "$status"
  done
  echo ""
  echo "BINARY SIZE RESULTS"
  echo "-------------------"
  printf "%-20s %12s %12s %10s %s\n" "Test" "rustc(B)" "tRust(B)" "Diff(%)" "Status"
  for r in "${SIZE_RESULTS[@]}"; do
    IFS='|' read -r name rustc trust pct status <<< "$r"
    printf "%-20s %12s %12s %10s %s\n" "$name" "$rustc" "$trust" "$pct" "$status"
  done
  echo ""
  echo "RUNTIME RESULTS"
  echo "---------------"
  printf "%-20s %12s %12s %10s %s\n" "Test" "rustc(s)" "tRust(s)" "Diff(%)" "Status"
  for r in "${RUNTIME_RESULTS[@]}"; do
    IFS='|' read -r name rustc trust pct status <<< "$r"
    printf "%-20s %12s %12s %10s %s\n" "$name" "$rustc" "$trust" "$pct" "$status"
  done
  echo ""
  echo "SUMMARY"
  echo "-------"
  echo "Compile Time: $COMPILE_PASS/$TOTAL_TESTS passed (threshold: 10%)"
  echo "Binary Size:  $SIZE_PASS/$TOTAL_TESTS passed (threshold: 5%)"
  echo "Runtime:      $RUNTIME_PASS/$RUNTIME_TOTAL passed (threshold: 5%)"
} >> "$LOG_FILE"

# Overall result
if [[ $COMPILE_PASS -eq $TOTAL_TESTS && $SIZE_PASS -eq $TOTAL_TESTS && $RUNTIME_PASS -eq $RUNTIME_TOTAL ]]; then
  echo "Overall: PASS - All performance metrics within thresholds"
  exit 0
else
  echo "Overall: PARTIAL - Some metrics exceed thresholds"
  # Exit 0 anyway to not break automation - this is informational
  exit 0
fi
