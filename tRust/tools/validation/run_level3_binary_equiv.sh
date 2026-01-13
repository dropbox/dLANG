#!/usr/bin/env bash
#
# Level 3 Validation: Binary Equivalence Testing
#
# This script compiles test programs with both rustc and tRust, runs both
# binaries, and compares outputs to verify behavioral equivalence.
#
# Logs: reports/validation/level3_logs/<test>.{rustc,trust,diff}.txt
#
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TEST_DIR="$ROOT/tools/validation/level3_tests"
LOG_DIR="$ROOT/reports/validation/level3_logs"
BIN_DIR="$ROOT/bin"

# Find system rustc
SYSTEM_RUSTC="$(which rustc)"
TRUST_RUSTC="$BIN_DIR/trustc"

mkdir -p "$LOG_DIR"

usage() {
  cat <<'EOF'
Usage:
  tools/validation/run_level3_binary_equiv.sh [--test NAME] [--release] [--verbose] [--verify]

Options:
  --test NAME    Run only the specified test (without .rs extension)
  --release      Compile with -O (optimization)
  --verbose      Show detailed output
  --verify       Enable tRust verification (default: disabled for equivalence testing)
  --help         Show this help message

Tests are located in: tools/validation/level3_tests/*.rs
Results are logged to: reports/validation/level3_logs/
EOF
}

# Normalize output by removing nondeterministic values (thread IDs, addresses, etc.)
normalize_output() {
  sed -E \
    -e 's/thread '"'"'[^'"'"']*'"'"' \([0-9]+\)/thread '\''main'\'' (THREAD_ID)/g' \
    -e 's/0x[0-9a-fA-F]+/0xADDR/g' \
    -e 's/capacity: [0-9]+/capacity: CAP/g'
}

TEST_FILTER=""
RELEASE_MODE=""
VERBOSE=0
VERIFY_MODE=0  # Default: disable verification for equivalence testing

while [[ $# -gt 0 ]]; do
  case "$1" in
    --test)
      shift
      TEST_FILTER="${1:-}"
      shift || true
      ;;
    --test=*)
      TEST_FILTER="${1#*=}"
      shift
      ;;
    --release)
      RELEASE_MODE="-O"
      shift
      ;;
    --verbose)
      VERBOSE=1
      shift
      ;;
    --verify)
      VERIFY_MODE=1
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

# Statistics
TOTAL=0
PASSED=0
FAILED=0
COMPILE_FAILED=0

run_test() {
  local test_file="$1"
  local test_name
  test_name="$(basename "$test_file" .rs)"

  ((TOTAL++)) || true

  local workdir
  workdir="$(mktemp -d "${TMPDIR:-/tmp}/trust_level3_${test_name}_XXXXXX")"

  local rustc_bin="$workdir/${test_name}_rustc"
  local trust_bin="$workdir/${test_name}_trust"
  local rustc_out="$LOG_DIR/${test_name}.rustc.txt"
  local trust_out="$LOG_DIR/${test_name}.trust.txt"
  local diff_out="$LOG_DIR/${test_name}.diff.txt"
  local compile_log="$LOG_DIR/${test_name}.compile.txt"

  # Compile with system rustc
  local rustc_status=0
  {
    echo "=== Compiling with system rustc ($SYSTEM_RUSTC) ==="
    "$SYSTEM_RUSTC" --edition 2021 $RELEASE_MODE -o "$rustc_bin" "$test_file" 2>&1
  } >> "$compile_log" || rustc_status=$?

  if [[ $rustc_status -ne 0 ]]; then
    printf "%-30s SKIP (rustc compile failed)\n" "$test_name"
    rm -rf "$workdir"
    return
  fi

  # Compile with tRust
  local trust_status=0
  local trust_extra_flags=""
  [[ $VERIFY_MODE -eq 0 ]] && trust_extra_flags="--no-verify"
  {
    echo "=== Compiling with tRust ($TRUST_RUSTC) $trust_extra_flags ==="
    "$TRUST_RUSTC" --edition 2021 $RELEASE_MODE $trust_extra_flags -o "$trust_bin" "$test_file" 2>&1
  } >> "$compile_log" || trust_status=$?

  if [[ $trust_status -ne 0 ]]; then
    printf "%-30s FAIL (tRust compile failed)\n" "$test_name"
    ((COMPILE_FAILED++)) || true
    ((FAILED++)) || true
    rm -rf "$workdir"
    return
  fi

  # Run rustc-compiled binary
  local rustc_run_status=0
  "$rustc_bin" 2>&1 | normalize_output > "$rustc_out" || rustc_run_status=$?
  echo "EXIT_CODE=$rustc_run_status" >> "$rustc_out"

  # Run tRust-compiled binary
  local trust_run_status=0
  "$trust_bin" 2>&1 | normalize_output > "$trust_out" || trust_run_status=$?
  echo "EXIT_CODE=$trust_run_status" >> "$trust_out"

  # Compare outputs
  if diff -u "$rustc_out" "$trust_out" > "$diff_out" 2>&1; then
    printf "%-30s PASS\n" "$test_name"
    ((PASSED++)) || true
  else
    printf "%-30s FAIL (output differs)\n" "$test_name"
    ((FAILED++)) || true
    if [[ $VERBOSE -eq 1 ]]; then
      echo "--- Diff ---"
      cat "$diff_out"
      echo "------------"
    fi
  fi

  rm -rf "$workdir"
}

echo "Level 3: Binary Equivalence Testing"
echo "===================================="
echo "System rustc: $SYSTEM_RUSTC"
echo "tRust:        $TRUST_RUSTC"
echo "Test dir:     $TEST_DIR"
echo "Log dir:      $LOG_DIR"
[[ -n "$RELEASE_MODE" ]] && echo "Mode:         Release (-O)"
[[ $VERIFY_MODE -eq 0 ]] && echo "Verification: Disabled (--no-verify)" || echo "Verification: Enabled"
echo ""

# Clear old logs
rm -f "$LOG_DIR"/*.txt

# Run tests
echo "Test                           Status"
echo "----------------------------------------"

if [[ -n "$TEST_FILTER" ]]; then
  test_file="$TEST_DIR/${TEST_FILTER}.rs"
  if [[ -f "$test_file" ]]; then
    run_test "$test_file"
  else
    echo "error: test not found: $test_file" >&2
    exit 1
  fi
else
  for test_file in "$TEST_DIR"/*.rs; do
    [[ -f "$test_file" ]] || continue
    run_test "$test_file"
  done
fi

echo "----------------------------------------"
echo ""
echo "Results: $PASSED/$TOTAL passed, $FAILED failed"
[[ $COMPILE_FAILED -gt 0 ]] && echo "         ($COMPILE_FAILED tRust compile failures)"
echo ""

if [[ $FAILED -eq 0 && $TOTAL -gt 0 ]]; then
  echo "All tests PASSED!"
  exit 0
else
  echo "Some tests FAILED."
  exit 1
fi
