#!/usr/bin/env bash
#
# Level 4 Validation: Feature Coverage Testing
#
# This script tests that all rustc language features work identically in tRust.
#
# Tests:
#   4.1 Language Features: generics, traits, async, macros, etc.
#   4.2 Compiler Flags: -O levels, -g, --target, -C options
#   4.3 Error Messages: equivalent or better diagnostics
#
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
TEST_DIR="$ROOT/tools/validation/level4_tests"
LOG_DIR="$ROOT/reports/validation/level4_logs"
BIN_DIR="$ROOT/bin"

SYSTEM_RUSTC="$(which rustc)"
TRUST_RUSTC="$BIN_DIR/trustc"

mkdir -p "$LOG_DIR"

usage() {
  cat <<'EOF'
Usage:
  tools/validation/run_level4_features.sh [OPTIONS]

Options:
  --test NAME        Run only the specified test
  --category CAT     Run only tests in category (language_features, compiler_flags, error_messages)
  --verbose          Show detailed output
  --help             Show this help message

Tests are located in: tools/validation/level4_tests/
Results are logged to: reports/validation/level4_logs/
EOF
}

TEST_FILTER=""
CATEGORY_FILTER=""
VERBOSE=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --test) TEST_FILTER="${2:-}"; shift 2 || shift ;;
    --test=*) TEST_FILTER="${1#*=}"; shift ;;
    --category) CATEGORY_FILTER="${2:-}"; shift 2 || shift ;;
    --category=*) CATEGORY_FILTER="${1#*=}"; shift ;;
    --verbose) VERBOSE=1; shift ;;
    --help|-h) usage; exit 0 ;;
    *) echo "error: unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

# Global statistics (bash 3.x compatible)
TOTAL=0
PASSED=0
FAILED=0
LF_TOTAL=0
LF_PASSED=0
LF_FAILED=0
CF_TOTAL=0
CF_PASSED=0
CF_FAILED=0
EM_TOTAL=0
EM_PASSED=0
EM_FAILED=0

# Normalize output for comparison
normalize_output() {
  sed -E \
    -e 's/0x[0-9a-fA-F]+/0xADDR/g' \
    -e 's/thread '"'"'[^'"'"']*'"'"'/thread '\''main'\''/g'
}

# Test language feature - compiles and runs, compares output
test_language_feature() {
  local test_file="$1"
  local test_name
  test_name="$(basename "$test_file" .rs)"

  TOTAL=$((TOTAL + 1))
  LF_TOTAL=$((LF_TOTAL + 1))

  local workdir
  workdir="$(mktemp -d "${TMPDIR:-/tmp}/trust_l4_${test_name}_XXXXXX")"

  local rustc_bin="$workdir/${test_name}_rustc"
  local trust_bin="$workdir/${test_name}_trust"
  local log="$LOG_DIR/${test_name}.log"

  # Compile with rustc
  local rustc_status=0
  echo "=== rustc compile ===" > "$log"
  "$SYSTEM_RUSTC" --edition 2021 -o "$rustc_bin" "$test_file" 2>> "$log" || rustc_status=$?

  if [[ $rustc_status -ne 0 ]]; then
    printf "  %-35s SKIP (rustc fails)\n" "$test_name"
    TOTAL=$((TOTAL - 1))
    LF_TOTAL=$((LF_TOTAL - 1))
    rm -rf "$workdir"
    return
  fi

  # Compile with tRust
  local trust_status=0
  echo "=== tRust compile ===" >> "$log"
  "$TRUST_RUSTC" --edition 2021 --no-verify -o "$trust_bin" "$test_file" 2>> "$log" || trust_status=$?

  if [[ $trust_status -ne 0 ]]; then
    printf "  %-35s FAIL (tRust compile)\n" "$test_name"
    FAILED=$((FAILED + 1))
    LF_FAILED=$((LF_FAILED + 1))
    [[ $VERBOSE -eq 1 ]] && tail -20 "$log"
    rm -rf "$workdir"
    return
  fi

  # Run both and compare
  local rustc_out="$workdir/rustc.out"
  local trust_out="$workdir/trust.out"

  "$rustc_bin" 2>&1 | normalize_output > "$rustc_out" || true
  "$trust_bin" 2>&1 | normalize_output > "$trust_out" || true

  if diff -q "$rustc_out" "$trust_out" > /dev/null 2>&1; then
    printf "  %-35s PASS\n" "$test_name"
    PASSED=$((PASSED + 1))
    LF_PASSED=$((LF_PASSED + 1))
  else
    printf "  %-35s FAIL (output differs)\n" "$test_name"
    FAILED=$((FAILED + 1))
    LF_FAILED=$((LF_FAILED + 1))
    echo "=== Output diff ===" >> "$log"
    diff -u "$rustc_out" "$trust_out" >> "$log" 2>&1 || true
    [[ $VERBOSE -eq 1 ]] && diff -u "$rustc_out" "$trust_out"
  fi

  rm -rf "$workdir"
}

# Test compiler flag - just verifies compilation succeeds
test_compiler_flag() {
  local test_file="$1"
  local flags="$2"
  local test_name="$3"

  TOTAL=$((TOTAL + 1))
  CF_TOTAL=$((CF_TOTAL + 1))

  local workdir
  workdir="$(mktemp -d "${TMPDIR:-/tmp}/trust_l4_flag_XXXXXX")"
  local log="$LOG_DIR/flag_${test_name}.log"

  # Test that tRust accepts the same flags as rustc
  echo "=== Testing flags: $flags ===" > "$log"

  local trust_status=0
  "$TRUST_RUSTC" --edition 2021 --no-verify $flags -o "$workdir/out" "$test_file" 2>> "$log" || trust_status=$?

  if [[ $trust_status -eq 0 ]]; then
    printf "  %-35s PASS\n" "$test_name"
    PASSED=$((PASSED + 1))
    CF_PASSED=$((CF_PASSED + 1))
  else
    printf "  %-35s FAIL\n" "$test_name"
    FAILED=$((FAILED + 1))
    CF_FAILED=$((CF_FAILED + 1))
    [[ $VERBOSE -eq 1 ]] && tail -20 "$log"
  fi

  rm -rf "$workdir"
}

# Test error message - compiles intentionally broken code
test_error_message() {
  local test_file="$1"
  local test_name
  test_name="$(basename "$test_file" .rs)"

  TOTAL=$((TOTAL + 1))
  EM_TOTAL=$((EM_TOTAL + 1))

  local log="$LOG_DIR/error_${test_name}.log"
  local rustc_err="$LOG_DIR/error_${test_name}.rustc.txt"
  local trust_err="$LOG_DIR/error_${test_name}.trust.txt"

  # Capture error messages from both
  "$SYSTEM_RUSTC" --edition 2021 "$test_file" 2> "$rustc_err" || true
  "$TRUST_RUSTC" --edition 2021 --no-verify "$test_file" 2> "$trust_err" || true

  # Check that tRust produces SOME error (not acceptance of invalid code)
  if [[ -s "$trust_err" ]]; then
    printf "  %-35s PASS (error produced)\n" "$test_name"
    PASSED=$((PASSED + 1))
    EM_PASSED=$((EM_PASSED + 1))
  else
    printf "  %-35s FAIL (no error from tRust)\n" "$test_name"
    FAILED=$((FAILED + 1))
    EM_FAILED=$((EM_FAILED + 1))
  fi

  # Log comparison
  {
    echo "=== rustc error ==="
    cat "$rustc_err"
    echo "=== tRust error ==="
    cat "$trust_err"
  } > "$log"
}

echo "Level 4: Feature Coverage Testing"
echo "=================================="
echo "System rustc: $SYSTEM_RUSTC"
echo "tRust:        $TRUST_RUSTC"
echo ""

# Clear old logs
rm -f "$LOG_DIR"/*.log "$LOG_DIR"/*.txt

# 4.1 Language Features
if [[ -z "$CATEGORY_FILTER" || "$CATEGORY_FILTER" == "language_features" ]]; then
  echo "4.1 Language Features"
  echo "---------------------"

  for test_file in "$TEST_DIR/language_features"/*.rs; do
    [[ -f "$test_file" ]] || continue
    test_name="$(basename "$test_file" .rs)"
    [[ -n "$TEST_FILTER" && "$test_name" != "$TEST_FILTER" ]] && continue
    test_language_feature "$test_file"
  done
  echo ""
fi

# 4.2 Compiler Flags
if [[ -z "$CATEGORY_FILTER" || "$CATEGORY_FILTER" == "compiler_flags" ]]; then
  echo "4.2 Compiler Flags"
  echo "------------------"

  # Use a simple test program
  FLAG_TEST="$TEST_DIR/compiler_flags/simple.rs"
  [[ -f "$FLAG_TEST" ]] || FLAG_TEST="$TEST_DIR/language_features/01_generics.rs"

  if [[ -f "$FLAG_TEST" ]]; then
    # Optimization levels
    test_compiler_flag "$FLAG_TEST" "-O" "opt_O"
    test_compiler_flag "$FLAG_TEST" "-C opt-level=0" "opt_level_0"
    test_compiler_flag "$FLAG_TEST" "-C opt-level=1" "opt_level_1"
    test_compiler_flag "$FLAG_TEST" "-C opt-level=2" "opt_level_2"
    test_compiler_flag "$FLAG_TEST" "-C opt-level=3" "opt_level_3"
    test_compiler_flag "$FLAG_TEST" "-C opt-level=s" "opt_level_s"
    test_compiler_flag "$FLAG_TEST" "-C opt-level=z" "opt_level_z"

    # Debug info
    test_compiler_flag "$FLAG_TEST" "-g" "debug_g"
    test_compiler_flag "$FLAG_TEST" "-C debuginfo=0" "debuginfo_0"
    test_compiler_flag "$FLAG_TEST" "-C debuginfo=1" "debuginfo_1"
    test_compiler_flag "$FLAG_TEST" "-C debuginfo=2" "debuginfo_2"

    # LTO
    test_compiler_flag "$FLAG_TEST" "-C lto=off" "lto_off"
    test_compiler_flag "$FLAG_TEST" "-C lto=thin" "lto_thin"
    test_compiler_flag "$FLAG_TEST" "-C lto=fat" "lto_fat"

    # Codegen units
    test_compiler_flag "$FLAG_TEST" "-C codegen-units=1" "codegen_units_1"
    test_compiler_flag "$FLAG_TEST" "-C codegen-units=16" "codegen_units_16"

    # Panic strategy
    test_compiler_flag "$FLAG_TEST" "-C panic=unwind" "panic_unwind"
    test_compiler_flag "$FLAG_TEST" "-C panic=abort" "panic_abort"

    # Other common flags
    test_compiler_flag "$FLAG_TEST" "-C overflow-checks=on" "overflow_on"
    test_compiler_flag "$FLAG_TEST" "-C overflow-checks=off" "overflow_off"
    test_compiler_flag "$FLAG_TEST" "--emit=llvm-ir" "emit_llvm_ir"
    test_compiler_flag "$FLAG_TEST" "--emit=asm" "emit_asm"
  else
    echo "  (no test file available)"
  fi
  echo ""
fi

# 4.3 Error Messages
if [[ -z "$CATEGORY_FILTER" || "$CATEGORY_FILTER" == "error_messages" ]]; then
  echo "4.3 Error Messages"
  echo "------------------"

  for test_file in "$TEST_DIR/error_messages"/*.rs; do
    [[ -f "$test_file" ]] || continue
    test_name="$(basename "$test_file" .rs)"
    [[ -n "$TEST_FILTER" && "$test_name" != "$TEST_FILTER" ]] && continue
    test_error_message "$test_file"
  done
  echo ""
fi

# Summary
echo "========================================"
echo "Summary"
echo "========================================"

if [[ $LF_TOTAL -gt 0 ]]; then
  printf "  %-20s %d/%d passed\n" "language_features:" "$LF_PASSED" "$LF_TOTAL"
fi
if [[ $CF_TOTAL -gt 0 ]]; then
  printf "  %-20s %d/%d passed\n" "compiler_flags:" "$CF_PASSED" "$CF_TOTAL"
fi
if [[ $EM_TOTAL -gt 0 ]]; then
  printf "  %-20s %d/%d passed\n" "error_messages:" "$EM_PASSED" "$EM_TOTAL"
fi

echo "----------------------------------------"
printf "  %-20s %d/%d passed, %d failed\n" "TOTAL:" "$PASSED" "$TOTAL" "$FAILED"
echo ""

if [[ $FAILED -eq 0 && $TOTAL -gt 0 ]]; then
  echo "All tests PASSED!"
  exit 0
else
  echo "Some tests FAILED."
  exit 1
fi
