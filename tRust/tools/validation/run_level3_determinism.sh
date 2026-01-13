#!/usr/bin/env bash
#
# Level 3.3 Validation: Deterministic Output Testing
#
# This script compiles the same source file multiple times with both rustc and
# tRust, then verifies all outputs are identical (deterministic compilation).
#
# Per VALIDATION_PLAN.md Level 3.3:
# - Compile same file 10 times with each compiler
# - All outputs from each compiler must be identical
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
  tools/validation/run_level3_determinism.sh [--iterations N] [--test NAME] [--release] [--verbose]

Options:
  --iterations N   Number of compilation iterations (default: 10)
  --test NAME      Test source file (default: arithmetic)
  --release        Compile with -O (optimization)
  --verbose        Show detailed output
  --help           Show this help message

This test verifies that compiling the same source multiple times produces
identical binary output (deterministic compilation).
EOF
}

ITERATIONS=10
TEST_NAME="arithmetic"
RELEASE_MODE=""
VERBOSE=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --iterations)
      shift
      ITERATIONS="${1:-10}"
      shift || true
      ;;
    --iterations=*)
      ITERATIONS="${1#*=}"
      shift
      ;;
    --test)
      shift
      TEST_NAME="${1:-arithmetic}"
      shift || true
      ;;
    --test=*)
      TEST_NAME="${1#*=}"
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

TEST_FILE="$TEST_DIR/${TEST_NAME}.rs"
if [[ ! -f "$TEST_FILE" ]]; then
  echo "error: test file not found: $TEST_FILE" >&2
  exit 1
fi

WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/trust_determinism_XXXXXX")"
trap 'rm -rf "$WORKDIR"' EXIT

LOG_FILE="$LOG_DIR/determinism.txt"
> "$LOG_FILE"

echo "Level 3.3: Determinism Testing"
echo "==============================="
echo "System rustc:  $SYSTEM_RUSTC"
echo "tRust:         $TRUST_RUSTC"
echo "Test file:     $TEST_FILE"
echo "Iterations:    $ITERATIONS"
[[ -n "$RELEASE_MODE" ]] && echo "Mode:          Release (-O)" || echo "Mode:          Debug"
echo ""

# Compile N times with rustc
echo "Compiling $ITERATIONS times with rustc..."
RUSTC_HASHES=()
for i in $(seq 1 "$ITERATIONS"); do
  OUT="$WORKDIR/rustc_$i"
  if ! "$SYSTEM_RUSTC" --edition 2021 $RELEASE_MODE -o "$OUT" "$TEST_FILE" 2>/dev/null; then
    echo "error: rustc compilation failed on iteration $i" >&2
    exit 1
  fi
  HASH=$(shasum -a 256 "$OUT" | cut -d' ' -f1)
  RUSTC_HASHES+=("$HASH")
  [[ $VERBOSE -eq 1 ]] && echo "  rustc[$i]: $HASH"
done

# Compile N times with tRust
echo "Compiling $ITERATIONS times with tRust..."
TRUST_HASHES=()
for i in $(seq 1 "$ITERATIONS"); do
  OUT="$WORKDIR/trust_$i"
  if ! "$TRUST_RUSTC" --edition 2021 $RELEASE_MODE --no-verify -o "$OUT" "$TEST_FILE" 2>/dev/null; then
    echo "error: tRust compilation failed on iteration $i" >&2
    exit 1
  fi
  HASH=$(shasum -a 256 "$OUT" | cut -d' ' -f1)
  TRUST_HASHES+=("$HASH")
  [[ $VERBOSE -eq 1 ]] && echo "  tRust[$i]: $HASH"
done

echo ""

# Check rustc determinism
RUSTC_UNIQUE=$(printf '%s\n' "${RUSTC_HASHES[@]}" | sort -u | wc -l | tr -d ' ')
RUSTC_FIRST="${RUSTC_HASHES[0]}"

# Check tRust determinism
TRUST_UNIQUE=$(printf '%s\n' "${TRUST_HASHES[@]}" | sort -u | wc -l | tr -d ' ')
TRUST_FIRST="${TRUST_HASHES[0]}"

echo "Results:"
echo "--------"

RUSTC_PASS=0
if [[ "$RUSTC_UNIQUE" -eq 1 ]]; then
  echo "rustc:  PASS (all $ITERATIONS binaries identical)"
  echo "        SHA-256: $RUSTC_FIRST"
  RUSTC_PASS=1
else
  echo "rustc:  FAIL ($RUSTC_UNIQUE unique hashes out of $ITERATIONS)"
  printf '%s\n' "${RUSTC_HASHES[@]}" | sort | uniq -c | while read count hash; do
    echo "        $count x $hash"
  done
fi

TRUST_PASS=0
if [[ "$TRUST_UNIQUE" -eq 1 ]]; then
  echo "tRust:  PASS (all $ITERATIONS binaries identical)"
  echo "        SHA-256: $TRUST_FIRST"
  TRUST_PASS=1
else
  echo "tRust:  FAIL ($TRUST_UNIQUE unique hashes out of $ITERATIONS)"
  printf '%s\n' "${TRUST_HASHES[@]}" | sort | uniq -c | while read count hash; do
    echo "        $count x $hash"
  done
fi

echo ""

# Write log file
{
  echo "Level 3.3 Determinism Test"
  echo "=========================="
  echo "Date: $(date -u '+%Y-%m-%d %H:%M:%S UTC')"
  echo "Test: $TEST_NAME"
  echo "Iterations: $ITERATIONS"
  echo "Mode: ${RELEASE_MODE:-debug}"
  echo ""
  echo "rustc hashes:"
  for i in $(seq 1 "$ITERATIONS"); do
    echo "  $i: ${RUSTC_HASHES[$((i-1))]}"
  done
  echo ""
  echo "tRust hashes:"
  for i in $(seq 1 "$ITERATIONS"); do
    echo "  $i: ${TRUST_HASHES[$((i-1))]}"
  done
  echo ""
  echo "Results:"
  echo "  rustc unique hashes: $RUSTC_UNIQUE"
  echo "  tRust unique hashes: $TRUST_UNIQUE"
} >> "$LOG_FILE"

# Overall result
if [[ $RUSTC_PASS -eq 1 && $TRUST_PASS -eq 1 ]]; then
  echo "Overall: PASS - Both compilers produce deterministic output"
  exit 0
else
  echo "Overall: FAIL - One or more compilers not deterministic"
  exit 1
fi
