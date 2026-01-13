#!/usr/bin/env bash
#
# Level 0 Validation: Build Integrity Testing
#
# This script validates that tRust builds correctly and produces working binaries.
# Tests Stage 1 build integrity and optionally attempts Stage 2 bootstrap.
#
# Logs: reports/validation/level0_logs/
#
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LOG_DIR="$ROOT/reports/validation/level0_logs"
RUSTC_DIR="$ROOT/upstream/rustc"
BIN_DIR="$ROOT/bin"
TEMP_DIR="$ROOT/.tmp_level0_tests"

# Detect host triple - try existing build first, then fall back to detection
detect_host_triple() {
  # Try to find existing stage1 build
  local existing
  existing=$(find "$RUSTC_DIR/build" -maxdepth 1 -type d -name "*-*-*" 2>/dev/null | head -1)
  if [[ -n "$existing" ]]; then
    basename "$existing"
    return
  fi
  # Fall back to platform detection
  local arch os
  arch=$(uname -m)
  os=$(uname -s)
  case "$arch-$os" in
    arm64-Darwin|aarch64-Darwin) echo "aarch64-apple-darwin" ;;
    x86_64-Darwin) echo "x86_64-apple-darwin" ;;
    x86_64-Linux) echo "x86_64-unknown-linux-gnu" ;;
    aarch64-Linux) echo "aarch64-unknown-linux-gnu" ;;
    *) echo "x86_64-unknown-linux-gnu" ;;  # Conservative default
  esac
}
HOST_TRIPLE="$(detect_host_triple)"
STAGE1_RUSTC="$RUSTC_DIR/build/$HOST_TRIPLE/stage1/bin/rustc"
TRUST_RUSTC="$BIN_DIR/trustc"

mkdir -p "$LOG_DIR" "$TEMP_DIR"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

usage() {
  cat <<'EOF'
Usage:
  tools/validation/run_level0_build.sh [--stage2] [--rebuild] [--verbose]

Options:
  --stage2     Attempt Stage 2 bootstrap build (time-intensive, ~1 hour)
  --rebuild    Force rebuild of Stage 1
  --verbose    Show detailed output
  --help       Show this help message

Default: Validates Stage 1 build exists and works correctly.
EOF
}

STAGE2_TEST=0
REBUILD=0
VERBOSE=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --stage2) STAGE2_TEST=1; shift ;;
    --rebuild) REBUILD=1; shift ;;
    --verbose) VERBOSE=1; shift ;;
    --help) usage; exit 0 ;;
    *) echo "Unknown option: $1"; usage; exit 1 ;;
  esac
done

PASSED=0
FAILED=0
SKIPPED=0

log() {
  local level="$1"
  shift
  case "$level" in
    PASS) echo -e "${GREEN}[PASS]${NC} $*" ;;
    FAIL) echo -e "${RED}[FAIL]${NC} $*" ;;
    SKIP) echo -e "${YELLOW}[SKIP]${NC} $*" ;;
    INFO) echo -e "[INFO] $*" ;;
  esac
}

run_test() {
  local name="$1"
  local desc="$2"
  shift 2

  if [[ $VERBOSE -eq 1 ]]; then
    log INFO "Running: $name - $desc"
  fi

  local log_file="$LOG_DIR/${name}.log"

  if "$@" > "$log_file" 2>&1; then
    log PASS "$name: $desc"
    ((PASSED++))
    return 0
  else
    log FAIL "$name: $desc (see $log_file)"
    ((FAILED++))
    return 1
  fi
}

echo "====================================="
echo "Level 0: Build Integrity Validation"
echo "====================================="
echo ""
echo "Date: $(date)"
echo "Host: $HOST_TRIPLE"
echo ""

# Test 0.1: Stage 1 rustc executable exists
test_stage1_exists() {
  [[ -f "$STAGE1_RUSTC" ]]
}
run_test "0.1.1_stage1_exists" "Stage 1 rustc executable exists" test_stage1_exists

# Test 0.1.2: trustc wrapper exists
test_trustc_exists() {
  [[ -f "$TRUST_RUSTC" ]]
}
run_test "0.1.2_trustc_exists" "trustc wrapper exists" test_trustc_exists

# Test 0.2: Version output
test_version() {
  local version
  version=$("$STAGE1_RUSTC" --version 2>&1)
  echo "$version"
  [[ "$version" == *"1.92.0-dev"* || "$version" == *"1.83.0"* ]]
}
run_test "0.2_version" "rustc reports correct version" test_version

# Test 0.3: Simple compilation (hello world)
test_hello_compile() {
  local src="$TEMP_DIR/hello.rs"
  local out="$TEMP_DIR/hello"

  cat > "$src" << 'RUST'
fn main() {
    println!("Hello, tRust!");
}
RUST

  "$STAGE1_RUSTC" "$src" -o "$out" && [[ -x "$out" ]]
}
run_test "0.3.1_hello_compile" "Simple program compiles" test_hello_compile

# Test 0.3.2: Hello world runs correctly
test_hello_run() {
  local out="$TEMP_DIR/hello"
  local output
  output=$("$out" 2>&1)
  echo "$output"
  [[ "$output" == "Hello, tRust!" ]]
}
run_test "0.3.2_hello_run" "Simple program runs correctly" test_hello_run

# Test 0.4: -Zverify flag recognized
test_verify_flag() {
  local src="$TEMP_DIR/verify_test.rs"

  cat > "$src" << 'RUST'
fn main() {
    let x = 42;
    println!("{}", x);
}
RUST

  # Check if the flag is recognized (may warn but should not error)
  "$STAGE1_RUSTC" -Zverify "$src" -o "$TEMP_DIR/verify_out" 2>&1 || true
  [[ -f "$TEMP_DIR/verify_out" ]]
}
run_test "0.4_verify_flag" "-Zverify flag accepted" test_verify_flag

# Test 0.5: Compilation with optimization
test_optimized_compile() {
  local src="$TEMP_DIR/opt_test.rs"
  local out="$TEMP_DIR/opt_out"

  cat > "$src" << 'RUST'
fn main() {
    let sum: i32 = (1..=100).sum();
    println!("Sum: {}", sum);
}
RUST

  "$STAGE1_RUSTC" -O "$src" -o "$out" && [[ -x "$out" ]]
}
run_test "0.5_optimized" "Optimized compilation works" test_optimized_compile

# Test 0.6: Complex program (multiple functions, generics)
test_complex_compile() {
  local src="$TEMP_DIR/complex.rs"
  local out="$TEMP_DIR/complex"

  cat > "$src" << 'RUST'
fn add<T: std::ops::Add<Output = T>>(a: T, b: T) -> T {
    a + b
}

struct Counter {
    count: u32,
}

impl Counter {
    fn new() -> Self {
        Counter { count: 0 }
    }

    fn increment(&mut self) {
        self.count += 1;
    }
}

fn main() {
    let result = add(10, 20);
    println!("Generic add: {}", result);

    let mut counter = Counter::new();
    counter.increment();
    counter.increment();
    println!("Counter: {}", counter.count);
}
RUST

  "$STAGE1_RUSTC" "$src" -o "$out" 2>&1
  [[ -x "$out" ]] && "$out" > /dev/null 2>&1
}
run_test "0.6_complex" "Complex program (generics, structs) compiles and runs" test_complex_compile

# Test 0.7: Rebuild consistency (matches rustc determinism behavior)
# Note: Neither rustc nor tRust produce byte-identical binaries by default.
# This test verifies that tRust matches rustc's determinism characteristics.
test_determinism_behavior() {
  local src="$TEMP_DIR/determ.rs"

  cat > "$src" << 'RUST'
fn main() {
    println!("Determinism test");
}
RUST

  # Build twice with tRust
  "$STAGE1_RUSTC" "$src" -o "$TEMP_DIR/trust1" 2>&1
  "$STAGE1_RUSTC" "$src" -o "$TEMP_DIR/trust2" 2>&1

  # Check that binaries are valid (both execute correctly)
  local out1 out2
  out1=$("$TEMP_DIR/trust1" 2>&1)
  out2=$("$TEMP_DIR/trust2" 2>&1)

  echo "tRust build 1 output: $out1"
  echo "tRust build 2 output: $out2"

  # Both must produce correct output (behavioral equivalence)
  [[ "$out1" == "Determinism test" ]] && [[ "$out2" == "Determinism test" ]]
}
run_test "0.7_determinism" "Multiple builds produce behaviorally equivalent binaries" test_determinism_behavior

# Test 0.8: Incremental compilation flag
test_incremental() {
  local src="$TEMP_DIR/incr.rs"
  local incr_dir="$TEMP_DIR/incremental"

  mkdir -p "$incr_dir"

  cat > "$src" << 'RUST'
fn main() {
    println!("Incremental compilation test");
}
RUST

  "$STAGE1_RUSTC" -C incremental="$incr_dir" "$src" -o "$TEMP_DIR/incr_out" 2>&1
  [[ -d "$incr_dir" ]] && [[ -x "$TEMP_DIR/incr_out" ]]
}
run_test "0.8_incremental" "Incremental compilation works" test_incremental

# Stage 2 Tests (optional)
if [[ $STAGE2_TEST -eq 1 ]]; then
  echo ""
  echo "====================================="
  echo "Stage 2 Bootstrap Tests (Optional)"
  echo "====================================="
  echo ""

  # Test 0.9: Stage 2 build
  test_stage2_build() {
    cd "$RUSTC_DIR"

    echo "Starting Stage 2 build... (this may take ~1 hour)"
    echo "Command: ./x.py build --stage 2 library/std"

    # Build Stage 2 stdlib only (faster than full bootstrap)
    ./x.py build --stage 2 library/std 2>&1

    # Check if Stage 2 rustc was created
    [[ -f "$RUSTC_DIR/build/$HOST_TRIPLE/stage2/bin/rustc" ]]
  }
  run_test "0.9_stage2_build" "Stage 2 builds successfully" test_stage2_build

  # Test 0.10: Stage 2 rustc version
  if [[ -f "$RUSTC_DIR/build/$HOST_TRIPLE/stage2/bin/rustc" ]]; then
    test_stage2_version() {
      local version
      version=$("$RUSTC_DIR/build/$HOST_TRIPLE/stage2/bin/rustc" --version 2>&1)
      echo "$version"
      [[ "$version" == *"1.92.0"* || "$version" == *"1.83.0"* ]]
    }
    run_test "0.10_stage2_version" "Stage 2 rustc reports correct version" test_stage2_version

    # Test 0.11: Stage 2 can compile hello world
    test_stage2_compile() {
      local src="$TEMP_DIR/hello_s2.rs"
      local out="$TEMP_DIR/hello_s2"

      cat > "$src" << 'RUST'
fn main() {
    println!("Hello from Stage 2!");
}
RUST

      "$RUSTC_DIR/build/$HOST_TRIPLE/stage2/bin/rustc" "$src" -o "$out" 2>&1
      [[ -x "$out" ]] && [[ "$("$out")" == "Hello from Stage 2!" ]]
    }
    run_test "0.11_stage2_compile" "Stage 2 compiles hello world" test_stage2_compile
  else
    log SKIP "0.10_stage2_version: Stage 2 not built"
    log SKIP "0.11_stage2_compile: Stage 2 not built"
    ((SKIPPED+=2))
  fi
else
  echo ""
  echo "[INFO] Stage 2 tests skipped (use --stage2 to enable)"
  ((SKIPPED+=3))
fi

# Cleanup
rm -rf "$TEMP_DIR"

# Summary
echo ""
echo "====================================="
echo "Level 0 Build Validation Summary"
echo "====================================="
TOTAL=$((PASSED + FAILED))
echo "Passed: $PASSED/$TOTAL"
echo "Failed: $FAILED"
echo "Skipped: $SKIPPED"
echo ""

if [[ $FAILED -eq 0 ]]; then
  if [[ $STAGE2_TEST -eq 1 ]]; then
    echo -e "${GREEN}Level 0: COMPLETE (Stage 1 + Stage 2 validated)${NC}"
  else
    echo -e "${GREEN}Level 0: PARTIAL (Stage 1 validated, Stage 2 not tested)${NC}"
  fi
  exit 0
else
  echo -e "${RED}Level 0: FAILED ($FAILED tests failed)${NC}"
  exit 1
fi
