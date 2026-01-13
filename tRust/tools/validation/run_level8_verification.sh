#!/bin/bash
#
# Level 8 Validation: Verification Advantage
#
# Tests:
#   8.1 Bug Detection - tRust catches bugs rustc misses
#   8.2 Verification Performance - Overhead is reasonable
#   8.3 False Positive Rate - Verification accepts valid code
#   8.4 Spec Coverage - Contract verification works correctly
#

set +e  # Don't exit on error

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$SCRIPT_DIR/../.."
UPSTREAM_SYSROOT="$PROJECT_ROOT/upstream/rustc/build/host/stage1"
SYSROOT="${TRUST_SYSROOT:-$UPSTREAM_SYSROOT}"
TRUST_RUSTC="$SYSROOT/bin/rustc"
SYSTEM_RUSTC="$(which rustc)"
TMPDIR=$(mktemp -d)
trap "rm -rf $TMPDIR" EXIT

TIMEOUT_CMD="timeout 30"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

VERBOSE=false
[ "$1" == "--verbose" ] || [ "$1" == "-v" ] && VERBOSE=true

passed=0
failed=0
total=0

log() { $VERBOSE && echo "$@"; }
test_pass() { echo -e "${GREEN}PASS${NC}: $1"; passed=$((passed + 1)); total=$((total + 1)); }
test_fail() { echo -e "${RED}FAIL${NC}: $1"; [ -n "$2" ] && echo "       $2"; failed=$((failed + 1)); total=$((total + 1)); }

echo "========================================"
echo "Level 8: Verification Advantage"
echo "========================================"
echo ""

# Check tRust is available
if [ ! -x "$TRUST_RUSTC" ]; then
    echo "Error: tRust not found at $TRUST_RUSTC"
    exit 1
fi

# =============================================================================
# 8.1 Bug Detection
# =============================================================================
echo "--- 8.1 Bug Detection ---"

# Helper: compile with rustc, should succeed
rustc_ok() {
    $TIMEOUT_CMD $SYSTEM_RUSTC "$1" --edition 2021 -o "$TMPDIR/rustc_out" 2>/dev/null
}

# Helper: compile with tRust -Zverify, should fail
trust_should_fail() {
    $TIMEOUT_CMD $TRUST_RUSTC "$1" --edition 2021 -Zverify -o "$TMPDIR/trust_out" 2>"$TMPDIR/err.txt"
    [ $? -ne 0 ]
}

# Test 8.1.1: Overflow
cat > "$TMPDIR/test.rs" << 'EOF'
fn add_overflow(a: u8, b: u8) -> u8 { a + b }
fn main() {}
EOF
if rustc_ok "$TMPDIR/test.rs" && trust_should_fail "$TMPDIR/test.rs"; then
    test_pass "8.1.1 Overflow detection"
else
    test_fail "8.1.1 Overflow detection" "tRust should detect overflow bug"
fi

# Test 8.1.2: Bounds
cat > "$TMPDIR/test.rs" << 'EOF'
fn get_elem(arr: &[i32; 3], i: usize) -> i32 { arr[i] }
fn main() {}
EOF
if rustc_ok "$TMPDIR/test.rs" && trust_should_fail "$TMPDIR/test.rs"; then
    test_pass "8.1.2 Bounds detection"
else
    test_fail "8.1.2 Bounds detection" "tRust should detect bounds bug"
fi

# Test 8.1.3: Division by zero
cat > "$TMPDIR/test.rs" << 'EOF'
fn divide(a: u32, b: u32) -> u32 { a / b }
fn main() {}
EOF
if rustc_ok "$TMPDIR/test.rs" && trust_should_fail "$TMPDIR/test.rs"; then
    test_pass "8.1.3 Division-by-zero detection"
else
    test_fail "8.1.3 Division-by-zero detection" "tRust should detect divzero bug"
fi

# Test 8.1.4: Contract violation (tRust-specific #[ensures] - rustc ignores it)
cat > "$TMPDIR/test.rs" << 'EOF'
#[ensures("result >= 0")]
fn abs_buggy(x: i32) -> i32 { x }
fn main() {}
EOF
# Only tRust understands #[ensures], so only check tRust
if trust_should_fail "$TMPDIR/test.rs"; then
    test_pass "8.1.4 Contract verification"
else
    test_fail "8.1.4 Contract verification" "tRust should detect contract violation"
fi

echo ""

# =============================================================================
# 8.2 Verification Performance
# =============================================================================
echo "--- 8.2 Verification Performance ---"

cat > "$TMPDIR/perf.rs" << 'EOF'
#[requires("x >= 0")]
#[ensures("result >= x")]
fn identity_pos(x: i32) -> i32 { x }
#[requires("a < 100 && b < 100")]
fn safe_add(a: u8, b: u8) -> u8 { a + b }
#[requires("b != 0")]
fn safe_div(a: u32, b: u32) -> u32 { a / b }
fn main() {}
EOF

# Time without verification
t1=$(python3 -c "import time; print(time.time())")
$TIMEOUT_CMD $TRUST_RUSTC "$TMPDIR/perf.rs" --edition 2021 -o "$TMPDIR/perf1" 2>/dev/null
t2=$(python3 -c "import time; print(time.time())")
no_verify=$(python3 -c "print($t2 - $t1)")

# Time with verification
t1=$(python3 -c "import time; print(time.time())")
$TIMEOUT_CMD $TRUST_RUSTC "$TMPDIR/perf.rs" --edition 2021 -Zverify -o "$TMPDIR/perf2" 2>/dev/null
t2=$(python3 -c "import time; print(time.time())")
with_verify=$(python3 -c "print($t2 - $t1)")

overhead=$(python3 -c "print(round(($with_verify / $no_verify - 1) * 100, 1) if $no_verify > 0.001 else 0)")
log "  Without verification: ${no_verify}s"
log "  With verification: ${with_verify}s"
log "  Overhead: ${overhead}%"

# Accept up to 200% overhead
if python3 -c "exit(0 if $overhead < 200 else 1)"; then
    test_pass "8.2.1 Verification overhead (${overhead}%)"
else
    test_fail "8.2.1 Verification overhead" "${overhead}% exceeds 200%"
fi

echo ""

# =============================================================================
# 8.3 False Positive Rate
# =============================================================================
echo "--- 8.3 False Positive Rate ---"

# Helper: compile with tRust -Zverify, should succeed
trust_should_pass() {
    $TIMEOUT_CMD $TRUST_RUSTC "$1" --edition 2021 -Zverify -o "$TMPDIR/trust_out" 2>"$TMPDIR/err.txt"
    [ $? -eq 0 ]
}

# Test 8.3.1: Safe contracted code
cat > "$TMPDIR/test.rs" << 'EOF'
#[requires("a < 100 && b < 100")]
fn safe_add(a: u8, b: u8) -> u8 { a + b }
#[requires("b <= a")]
fn safe_sub(a: u8, b: u8) -> u8 { a - b }
#[requires("b != 0")]
fn safe_div(a: u32, b: u32) -> u32 { a / b }
fn main() {}
EOF
if trust_should_pass "$TMPDIR/test.rs"; then
    test_pass "8.3.1 Safe contracted code"
else
    test_fail "8.3.1 Safe contracted code" "False positive on valid code"
fi

# Test 8.3.2: Path-sensitive safe code
cat > "$TMPDIR/test.rs" << 'EOF'
fn safe_add_guarded(a: u8, b: u8) -> u8 {
    if a < 100 && b < 100 { a + b } else { 0 }
}
fn safe_index_guarded(arr: &[i32; 3], i: usize) -> i32 {
    if i < 3 { arr[i] } else { 0 }
}
fn main() {}
EOF
if trust_should_pass "$TMPDIR/test.rs"; then
    test_pass "8.3.2 Path-sensitive safe code"
else
    test_fail "8.3.2 Path-sensitive safe code" "False positive on valid code"
fi

# Test 8.3.3: Checked operations
cat > "$TMPDIR/test.rs" << 'EOF'
fn safe_checked_add(a: u8, b: u8) -> Option<u8> { a.checked_add(b) }
fn safe_get(arr: &[i32], i: usize) -> Option<&i32> { arr.get(i) }
fn main() {}
EOF
if trust_should_pass "$TMPDIR/test.rs"; then
    test_pass "8.3.3 Checked operations"
else
    test_fail "8.3.3 Checked operations" "False positive on valid code"
fi

echo ""

# =============================================================================
# 8.4 Specification Coverage
# =============================================================================
echo "--- 8.4 Specification Coverage ---"

# Test 8.4.1: #[requires] parsing
cat > "$TMPDIR/test.rs" << 'EOF'
#[requires("n > 0")]
fn positive_only(n: i32) -> i32 { n }
fn main() {}
EOF
if trust_should_pass "$TMPDIR/test.rs"; then
    test_pass "8.4.1 #[requires] parsing"
else
    test_fail "8.4.1 #[requires] parsing" "Failed to parse requires"
fi

# Test 8.4.2: #[ensures] parsing
# Note: We use a simple provable example. The abs() example in the book
# intentionally has a bug (i32::MIN overflow) and is correctly rejected.
cat > "$TMPDIR/test.rs" << 'EOF'
#[ensures("result == 42")]
fn return_42() -> i32 { 42 }
fn main() {}
EOF
if trust_should_pass "$TMPDIR/test.rs"; then
    test_pass "8.4.2 #[ensures] parsing"
else
    test_fail "8.4.2 #[ensures] parsing" "Failed to parse ensures"
fi

# Test 8.4.3: Combined requires/ensures
cat > "$TMPDIR/test.rs" << 'EOF'
#[requires("x >= 0")]
#[ensures("result >= x")]
fn identity_nonneg(x: i32) -> i32 { x }
fn main() {}
EOF
if trust_should_pass "$TMPDIR/test.rs"; then
    test_pass "8.4.3 Combined requires/ensures"
else
    test_fail "8.4.3 Combined requires/ensures" "Failed combined verification"
fi

# Test 8.4.4: Wrong postcondition should fail
cat > "$TMPDIR/test.rs" << 'EOF'
#[ensures("result > 100")]
fn identity_wrong(x: i32) -> i32 { x }
fn main() {}
EOF
if trust_should_fail "$TMPDIR/test.rs"; then
    test_pass "8.4.4 Wrong postcondition detection"
else
    test_fail "8.4.4 Wrong postcondition detection" "Should reject wrong postcondition"
fi

echo ""

# =============================================================================
# Summary
# =============================================================================
echo "========================================"
echo "Level 8 Summary: $passed/$total passed"
echo "========================================"

if [ $failed -eq 0 ]; then
    echo -e "${GREEN}LEVEL 8: ALL TESTS PASSED${NC}"
    exit 0
else
    echo -e "${YELLOW}LEVEL 8: $failed TESTS FAILED${NC}"
    exit 1
fi
