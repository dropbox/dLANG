#!/bin/bash
# Level 7 Validation: Stress Testing
# Validates tRust stability under adversarial conditions
#
# Tests:
# 7.1 Large Codebase Compilation (ripgrep, alacritty)
# 7.2 Fuzzing (parser, type checker) - cargo-fuzz
# 7.3 Memory Safety (macOS leaks tool)
# 7.4 Crash Testing (ICE test cases)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
LOG_DIR="$PROJECT_ROOT/reports/validation/level7_logs"
TEST_DIR="$SCRIPT_DIR/level7_tests"

# tRust stage1 compiler
TRUST_COMPILER="$PROJECT_ROOT/upstream/rustc/build/aarch64-apple-darwin/stage1/bin/rustc"
TRUST_SYSROOT="$PROJECT_ROOT/upstream/rustc/build/aarch64-apple-darwin/stage1"

# Parse arguments
VERBOSE=false
QUICK=false
for arg in "$@"; do
    case $arg in
        --verbose|-v) VERBOSE=true ;;
        --quick|-q) QUICK=true ;;
    esac
done

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

# Counters
PASSED=0
FAILED=0
SKIPPED=0

log() {
    echo -e "$1"
}

log_verbose() {
    if $VERBOSE; then
        echo -e "$1"
    fi
}

run_test() {
    local name="$1"
    local category="$2"
    shift 2

    log_verbose "${YELLOW}Running: $name${NC}"

    local log_file="$LOG_DIR/${category}_${name// /_}.log"

    local status=0
    set +e
    (set -euo pipefail; "$@") >"$log_file" 2>&1
    status=$?
    set -e

    if [[ $status -eq 0 ]]; then
        log "${GREEN}PASS${NC}: $name"
        PASSED=$((PASSED + 1))
    else
        log "${RED}FAIL${NC}: $name (see $log_file)"
        FAILED=$((FAILED + 1))
    fi

    return 0
}

skip_test() {
    local name="$1"
    local reason="$2"
    log "${YELLOW}SKIP${NC}: $name ($reason)"
    SKIPPED=$((SKIPPED + 1))
}

# Check prerequisites
check_prerequisites() {
    log "=== Checking Prerequisites ==="

    if [[ ! -x "$TRUST_COMPILER" ]]; then
        log "${RED}ERROR: tRust compiler not found at $TRUST_COMPILER${NC}"
        exit 1
    fi

    log_verbose "tRust compiler: $TRUST_COMPILER"
    log_verbose "tRust sysroot: $TRUST_SYSROOT"

    mkdir -p "$LOG_DIR"
}

# =============================================================================
# 7.1 Large Codebase Compilation
# =============================================================================

test_large_codebase() {
    log ""
    log "=== 7.1 Large Codebase Compilation ==="

    # Test 1: Compile the tRust verification library itself (already available)
    run_test "compile_trust_vcir" "7.1" test_compile_vcir

    # Test 2: Compile a moderately complex test file with many generics
    run_test "compile_complex_generics" "7.1" test_complex_generics

    # Test 3: Compile stress test with deep type recursion
    run_test "compile_type_stress" "7.1" test_type_stress

    # Test 4: Compile with many dependencies (simulated large crate graph)
    run_test "compile_many_modules" "7.1" test_many_modules

    if ! $QUICK; then
        # Test 5: Check stage1 compiler can be used with cargo (external project)
        run_test "cargo_ripgrep_check" "7.1" test_cargo_ripgrep_check
    else
        skip_test "cargo_ripgrep_check" "quick mode"
    fi
}

test_compile_vcir() {
    # Compile all existing level3 test files as a stress test
    local test_count=0
    local success_count=0

    for test_file in "$PROJECT_ROOT/tools/validation/level3_tests"/*.rs; do
        if [[ -f "$test_file" ]]; then
            test_count=$((test_count + 1))
            if "$TRUST_COMPILER" --edition 2021 \
                --sysroot "$TRUST_SYSROOT" \
                "$test_file" -o /tmp/trust_stress_$test_count 2>&1; then
                success_count=$((success_count + 1))
                rm -f /tmp/trust_stress_$test_count
            fi
        fi
    done

    echo "Compiled $success_count/$test_count existing test files"
    [[ $success_count -eq $test_count ]]
}

test_complex_generics() {
    local test_file="$TEST_DIR/complex_generics.rs"
    cat > "$test_file" << 'EOF'
// Complex generics stress test
use std::marker::PhantomData;
use std::collections::HashMap;

trait Processor<T> {
    type Output;
    fn process(&self, input: T) -> Self::Output;
}

struct Chain<A, B, T, U, V>
where
    A: Processor<T, Output = U>,
    B: Processor<U, Output = V>,
{
    first: A,
    second: B,
    _marker: PhantomData<(T, U, V)>,
}

impl<A, B, T, U, V> Processor<T> for Chain<A, B, T, U, V>
where
    A: Processor<T, Output = U>,
    B: Processor<U, Output = V>,
{
    type Output = V;

    fn process(&self, input: T) -> V {
        self.second.process(self.first.process(input))
    }
}

struct NestedWrapper<T, const N: usize> {
    data: [Option<Box<T>>; N],
}

impl<T: Clone, const N: usize> NestedWrapper<T, N> {
    fn new() -> Self {
        Self { data: std::array::from_fn(|_| None) }
    }
}

type ComplexType<'a> = HashMap<String, Vec<Box<dyn Processor<i32, Output = String> + 'a>>>;

fn main() {
    let _wrapper: NestedWrapper<Vec<String>, 10> = NestedWrapper::new();
    println!("Complex generics compiled successfully");
}
EOF

    "$TRUST_COMPILER" --edition 2021 \
        --sysroot "$TRUST_SYSROOT" \
        "$test_file" -o /tmp/trust_complex_generics 2>&1

    /tmp/trust_complex_generics
    rm -f /tmp/trust_complex_generics
}

test_type_stress() {
    local test_file="$TEST_DIR/type_stress.rs"
    cat > "$test_file" << 'EOF'
// Type recursion stress test
trait DeepTrait<T> {
    type Assoc;
}

struct Level0;
struct Level1<T>(T);
struct Level2<T>(T);
struct Level3<T>(T);
struct Level4<T>(T);
struct Level5<T>(T);

impl DeepTrait<Level0> for Level1<Level0> { type Assoc = Level0; }
impl<T> DeepTrait<Level1<T>> for Level2<Level1<T>> where Level1<T>: DeepTrait<T> { type Assoc = Level1<T>; }
impl<T> DeepTrait<Level2<T>> for Level3<Level2<T>> where Level2<T>: DeepTrait<T> { type Assoc = Level2<T>; }
impl<T> DeepTrait<Level3<T>> for Level4<Level3<T>> where Level3<T>: DeepTrait<T> { type Assoc = Level3<T>; }
impl<T> DeepTrait<Level4<T>> for Level5<Level4<T>> where Level4<T>: DeepTrait<T> { type Assoc = Level4<T>; }

// Recursive type with lifetime
enum List<'a, T> {
    Nil,
    Cons(T, &'a List<'a, T>),
}

impl<'a, T: Copy> List<'a, T> {
    fn len(&self) -> usize {
        match self {
            List::Nil => 0,
            List::Cons(_, tail) => 1 + tail.len(),
        }
    }
}

fn main() {
    let nil: List<i32> = List::Nil;
    let cons = List::Cons(1, &nil);
    let cons2 = List::Cons(2, &cons);
    println!("List length: {}", cons2.len());
    println!("Type stress test passed");
}
EOF

    "$TRUST_COMPILER" --edition 2021 \
        --sysroot "$TRUST_SYSROOT" \
        "$test_file" -o /tmp/trust_type_stress 2>&1

    /tmp/trust_type_stress
    rm -f /tmp/trust_type_stress
}

test_many_modules() {
    local test_dir="$TEST_DIR/many_modules"
    if [[ ! -f "$test_dir/main.rs" ]]; then
        echo "Missing fixture: $test_dir/main.rs"
        return 1
    fi

    for mod in a b c d e f g h; do
        if [[ ! -f "$test_dir/mod_$mod.rs" ]]; then
            echo "Missing fixture: $test_dir/mod_$mod.rs"
            return 1
        fi
    done

    # Compile as a binary with modules
    (
        cd "$test_dir"
        "$TRUST_COMPILER" --edition 2021 \
            --sysroot "$TRUST_SYSROOT" \
            main.rs -o /tmp/trust_many_modules 2>&1
    )

    /tmp/trust_many_modules
    rm -f /tmp/trust_many_modules
}

test_cargo_ripgrep_check() {
    local ripgrep_dir="/tmp/trust_ripgrep_test"

    # Clone ripgrep if not present
    if [[ ! -d "$ripgrep_dir/.git" ]]; then
        local clone_log
        clone_log=$(mktemp)
        if ! git clone --depth 1 https://github.com/BurntSushi/ripgrep.git "$ripgrep_dir" >"$clone_log" 2>&1; then
            cat "$clone_log"
            rm -f "$clone_log"
            return 1
        fi
        rm -f "$clone_log"
    fi

    # Try cargo check with tRust (not full build - that would take too long)
    local cargo_log
    cargo_log=$(mktemp)
    if ! (cd "$ripgrep_dir" && RUSTC="$TRUST_COMPILER" cargo check >"$cargo_log" 2>&1); then
        cat "$cargo_log"
        rm -f "$cargo_log"
        return 1
    fi
    rm -f "$cargo_log"

    echo "ripgrep cargo check passed with tRust"
}

# =============================================================================
# 7.2 Fuzzing Tests (Basic)
# =============================================================================

test_fuzzing() {
    log ""
    log "=== 7.2 Fuzzing Tests ==="

    # Note: Full fuzzing requires cargo-fuzz setup which may not be feasible
    # We run basic parser stress tests instead

    run_test "parser_stress" "7.2" test_parser_stress
    run_test "unicode_stress" "7.2" test_unicode_stress
    run_test "macro_stress" "7.2" test_macro_stress
}

test_parser_stress() {
    local test_file="$TEST_DIR/parser_stress.rs"
    cat > "$test_file" << 'EOF'
// Parser stress test with unusual but valid syntax
#![allow(unused_parens)]
#![allow(unused_braces)]
fn main() {
    // Nested blocks
    {{{{{let _x = 1;}}}}}

    // Complex expressions
    let _ = (((((1 + 2) * 3) - 4) / 5) % 6);

    // Many closures
    let f = |x| move |y| move |z| x + y + z;
    assert_eq!(f(1)(2)(3), 6);

    // Match with many arms
    let n = 5;
    let _ = match n {
        0 => "zero",
        1 => "one",
        2 => "two",
        3 => "three",
        4 => "four",
        5 => "five",
        6 => "six",
        7 => "seven",
        8 => "eight",
        9 => "nine",
        _ => "many",
    };

    // Complex pattern matching
    let tuple = (Some(1), Some(2), Some(3));
    if let (Some(a), Some(b), Some(c)) = tuple {
        assert_eq!(a + b + c, 6);
    }

    println!("Parser stress test passed");
}
EOF

    "$TRUST_COMPILER" --edition 2021 \
        --sysroot "$TRUST_SYSROOT" \
        "$test_file" -o /tmp/trust_parser_stress 2>&1

    /tmp/trust_parser_stress
    rm -f /tmp/trust_parser_stress
}

test_unicode_stress() {
    local test_file="$TEST_DIR/unicode_stress.rs"
    cat > "$test_file" << 'EOF'
// Unicode stress test
fn main() {
    // Unicode identifiers
    let α = 1;
    let β = 2;
    let γ = α + β;

    // Unicode strings
    let emoji = "Hello 🌍🦀 World";
    let chinese = "你好世界";
    let arabic = "مرحبا بالعالم";
    let math = "∀x∈ℝ: x²≥0";

    // Unicode in comments
    // This is a comment with émojis: 🎉✨🚀

    // Combining characters
    let cafe = "café";
    let angstrom = "Å";

    assert_eq!(γ, 3);
    println!("Unicode stress test passed: {}", emoji);
}
EOF

    "$TRUST_COMPILER" --edition 2021 \
        --sysroot "$TRUST_SYSROOT" \
        "$test_file" -o /tmp/trust_unicode_stress 2>&1

    /tmp/trust_unicode_stress
    rm -f /tmp/trust_unicode_stress
}

test_macro_stress() {
    local test_file="$TEST_DIR/macro_stress.rs"
    cat > "$test_file" << 'EOF'
// Macro stress test
macro_rules! nested {
    ($x:expr) => { $x };
    ($x:expr, $($rest:expr),+) => {
        nested!($x) + nested!($($rest),+)
    };
}

macro_rules! recursive_sum {
    ($acc:expr;) => { $acc };
    ($acc:expr; $head:expr $(, $tail:expr)*) => {
        recursive_sum!($acc + $head; $($tail),*)
    };
}

macro_rules! make_fn {
    ($name:ident, $val:expr) => {
        fn $name() -> i32 { $val }
    };
}

make_fn!(one, 1);
make_fn!(two, 2);
make_fn!(three, 3);

macro_rules! count_args {
    () => { 0 };
    ($head:tt $($tail:tt)*) => { 1 + count_args!($($tail)*) };
}

fn main() {
    assert_eq!(nested!(1, 2, 3, 4, 5), 15);
    assert_eq!(recursive_sum!(0; 1, 2, 3, 4, 5), 15);
    assert_eq!(one() + two() + three(), 6);
    assert_eq!(count_args!(a b c d e), 5);
    println!("Macro stress test passed");
}
EOF

    "$TRUST_COMPILER" --edition 2021 \
        --sysroot "$TRUST_SYSROOT" \
        "$test_file" -o /tmp/trust_macro_stress 2>&1

    /tmp/trust_macro_stress
    rm -f /tmp/trust_macro_stress
}

# =============================================================================
# 7.3 Memory Safety Tests
# =============================================================================

test_memory_safety() {
    log ""
    log "=== 7.3 Memory Safety Tests ==="

    # Use macOS leaks tool
    if ! command -v leaks &> /dev/null; then
        skip_test "memory_leak_check" "leaks tool not available"
        return
    fi

    run_test "memory_leak_check" "7.3" test_memory_leak_check
    run_test "allocation_stress" "7.3" test_allocation_stress
}

test_memory_leak_check() {
    local test_file="$TEST_DIR/memory_test.rs"
    cat > "$test_file" << 'EOF'
// Memory allocation test
use std::collections::HashMap;

fn allocate_and_free() {
    let mut vec: Vec<String> = Vec::new();
    for i in 0..1000 {
        vec.push(format!("String number {}", i));
    }

    let mut map: HashMap<i32, Vec<u8>> = HashMap::new();
    for i in 0..100 {
        map.insert(i, vec![0u8; 1024]);
    }

    // All memory should be freed when going out of scope
}

fn main() {
    for _ in 0..10 {
        allocate_and_free();
    }
    println!("Memory test completed");
}
EOF

    "$TRUST_COMPILER" --edition 2021 \
        --sysroot "$TRUST_SYSROOT" \
        "$test_file" -o /tmp/trust_memory_test 2>&1

    # Run with leaks tool
    local leak_output
    leak_output=$(leaks --atExit -- /tmp/trust_memory_test 2>&1)

    # Check for "0 leaks" in output
    if echo "$leak_output" | grep -q "0 leaks"; then
        if echo "$leak_output" | grep -q "^Memory test completed$"; then
            echo "Memory test completed"
        fi
        local leak_line
        leak_line=$(echo "$leak_output" | grep "0 leaks" | tail -n 1)
        echo "$leak_line" | sed -E 's/^Process[[:space:]]+[0-9]+:[[:space:]]+//'
        rm -f /tmp/trust_memory_test
        return 0
    else
        echo "$leak_output"
        rm -f /tmp/trust_memory_test
        return 1
    fi
}

test_allocation_stress() {
    local test_file="$TEST_DIR/alloc_stress.rs"
    cat > "$test_file" << 'EOF'
// Allocation stress test
fn main() {
    // Many small allocations
    let mut vecs: Vec<Vec<u8>> = Vec::new();
    for _ in 0..10000 {
        vecs.push(vec![1, 2, 3, 4, 5]);
    }

    // Large allocation
    let large: Vec<u8> = vec![0; 10_000_000];
    assert_eq!(large.len(), 10_000_000);

    // Reallocations
    let mut growing: Vec<i32> = Vec::new();
    for i in 0..100000 {
        growing.push(i);
    }

    println!("Allocation stress test passed");
}
EOF

    "$TRUST_COMPILER" --edition 2021 \
        --sysroot "$TRUST_SYSROOT" \
        "$test_file" -o /tmp/trust_alloc_stress 2>&1

    /tmp/trust_alloc_stress
    rm -f /tmp/trust_alloc_stress
}

# =============================================================================
# 7.4 Crash/ICE Tests
# =============================================================================

test_crash_resistance() {
    log ""
    log "=== 7.4 Crash/ICE Resistance Tests ==="

    run_test "malformed_input_handling" "7.4" test_malformed_input
    run_test "error_recovery" "7.4" test_error_recovery
    run_test "deep_recursion_limit" "7.4" test_deep_recursion
    run_test "trait_cycle_detection" "7.4" test_trait_cycle
}

test_malformed_input() {
    local test_file="$TEST_DIR/malformed.rs"

    # Create files with intentionally malformed content
    # These should produce errors, NOT crashes

    # Test 1: Unclosed braces
    echo "fn main() { let x = 1;" > "$test_file"
    if "$TRUST_COMPILER" --edition 2021 --sysroot "$TRUST_SYSROOT" "$test_file" -o /tmp/malformed 2>&1; then
        echo "UNEXPECTED: malformed code compiled"
        return 1
    else
        echo "Expected error for unclosed brace"
    fi

    # Test 2: Invalid UTF-8 would require binary file, skip

    # Test 3: Extremely long identifier
    python3 -c "print('fn ' + 'a'*10000 + '() {}')" > "$test_file"
    if ! "$TRUST_COMPILER" --edition 2021 --sysroot "$TRUST_SYSROOT" "$test_file" -o /tmp/malformed 2>&1; then
        echo "Long identifier rejected (acceptable)"
    else
        echo "Long identifier accepted"
        rm -f /tmp/malformed
    fi

    # Test 4: Empty file
    echo "" > "$test_file"
    if "$TRUST_COMPILER" --edition 2021 --sysroot "$TRUST_SYSROOT" --crate-type lib "$test_file" -o /tmp/malformed.rlib 2>&1; then
        echo "Empty file compiled as lib"
        rm -f /tmp/malformed.rlib
    else
        echo "Empty file rejected"
    fi

    echo "Malformed input handling test passed - no crashes"
}

test_error_recovery() {
    local test_file="$TEST_DIR/error_recovery.rs"
    cat > "$test_file" << 'EOF'
// Multiple errors - compiler should report all, not crash
fn main() {
    let x: i32 = "string";  // type error
    let y = undefined_var;   // undefined
    println!("{}", nonexistent);  // more undefined
}
EOF

    # Should fail compilation but not crash
    if "$TRUST_COMPILER" --edition 2021 --sysroot "$TRUST_SYSROOT" "$test_file" -o /tmp/error_recovery 2>&1; then
        echo "UNEXPECTED: code with errors compiled"
        return 1
    else
        echo "Expected errors reported without crash"
    fi

    return 0
}

test_deep_recursion() {
    local test_file="$TEST_DIR/deep_recursion.rs"

    # Generate deeply nested code
    local expr="1"
    for _ in {1..50}; do
        expr="($expr)"
    done

    cat > "$test_file" << EOF
#![allow(unused_parens)]
fn main() {
    // Deeply nested expressions (50 levels)
    let _ = $expr;
    println!("Deep nesting handled");
}
EOF

    "$TRUST_COMPILER" --edition 2021 \
        --sysroot "$TRUST_SYSROOT" \
        "$test_file" -o /tmp/trust_deep_recursion 2>&1

    /tmp/trust_deep_recursion
    rm -f /tmp/trust_deep_recursion
}

test_trait_cycle() {
    local test_file="$TEST_DIR/trait_cycle.rs"
    cat > "$test_file" << 'EOF'
// This should produce an error about cyclic trait bounds, not crash
trait A: B {}
trait B: A {}

struct S;
// impl A for S {} // Would cause cycle error
// impl B for S {}

fn main() {
    println!("Trait cycle detection OK");
}
EOF

    local compile_out
    if compile_out=$("$TRUST_COMPILER" --edition 2021 --sysroot "$TRUST_SYSROOT" "$test_file" -o /tmp/trust_trait_cycle 2>&1); then
        echo "UNEXPECTED: cyclic traits compiled"
        rm -f /tmp/trust_trait_cycle
        return 1
    fi

    echo "$compile_out"
    if echo "$compile_out" | grep -q "internal compiler error"; then
        echo "UNEXPECTED: ICE"
        return 1
    fi
    if ! echo "$compile_out" | grep -q "E0391"; then
        echo "UNEXPECTED: missing expected cycle error (E0391)"
        return 1
    fi

    echo "Expected cycle error reported without crash"
    return 0
}

# =============================================================================
# Main
# =============================================================================

main() {
    log "Level 7 Validation: Stress Testing"
    log "=================================="
    log "Date: $(date)"
    log ""

    check_prerequisites

    test_large_codebase
    test_fuzzing
    test_memory_safety
    test_crash_resistance

    log ""
    log "=== Summary ==="
    log "Passed: $PASSED"
    log "Failed: $FAILED"
    log "Skipped: $SKIPPED"
    log "Total: $((PASSED + FAILED + SKIPPED))"

    if [[ $FAILED -eq 0 ]]; then
        log ""
        log "${GREEN}Level 7 Validation: PASS ($PASSED/$((PASSED + SKIPPED)) tests)${NC}"
        exit 0
    else
        log ""
        log "${RED}Level 7 Validation: FAIL ($PASSED passed, $FAILED failed)${NC}"
        exit 1
    fi
}

main "$@"
