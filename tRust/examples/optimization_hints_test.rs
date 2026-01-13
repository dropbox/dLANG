// Optimization Hints Integration Test (Phase 9.0)
//
// This test verifies that tRust tracks proven-safe operations for
// potential optimization. When arithmetic operations are proven safe
// via preconditions, they are recorded in the optimization_hints
// section of the JSON output.
//
// Run with: TRUST_OUTPUT_FORMAT=json trustc -Zverify this_file.rs
// Look for: "optimization_hints" in JSON output
//
// Phase 9 Goals:
// - 9.1: Bounds Check Elimination (use safe_bounds_checks)
// - 9.2: Null Check Elimination (future)
// - 9.3: Overflow Check Elimination (use safe_overflow_checks)
// - 9.4: Specialization Based on Proofs (future)

// === Safe Addition ===
// Precondition constrains inputs so addition cannot overflow
#[requires("a <= 100 && b <= 100")]
#[ensures("result == a + b")]
fn safe_add(a: u8, b: u8) -> u8 {
    // OPTIMIZATION HINT: overflow check can be eliminated
    // Because: a + b <= 200 which fits in u8
    a + b
}

// === Safe Subtraction ===
// Precondition ensures no underflow
#[requires("a >= b")]
#[ensures("result == a - b")]
fn safe_sub(a: u8, b: u8) -> u8 {
    // OPTIMIZATION HINT: underflow check can be eliminated
    // Because: a >= b guarantees non-negative result
    a - b
}

// === Safe Multiplication ===
// Precondition constrains inputs to prevent overflow
#[requires("a <= 15 && b <= 15")]
fn safe_mul(a: u8, b: u8) -> u8 {
    // OPTIMIZATION HINT: overflow check can be eliminated
    // Because: a * b <= 225 which fits in u8
    a * b
}

// === Safe Division ===
// Precondition prevents division by zero
#[requires("b > 0")]
fn safe_div(a: u32, b: u32) -> u32 {
    // OPTIMIZATION HINT: division-by-zero check can be eliminated
    // Because: b > 0 is guaranteed
    a / b
}

// === Safe Modulo ===
// Precondition prevents modulo by zero
#[requires("b > 0")]
fn safe_mod(a: u32, b: u32) -> u32 {
    // OPTIMIZATION HINT: modulo-by-zero check can be eliminated
    // Because: b > 0 is guaranteed
    a % b
}

// === Multiple Operations ===
// Chain of operations all provably safe
#[requires("x <= 50")]
#[ensures("result <= 255")]
fn chain_ops(x: u8) -> u8 {
    // All operations safe due to precondition
    let doubled = x * 2;      // x * 2 <= 100, fits in u8
    let added = doubled + 50; // 100 + 50 = 150, fits in u8
    added
}

// === Array Index (Bounds Check) ===
// Precondition ensures valid array index
#[requires("idx < 10")]
fn safe_index(arr: &[u8; 10], idx: usize) -> u8 {
    // OPTIMIZATION HINT: bounds check can be eliminated
    // Because: idx < 10 and arr.len() == 10
    arr[idx]
}

// === Direct Index with Precondition ===
// Function with explicit bounds precondition
#[requires("idx < 8")]
fn safe_index_direct(arr: &[u8; 8], idx: usize) -> u8 {
    // OPTIMIZATION HINT: bounds check can be eliminated
    // Because: idx < 8 and arr.len() == 8
    arr[idx]
}

fn main() {
    // Test safe arithmetic operations
    assert_eq!(safe_add(50, 50), 100);
    assert_eq!(safe_sub(100, 50), 50);
    assert_eq!(safe_mul(10, 10), 100);
    assert_eq!(safe_div(100, 10), 10);
    assert_eq!(safe_mod(17, 5), 2);
    assert_eq!(chain_ops(25), 100);

    // Test safe array access
    let arr10 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    assert_eq!(safe_index(&arr10, 5), 6);

    let arr8 = [1, 2, 3, 4, 5, 6, 7, 8];
    assert_eq!(safe_index_direct(&arr8, 3), 4);

    println!("All optimization hints tests passed!");
}
