//! Integration test for Phase 12.2 refinement inference for local variables
//!
//! This test verifies that refinement predicates are correctly inferred from:
//! - Constant assignments (let x = 5 → x == 5)
//! - Binary operations with refined operands (let y = x + 1 where x >= 0 → y >= 1)
//!
//! Key features tested:
//! - Constant equality refinement inference
//! - Addition bounds inference
//! - Subtraction bounds inference
//! - Multiplication bounds inference (non-negative preservation)
//!
//! Note: Inferred refinements are reported in verbose output with:
//! "[tRust] Phase 12.2: Tracked N refinement(s) through assignments"

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Constant refinement inference
// ============================================================================

/// Simple constant assignment: let x = 5 → x == 5
#[ensures("result == 5")]
fn constant_five() -> i32 {
    let x = 5;  // Inferred: x == 5
    x           // result == 5
}

/// Constant zero: let x = 0 → x == 0
#[ensures("result == 0")]
fn constant_zero() -> i32 {
    let x = 0;  // Inferred: x == 0
    x           // result == 0
}

/// Negative constant: let x = -10 → x == -10
#[ensures("result == -10")]
fn constant_negative() -> i32 {
    let x = -10;  // Inferred: x == -10
    x             // result == -10
}

/// Large constant: let x = 1000000 → x == 1000000
#[ensures("result == 1000000")]
fn constant_large() -> i64 {
    let x: i64 = 1_000_000;  // Inferred: x == 1000000
    x                        // result == 1000000
}

// ============================================================================
// Part 2: Binary operation inference with constants (bounded ranges)
// ============================================================================

/// Addition with constant: refined + const
/// If n >= 0 and n < 100, we can safely add 1 and result >= 1
#[trust::refined(n, "n >= 0 && n < 100")]
#[requires("n >= 0 && n < 100")]  // Explicit for automatic overflow checker
#[ensures("result >= 1")]
fn add_one_to_nonnegative(n: i32) -> i32 {
    let x = n;      // x >= 0 && x < 100 (propagated)
    let y = x + 1;  // Inferred: y >= 1 (from x >= 0 + 1)
    y               // result >= 1
}

/// Addition with larger constant
/// If n >= 5 and n < 100, we add 10 and result >= 15
#[trust::refined(n, "n >= 5 && n < 100")]
#[requires("n >= 5 && n < 100")]  // Explicit for automatic overflow checker
#[ensures("result >= 15")]
fn add_ten_to_bounded(n: i32) -> i32 {
    let x = n;       // x >= 5 && x < 100 (propagated)
    let y = x + 10;  // Inferred: y >= 15
    y                // result >= 15
}

/// Subtraction with constant (safe: n >= 10 ensures no underflow)
#[trust::refined(n, "n >= 10 && n < 100")]
#[requires("n >= 10 && n < 100")]  // Explicit for automatic overflow checker
#[ensures("result >= 5")]
fn subtract_five_from_bounded(n: i32) -> i32 {
    let x = n;      // x >= 10 && x < 100 (propagated)
    let y = x - 5;  // Inferred: y >= 5 (safe: 10 - 5 = 5 min)
    y               // result >= 5
}

// ============================================================================
// Part 3: Two-operand binary operations (bounded)
// ============================================================================

/// Addition of two bounded non-negative values
#[trust::refined(a, "a >= 0 && a < 1000")]
#[trust::refined(b, "b >= 0 && b < 1000")]
#[requires("a >= 0 && a < 1000 && b >= 0 && b < 1000")]  // Overflow prevention
#[ensures("result >= 0")]
fn add_two_nonnegative(a: i32, b: i32) -> i32 {
    let x = a;      // x >= 0 && x < 1000
    let y = b;      // y >= 0 && y < 1000
    let z = x + y;  // Inferred: z >= 0 (both operands non-negative, sum < 2000)
    z               // result >= 0
}

/// Multiplication of two small non-negative values
#[trust::refined(a, "a >= 0 && a < 100")]
#[trust::refined(b, "b >= 0 && b < 100")]
#[requires("a >= 0 && a < 100 && b >= 0 && b < 100")]  // Overflow prevention
#[ensures("result >= 0")]
fn multiply_two_nonnegative(a: i32, b: i32) -> i32 {
    let x = a;      // x >= 0 && x < 100
    let y = b;      // y >= 0 && y < 100
    let z = x * y;  // Inferred: z >= 0 (product of non-negatives < 10000)
    z               // result >= 0
}

// ============================================================================
// Part 4: Chained operations (bounded)
// ============================================================================

/// Chained addition: x + 1 + 1
#[trust::refined(n, "n >= 0 && n < 100")]
#[requires("n >= 0 && n < 100")]  // Explicit for automatic overflow checker
#[ensures("result >= 2")]
fn add_one_twice(n: i32) -> i32 {
    let x = n;       // x >= 0 && x < 100
    let y = x + 1;   // Inferred: y >= 1
    let z = y + 1;   // Inferred: z >= 2
    z                // result >= 2
}

/// Mixed operations: (n + 5) - 3
#[trust::refined(n, "n >= 0 && n < 100")]
#[requires("n >= 0 && n < 100")]  // Explicit for automatic overflow checker
#[ensures("result >= 2")]
fn add_then_subtract(n: i32) -> i32 {
    let x = n;       // x >= 0 && x < 100
    let y = x + 5;   // Inferred: y >= 5
    let z = y - 3;   // Inferred: z >= 2 (safe: y >= 5, so y - 3 >= 2)
    z                // result >= 2
}

// ============================================================================
// Part 5: Unsigned integers (bounded)
// ============================================================================

/// Unsigned addition with constant
#[trust::refined(n, "n >= 10 && n < 1000")]
#[requires("n >= 10 && n < 1000")]  // Explicit for automatic overflow checker
#[ensures("result >= 15")]
fn unsigned_add(n: usize) -> usize {
    let x = n;      // x >= 10 && x < 1000
    let y = x + 5;  // Inferred: y >= 15
    y               // result >= 15
}

/// Unsigned constant
#[ensures("result == 42")]
fn unsigned_constant() -> usize {
    let x: usize = 42;  // Inferred: x == 42
    x                   // result == 42
}

// ============================================================================
// Part 6: Upper bounds (bounded to prevent overflow)
// ============================================================================

/// Upper bound propagation through addition
#[trust::refined(n, "n >= 0 && n <= 10")]
#[requires("n >= 0 && n <= 10")]  // Explicit for automatic overflow checker
#[ensures("result <= 15")]
fn upper_bound_add(n: i32) -> i32 {
    let x = n;      // 0 <= x <= 10
    let y = x + 5;  // Inferred: y <= 15 (max = 10 + 5 = 15)
    y               // result <= 15
}

/// Upper bound with strict inequality
#[trust::refined(n, "n >= 0 && n < 10")]
#[requires("n >= 0 && n < 10")]  // Explicit for automatic overflow checker
#[ensures("result <= 14")]
fn strict_upper_bound_add(n: i32) -> i32 {
    let x = n;      // 0 <= x < 10 → x <= 9
    let y = x + 5;  // Inferred: y <= 14 (max = 9 + 5 = 14)
    y               // result <= 14
}

// ============================================================================
// Part 7: Scale by constant (bounded to prevent overflow)
// ============================================================================

/// Multiply by positive constant preserves bounds
#[trust::refined(n, "n >= 5 && n < 1000")]
#[requires("n >= 5 && n < 1000")]  // Explicit for automatic overflow checker
#[ensures("result >= 10")]
fn scale_by_two(n: i32) -> i32 {
    let x = n;      // 5 <= x < 1000
    let y = x * 2;  // Inferred: y >= 10 (min = 5 * 2 = 10, max < 2000)
    y               // result >= 10
}

fn main() {
    // Part 1: Constant inference
    assert_eq!(constant_five(), 5);
    assert_eq!(constant_zero(), 0);
    assert_eq!(constant_negative(), -10);
    assert_eq!(constant_large(), 1_000_000);

    // Part 2: Binary ops with constants
    assert!(add_one_to_nonnegative(0) >= 1);
    assert!(add_one_to_nonnegative(10) >= 1);
    assert!(add_ten_to_bounded(5) >= 15);
    assert!(subtract_five_from_bounded(10) >= 5);

    // Part 3: Two-operand ops
    assert!(add_two_nonnegative(3, 7) >= 0);
    assert!(multiply_two_nonnegative(4, 5) >= 0);

    // Part 4: Chained ops
    assert!(add_one_twice(0) >= 2);
    assert!(add_then_subtract(0) >= 2);

    // Part 5: Unsigned
    assert!(unsigned_add(10) >= 15);
    assert_eq!(unsigned_constant(), 42);

    // Part 6: Upper bounds
    assert!(upper_bound_add(5) <= 15);
    assert!(strict_upper_bound_add(5) <= 14);

    // Part 7: Scale
    assert!(scale_by_two(5) >= 10);

    println!("Phase 12.2: All refinement inference tests passed!");
}
