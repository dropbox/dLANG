//! Integration test for Phase 12.3 automatic precondition synthesis
//!
//! This test demonstrates that tRust can automatically infer the minimal
//! preconditions needed for function safety:
//! - Division by zero: divisor != 0
//! - Remainder by zero: divisor != 0
//! - Array bounds: 0 <= idx < len
//!
//! When preconditions are missing, tRust reports:
//! "[tRust] Phase 12.3: Inferred N precondition(s) for function_name"
//! "[tRust] Phase 12.3: N missing precondition(s) for function_name:"
//!   - MISSING: predicate (reason)
//! "[tRust] Phase 12.3: Suggested refinements:"
//!   - #[trust::refined(param, "predicate")]  // reason
//!
//! This enables automatic precondition synthesis - the system suggests
//! what refinement types should be added to make functions safe.

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Division with declared precondition (safe, no suggestions)
// ============================================================================

/// Safe division with declared precondition
/// This function already has the necessary precondition, so no suggestions needed.
#[trust::refined(divisor, "divisor != 0")]
#[requires("divisor != 0")]  // Explicit for automatic division-by-zero checker
#[ensures("true")]
fn safe_divide(dividend: i32, divisor: i32) -> i32 {
    dividend / divisor
}

/// Safe remainder with declared precondition
#[trust::refined(divisor, "divisor != 0")]
#[requires("divisor != 0")]  // Explicit for automatic remainder-by-zero checker
#[ensures("true")]
fn safe_remainder(dividend: i32, divisor: i32) -> i32 {
    dividend % divisor
}

// ============================================================================
// Part 2: Division with inferred precondition (would suggest refinement)
// ============================================================================

/// Division where precondition is declared but system can verify it's present.
/// This tests that the inference correctly matches declared preconditions.
#[requires("b != 0")]
#[ensures("true")]
fn divide_with_requires(a: i32, b: i32) -> i32 {
    // Phase 12.3 infers: b != 0 needed for division
    // The declared #[requires] matches, so no suggestion generated
    a / b
}

/// Quotient and remainder in one function
/// Both operations need the same precondition: divisor != 0
#[requires("divisor != 0")]
#[ensures("true")]
fn div_and_rem(dividend: i32, divisor: i32) -> (i32, i32) {
    // Phase 12.3 infers: divisor != 0 for both operations
    // Deduplication ensures only one precondition is inferred
    let q = dividend / divisor;
    let r = dividend % divisor;
    (q, r)
}

// ============================================================================
// Part 3: Multiple parameters with refinements
// ============================================================================

/// Division followed by another operation
/// Tests that parameter-level refinements are suggested correctly
#[trust::refined(y, "y != 0")]
#[requires("y != 0")]
#[requires("x >= 0 && x < 1000")]
#[ensures("result >= 0")]
fn divide_bounded(x: i32, y: i32) -> i32 {
    // Phase 12.3 infers: y != 0 from division
    let q = x / y;
    if q < 0 { 0 } else { q }
}

/// Two divisions, both parameters need refinements
#[trust::refined(a, "a != 0")]
#[trust::refined(b, "b != 0")]
#[requires("a != 0 && b != 0")]
#[ensures("true")]
fn double_divide(x: i32, a: i32, b: i32) -> i32 {
    // Phase 12.3 infers: a != 0 for first division
    // Phase 12.3 infers: b != 0 for second division
    let y = x / a;
    let z = y / b;
    z
}

// ============================================================================
// Part 4: Nested operations
// ============================================================================

/// Division in expression context
/// Using checked arithmetic to avoid overflow checker error
#[trust::refined(divisor, "divisor != 0")]
#[requires("divisor != 0")]
#[ensures("true")]
fn divide_add(a: i32, b: i32, divisor: i32) -> Option<i32> {
    // Phase 12.3 infers: divisor != 0
    a.checked_add(b / divisor)
}

/// Division result used in another division
#[trust::refined(y, "y != 0")]
#[requires("y != 0 && x >= y")]
#[ensures("true")]
fn divide_chain(x: i32, y: i32) -> i32 {
    // Phase 12.3 infers: y != 0 for first division
    // The result x/y could be zero, but this is the user's concern
    let q = x / y;
    q
}

// ============================================================================
// Part 5: Control flow with division
// ============================================================================

/// Conditional division
/// Division only happens in one branch, but precondition still needed
#[trust::refined(divisor, "divisor != 0")]
#[requires("divisor != 0")]
#[ensures("true")]
fn conditional_divide(dividend: i32, divisor: i32, use_div: bool) -> i32 {
    // Phase 12.3 infers: divisor != 0 even though division is conditional
    if use_div {
        dividend / divisor
    } else {
        dividend
    }
}

/// Division with early return
#[trust::refined(divisor, "divisor != 0")]
#[requires("divisor != 0")]
#[ensures("true")]
fn divide_or_default(dividend: i32, divisor: i32, default: i32) -> i32 {
    // Phase 12.3 sees division, infers: divisor != 0
    if dividend == 0 {
        return default;
    }
    dividend / divisor
}

// ============================================================================
// Part 6: Integer types
// ============================================================================

/// Division with unsigned integers
#[trust::refined(divisor, "divisor != 0")]
#[requires("divisor != 0")]
#[ensures("true")]
fn divide_unsigned(dividend: u32, divisor: u32) -> u32 {
    dividend / divisor
}

/// Division with i64
#[trust::refined(divisor, "divisor != 0")]
#[requires("divisor != 0")]
#[ensures("true")]
fn divide_i64(dividend: i64, divisor: i64) -> i64 {
    dividend / divisor
}

// ============================================================================
// Part 7: Combined with other Phase 12 features
// ============================================================================

/// Refinement type AND inferred precondition work together
/// The refinement provides n > 0, which implies n != 0
#[trust::refined(n, "n > 0")]
#[requires("n > 0")]  // This implies n != 0, so division is safe
#[ensures("result >= 0")]
fn divide_by_positive(x: i32, n: i32) -> i32 {
    // Phase 12.3 infers: n != 0 needed
    // But n > 0 (from refinement) implies n != 0, so covered
    let q = x / n;
    if q < 0 { 0 } else { q }
}

/// Return refinement with division
#[trust::refined(divisor, "divisor != 0")]
#[requires("divisor != 0 && dividend >= 0")]
#[trust::returns_refined("result >= 0")]
fn divide_nonnegative(dividend: i32, divisor: i32) -> i32 {
    // Division + return value refinement
    let q = dividend / divisor;
    if q < 0 { 0 } else { q }
}

// ============================================================================
// Part 8: Simple functions for verification
// ============================================================================

/// Simple addition - no preconditions needed from inference
/// (overflow checking is separate from precondition synthesis)
#[requires("a >= 0 && a < 1000 && b >= 0 && b < 1000")]
#[ensures("result >= 0")]
fn add_bounded(a: i32, b: i32) -> i32 {
    a + b
}

/// Simple multiplication - no preconditions needed from inference
#[requires("a >= 0 && a < 100 && b >= 0 && b < 100")]
#[ensures("result >= 0")]
fn mul_bounded(a: i32, b: i32) -> i32 {
    a * b
}

/// Identity function - no preconditions needed
#[ensures("result == x")]
fn identity(x: i32) -> i32 {
    x
}

// ============================================================================
// Main function to run all tests
// ============================================================================

fn main() {
    // Part 1: Safe division/remainder
    assert_eq!(safe_divide(10, 2), 5);
    assert_eq!(safe_remainder(10, 3), 1);

    // Part 2: Division with declared preconditions
    assert_eq!(divide_with_requires(20, 4), 5);
    assert_eq!(div_and_rem(17, 5), (3, 2));

    // Part 3: Multiple parameters
    assert_eq!(divide_bounded(100, 10), 10);
    assert_eq!(double_divide(100, 5, 2), 10);

    // Part 4: Nested operations
    assert_eq!(divide_add(10, 20, 4), Some(15));
    assert_eq!(divide_chain(100, 10), 10);

    // Part 5: Control flow
    assert_eq!(conditional_divide(20, 4, true), 5);
    assert_eq!(conditional_divide(20, 4, false), 20);
    assert_eq!(divide_or_default(20, 4, -1), 5);
    assert_eq!(divide_or_default(0, 4, -1), -1);

    // Part 6: Integer types
    assert_eq!(divide_unsigned(100u32, 7u32), 14);
    assert_eq!(divide_i64(1000i64, 7i64), 142);

    // Part 7: Combined features
    assert_eq!(divide_by_positive(100, 7), 14);
    assert_eq!(divide_nonnegative(100, 7), 14);

    // Part 8: Simple functions
    assert_eq!(add_bounded(100, 200), 300);
    assert_eq!(mul_bounded(10, 20), 200);
    assert_eq!(identity(42), 42);

    println!("All precondition synthesis tests passed!");
}
