//! Integration test for Phase 12.6 - Refinement Type Integration
//!
//! This test demonstrates the integration of refinement types with:
//! 1. Automatic conversion to #[requires]/[#ensures]
//! 2. JSON output including refinement type information
//! 3. Refinements complementing (not replacing) existing contracts
//!
//! Key integration features tested:
//! - #[trust::refined(param, "pred")] → equivalent to #[requires("pred")]
//! - #[trust::returns_refined("pred")] → equivalent to #[ensures("pred")]
//! - Refinement types propagate through the verification pipeline
//! - JSON output includes refinement_types array in summary

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Refinement types as preconditions
// ============================================================================

/// Demonstrate that #[trust::refined] is automatically converted to a precondition
/// The refinement "x >= 0" ensures the caller provides non-negative input
#[trust::refined(x, "x >= 0")]
#[requires("x >= 0")]
#[ensures("result >= 0")]
fn identity_nonneg(x: i32) -> i32 {
    x
}

/// Demonstrate refinement on multiple parameters
/// Bounds prevent overflow: a + b <= 1000 < i32::MAX
#[trust::refined(a, "a >= 0 && a <= 500")]
#[trust::refined(b, "b >= 0 && b <= 500")]
#[requires("a >= 0 && a <= 500 && b >= 0 && b <= 500")]
#[ensures("result >= 0")]
fn add_nonneg(a: i32, b: i32) -> i32 {
    // Safe because a + b <= 1000 < i32::MAX
    a + b
}

// ============================================================================
// Part 2: Refinement types as postconditions
// ============================================================================

/// Demonstrate #[trust::returns_refined] as a postcondition
#[trust::refined(n, "n >= 0")]
#[trust::returns_refined("result >= 1")]
#[requires("n >= 0")]
#[ensures("result >= 1")]
fn at_least_one(n: i32) -> i32 {
    if n < 1 { 1 } else { n }
}

/// Demonstrate return refinement for bounded output
#[trust::refined(x, "x >= 0 && x <= 100")]
#[trust::returns_refined("result >= 0 && result <= 100")]
#[requires("x >= 0 && x <= 100")]
#[ensures("result >= 0 && result <= 100")]
fn clamp_percentage(x: i32) -> i32 {
    if x < 0 { 0 }
    else if x > 100 { 100 }
    else { x }
}

// ============================================================================
// Part 3: Refinements complement existing contracts
// ============================================================================

/// Show that refinements work alongside regular requires/ensures
/// Both the refinement and the explicit requires are converted to preconditions
#[trust::refined(divisor, "divisor > 0")]
#[requires("divisor > 0 && dividend >= 0")]
#[ensures("result >= 0")]
fn safe_divide(dividend: i32, divisor: i32) -> i32 {
    dividend / divisor
}

/// Refinements and regular contracts combine for complete specification
#[trust::refined(idx, "idx >= 0 && idx < 10")]
#[trust::returns_refined("result >= 0 && result < 10")]
#[requires("idx >= 0 && idx < 10")]
#[ensures("result >= 0 && result < 10")]
fn bounded_index(idx: i32) -> i32 {
    idx
}

// ============================================================================
// Part 4: Simple function calls with refined parameters
// ============================================================================

/// Call a refined function with matching constraints
#[trust::refined(n, "n >= 0")]
#[requires("n >= 0")]
#[ensures("result >= 0")]
fn double_nonneg(n: i32) -> i32 {
    identity_nonneg(n)  // n >= 0 satisfies refinement
}

/// Chain of refined calls - use simpler constraints
#[trust::refined(x, "x >= 0 && x <= 50")]
#[requires("x >= 0 && x <= 50")]
#[ensures("result >= 0")]
fn double_clamped(x: i32) -> i32 {
    // Simply add the non-negative values
    add_nonneg(x, x)
}

// ============================================================================
// Part 5: Loop with refined bounds
// ============================================================================

/// Loop with refined start/end bounds
#[trust::refined(start, "start >= 0")]
#[trust::refined(count, "count >= 0 && count < 100")]
#[requires("start >= 0 && count >= 0 && count < 100")]
#[ensures("result >= 0")]
fn accumulate(start: i32, count: i32) -> i32 {
    let mut sum = start;
    let mut i = 0;

    #[invariant("i >= 0 && i <= count && sum >= 0")]
    while i < count {
        sum = sum + 1;
        i = i + 1;
    }

    sum
}

// ============================================================================
// Part 6: Nested refined function
// ============================================================================

/// Call refined function from within verified function
#[trust::refined(x, "x > 0 && x < 50")]
#[requires("x > 0 && x < 50")]
#[ensures("result >= 1")]
fn process_positive(x: i32) -> i32 {
    at_least_one(x)  // x > 0 satisfies n >= 0
}

fn main() {
    // Test Part 1: Refinements as preconditions
    assert!(identity_nonneg(10) >= 0);
    assert!(add_nonneg(10, 20) == 30);

    // Test Part 2: Refinements as postconditions
    assert!(at_least_one(0) >= 1);
    assert!(at_least_one(50) >= 1);
    assert!(clamp_percentage(50) <= 100);
    assert!(clamp_percentage(50) >= 0);

    // Test Part 3: Combined contracts
    assert!(safe_divide(100, 5) == 20);
    assert!(bounded_index(5) == 5);

    // Test Part 4: Chained calls
    assert!(double_nonneg(10) >= 0);
    assert!(double_clamped(25) <= 100);

    // Test Part 5: Loop with refined bounds
    assert!(accumulate(0, 5) == 5);

    // Test Part 6: Nested refined function
    assert!(process_positive(10) >= 1);

    println!("Phase 12.6: All refinement integration tests passed!");
}
