//! Integration test for Phase 12.4 - Refinement Type Inference
//!
//! This test demonstrates the constraint-based refinement type inference system
//! inspired by Liquid Types. The inference engine:
//!
//! 1. Assigns refinement variables to program points
//! 2. Generates constraints from program structure
//! 3. Solves constraints to infer refinement predicates
//!
//! Key features tested:
//! - Qualifier-based refinement inference
//! - Constraint propagation through assignments
//! - Loop invariant inference candidates
//! - Integration with existing refinement tracking

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Basic refinement inference
// ============================================================================

/// Test that constants get equality refinements inferred
/// Inference: let x = 5 → x == 5
#[ensures("result == 5")]
fn constant_refinement_inference() -> i32 {
    let x = 5;  // Inference engine assigns κ_x = "x == 5"
    x           // result == 5
}

/// Test that non-negative bounds are inferred
/// Inference: x >= 0 && y >= 0 → x + y >= 0
#[trust::refined(a, "a >= 0 && a < 1000")]
#[trust::refined(b, "b >= 0 && b < 1000")]
#[requires("a >= 0 && a < 1000 && b >= 0 && b < 1000")]
#[ensures("result >= 0")]
fn sum_nonnegative_inference(a: i32, b: i32) -> i32 {
    let x = a;      // κ_x = "x >= 0" (from refined param)
    let y = b;      // κ_y = "y >= 0" (from refined param)
    let z = x + y;  // Constraint: κ_z >= 0 (sum of non-negatives)
    z               // result >= 0
}

/// Test bound propagation through addition
/// Inference: x >= 5 and y = x + 10 → y >= 15
#[trust::refined(n, "n >= 5 && n < 100")]
#[requires("n >= 5 && n < 100")]
#[ensures("result >= 15")]
fn bound_propagation_inference(n: i32) -> i32 {
    let x = n;       // κ_x = "x >= 5" (propagated)
    let y = x + 10;  // Constraint: κ_y >= 15 (5 + 10)
    y                // result >= 15
}

// ============================================================================
// Part 2: Chained inference
// ============================================================================

/// Test inference through multiple operations
/// Inference: x >= 0, y = x + 1 → y >= 1, z = y * 2 → z >= 2
#[trust::refined(n, "n >= 0 && n < 100")]
#[requires("n >= 0 && n < 100")]
#[ensures("result >= 2")]
fn chained_inference(n: i32) -> i32 {
    let x = n;       // κ_x = "x >= 0"
    let y = x + 1;   // κ_y: constraint from x >= 0 + 1 → y >= 1
    let z = y * 2;   // κ_z: constraint from y >= 1 * 2 → z >= 2
    z                // result >= 2
}

/// Test inference with subtraction
/// Inference: x >= 20, y = x - 15 → y >= 5
#[trust::refined(n, "n >= 20 && n < 100")]
#[requires("n >= 20 && n < 100")]
#[ensures("result >= 5")]
fn subtraction_inference(n: i32) -> i32 {
    let x = n;       // κ_x = "x >= 20"
    let y = x - 15;  // κ_y: constraint from x >= 20 - 15 → y >= 5
    y                // result >= 5
}

// ============================================================================
// Part 3: Qualifier-based inference
// ============================================================================

/// Test that zero comparisons are inferred via qualifiers
/// The qualifier "v >= 0" matches when operating on unsigned-like values
#[trust::refined(n, "n >= 0")]
#[requires("n >= 0")]
#[ensures("result >= 0")]
fn qualifier_nonnegative(n: i32) -> i32 {
    let x = n;  // κ_x inherits qualifier "v >= 0"
    x           // result >= 0
}

/// Test that positive is preserved
/// The qualifier "v > 0" should be inferred
#[trust::refined(n, "n > 0 && n < 100")]
#[requires("n > 0 && n < 100")]
#[ensures("result > 0")]
fn qualifier_positive(n: i32) -> i32 {
    let x = n;  // κ_x = "x > 0" (from qualifier matching)
    x           // result > 0
}

// ============================================================================
// Part 4: Loop invariant inference candidates
// ============================================================================

/// Test loop with inferred invariant from initial value and bounds
/// The inference engine generates candidate invariant: i >= 0
#[trust::refined(n, "n > 0")]
#[requires("n > 0")]
#[ensures("result >= 0")]
fn loop_invariant_candidate_test(n: i32) -> i32 {
    let mut i = 0;      // Initial value candidate: i >= 0
    let mut sum = 0;    // Initial value candidate: sum >= 0

    // Loop invariant candidates:
    // - i >= 0 (from initial value, confidence 0.8)
    // - i <= n (from loop counter template, confidence 0.8)
    // - sum >= 0 (from initial value)
    #[invariant("i >= 0 && i <= n && sum >= 0")]
    while i < n {
        sum = sum + 1;
        i = i + 1;
    }

    sum  // result >= 0
}

/// Another loop demonstrating counter bounds inference
#[trust::refined(n, "n >= 0 && n < 1000")]
#[requires("n >= 0 && n < 1000")]
#[ensures("result >= 0")]
fn counter_bounds_inference(n: i32) -> i32 {
    let mut count = 0;  // Candidate: count >= 0

    // Invariant candidates from inference:
    // - count >= 0 (initial value)
    // - count <= n (loop bound pattern)
    #[invariant("count >= 0")]
    while count < n {
        count = count + 1;
    }

    count  // result >= 0
}

// ============================================================================
// Part 5: Complex inference scenarios
// ============================================================================

/// Multiple variables with interdependent constraints
#[trust::refined(a, "a >= 0 && a < 100")]
#[trust::refined(b, "b >= 0 && b < 100")]
#[requires("a >= 0 && a < 100 && b >= 0 && b < 100")]
#[ensures("result >= 0")]
fn multi_variable_inference(a: i32, b: i32) -> i32 {
    let x = a;          // κ_x: a >= 0
    let y = b;          // κ_y: b >= 0
    let sum = x + y;    // κ_sum: sum >= 0 (both operands non-negative)
    let diff = if x > y { x - y } else { y - x };  // κ_diff: diff >= 0 (absolute difference)
    sum + diff          // result >= 0
}

/// Inference with return value
/// The return refinement is inferred from the expression
#[trust::refined(n, "n >= 10 && n < 100")]
#[requires("n >= 10 && n < 100")]
#[ensures("result >= 5 && result <= 95")]
fn return_inference(n: i32) -> i32 {
    let x = n;          // κ_x: x >= 10 && x < 100
    let y = x - 5;      // κ_y: y >= 5 (from x >= 10 - 5)
    y                   // Return refinement inferred: result >= 5 && result <= 95
}

// ============================================================================
// Part 6: Negative tests (inference limitations)
// ============================================================================

/// This function demonstrates where inference is limited
/// The inference cannot determine n != 0 automatically
#[trust::refined(n, "n != 0")]
#[requires("n != 0")]  // Must be explicitly stated
#[ensures("result != 0")]
fn nonzero_requires_explicit(n: i32) -> i32 {
    let x = n;  // κ_x: cannot infer "x != 0" without explicit annotation
    x           // result != 0 (from explicit requires)
}

fn main() {
    // Part 1: Basic inference
    assert_eq!(constant_refinement_inference(), 5);
    assert!(sum_nonnegative_inference(10, 20) >= 0);
    assert!(bound_propagation_inference(5) >= 15);

    // Part 2: Chained inference
    assert!(chained_inference(0) >= 2);
    assert!(subtraction_inference(20) >= 5);

    // Part 3: Qualifier-based
    assert!(qualifier_nonnegative(0) >= 0);
    assert!(qualifier_positive(1) > 0);

    // Part 4: Loop invariants
    assert!(loop_invariant_candidate_test(5) >= 0);
    assert!(counter_bounds_inference(10) >= 0);

    // Part 5: Complex scenarios
    assert!(multi_variable_inference(5, 10) >= 0);
    assert!(return_inference(50) >= 5);
    assert!(return_inference(50) <= 95);

    // Part 6: Explicit annotations
    assert!(nonzero_requires_explicit(1) != 0);
    assert!(nonzero_requires_explicit(-1) != 0);

    println!("Phase 12.4: All refinement type inference tests passed!");
}
