//! Integration test for refinement type VC generation (Phase 12.2)
//!
//! Phase 12.2 automatically converts refinement type annotations to verification
//! conditions, eliminating the need for redundant #[requires]/#[ensures] attributes
//! when refinement types are used.
//!
//! Key feature:
//!   #[refined(param, "predicate")] automatically generates #[requires("predicate")]
//!   #[returns_refined("predicate")] automatically generates #[ensures("predicate")]
//!
//! This test demonstrates that refinement types work WITHOUT explicit requires/ensures.
//!
//! Note: Some functions still need explicit #[requires] for automatic safety checks
//! (bounds checking, division-by-zero) which run separately from contract verification.

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Parameter refinement generates preconditions automatically
// ============================================================================

/// A function using ONLY refinement type - no explicit #[requires]
/// Phase 12.2: The refined param automatically generates the precondition
#[trust::refined(n, "n > 0")]
#[ensures("result >= 1")]
fn positive_only_refined(n: i32) -> i32 {
    n  // n > 0 is assumed from the refinement type
}

/// Multiple refined params - all become preconditions automatically
#[trust::refined(a, "a >= 0")]
#[trust::refined(b, "b >= 0")]
#[ensures("result >= 0")]
fn max_nonneg_refined(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

/// Refined param with arithmetic - precondition prevents overflow
#[trust::refined(x, "x >= 0 && x < 100")]
#[requires("x >= 0 && x < 100")]  // Explicit for automatic overflow checker
#[ensures("result > x")]
fn increment_refined(x: i32) -> i32 {
    x + 1
}

// ============================================================================
// Part 2: Return refinement generates postconditions automatically
// ============================================================================

/// Return refinement ONLY - generates ensures automatically
#[requires("n >= 0")]
#[trust::returns_refined("result >= 0")]
fn abs_returns_refined(n: i32) -> i32 {
    n  // Already non-negative
}

/// Both parameter and return refinement - generates both automatically
#[trust::refined(x, "x > 0 && x < 200")]
#[requires("x > 0 && x < 200")]  // Explicit for automatic overflow checker
#[trust::returns_refined("result > x")]
fn increment_both_refined(x: u8) -> u8 {
    x + 1
}

/// Multiple properties through refinement
#[trust::refined(lo, "lo >= 0")]
#[trust::refined(hi, "hi >= lo")]
#[trust::returns_refined("result >= lo && result <= hi")]
fn clamp_refined(val: i32, lo: i32, hi: i32) -> i32 {
    if val < lo { lo }
    else if val > hi { hi }
    else { val }
}

// ============================================================================
// Part 3: Refinement types for domain-specific constraints
// ============================================================================

/// Array index refinement - demonstrates precondition generation
/// Note: The refined param generates a precondition that the verifier uses
#[trust::refined(idx, "idx < 4")]
#[requires("idx < 4")]  // Explicit for automatic bounds checker
fn access_small_array_refined(arr: &[i32; 4], idx: usize) -> i32 {
    arr[idx]
}

/// Non-zero refinement for division (need explicit requires for auto-checker)
#[trust::refined(divisor, "divisor != 0")]
#[requires("divisor != 0")]  // Explicit for automatic division-by-zero checker
fn safe_divide_refined(dividend: i32, divisor: i32) -> i32 {
    dividend / divisor
}

/// Simple percentage clamping (integer result to avoid float comparison issues)
#[trust::refined(pct, "true")]
#[trust::returns_refined("result >= 0 && result <= 100")]
fn clamp_percentage(pct: i32) -> i32 {
    if pct < 0 { 0 }
    else if pct > 100 { 100 }
    else { pct }
}

// ============================================================================
// Part 4: Combining refinement with simple contracts
// ============================================================================

/// Simple function showing refinement and explicit ensures together
#[trust::refined(x, "x > 0")]
#[ensures("result >= x")]
fn identity_positive_refined(x: i32) -> i32 {
    x
}

// ============================================================================
// Part 5: Refinement with boolean results
// ============================================================================

/// Boolean result with refinement
#[trust::refined(x, "true")]
#[trust::returns_refined("result == (x >= 0)")]
fn is_nonneg_refined(x: i32) -> bool {
    x >= 0
}

/// Range check with refinements
#[trust::refined(lo, "true")]
#[trust::refined(hi, "lo <= hi")]
#[trust::returns_refined("result == (x >= lo && x <= hi)")]
fn in_range_refined(x: i32, lo: i32, hi: i32) -> bool {
    x >= lo && x <= hi
}

fn main() {
    // Part 1: Parameter refinements
    let p = positive_only_refined(5);
    assert!(p >= 1);

    let max_val = max_nonneg_refined(3, 7);
    assert!(max_val >= 0);

    let inc = increment_refined(50);
    assert!(inc > 50);

    // Part 2: Return refinements
    let abs_val = abs_returns_refined(10);
    assert!(abs_val >= 0);

    let both = increment_both_refined(5);
    assert!(both > 5);

    let clamped = clamp_refined(150, 0, 100);
    assert!(clamped >= 0 && clamped <= 100);

    // Part 3: Domain-specific
    let arr = [10, 20, 30, 40];
    let elem = access_small_array_refined(&arr, 2);
    assert!(elem == 30);

    let pct = clamp_percentage(150);
    assert!(pct >= 0 && pct <= 100);

    let div = safe_divide_refined(100, 5);
    assert!(div == 20);

    // Part 4: Combined with explicit ensures
    let identity = identity_positive_refined(42);
    assert!(identity >= 42);

    // Part 5: Boolean refinements
    let is_pos = is_nonneg_refined(5);
    assert!(is_pos);

    let in_rng = in_range_refined(5, 0, 10);
    assert!(in_rng);

    println!("Phase 12.2: All refinement type VC generation tests passed!");
}
