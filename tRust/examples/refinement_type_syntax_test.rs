//! Integration test for refinement type syntax (Phase 12.1)
//!
//! Refinement types attach predicates to types, enabling automatic verification
//! at call sites. This test validates the basic syntax parsing for Phase 12.1:
//!
//! Syntax:
//!   #[refined(param_name, "predicate")]  -- refinement on a parameter
//!   #[returns_refined("predicate")]       -- refinement on return value
//!
//! NOTE: Phase 12.1 only implements syntax parsing. The refinement attributes
//! are parsed and stored but do not yet generate verification conditions.
//! Phase 12.2 will add automatic VC generation from refinements.
//!
//! This test demonstrates that:
//! 1. The refinement syntax is parsed correctly (no parse errors)
//! 2. Functions with refinement attributes verify correctly

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Basic parameter refinement syntax
// ============================================================================

/// A function with a refined parameter
/// NOTE: In Phase 12.1, #[refined] is parsed but not yet used for VC generation
#[trust::refined(n, "n > 0")]
#[requires("n > 0")]  // Explicit requires until Phase 12.2
#[ensures("result >= 1")]
fn positive_identity(n: i32) -> i32 {
    n
}

/// Multiple refined parameters - using max() to avoid overflow
#[trust::refined(a, "a > 0")]
#[trust::refined(b, "b > 0")]
#[requires("a > 0")]
#[requires("b > 0")]
#[ensures("result > 0")]
fn max_positives(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }  // No arithmetic, just comparison
}

/// Refined parameter with simple identity (no arithmetic)
#[trust::refined(x, "x >= 0")]
#[requires("x >= 0")]
fn nonnegative_identity(x: i32) -> i32 {
    x
}

// ============================================================================
// Part 2: Return type refinement
// ============================================================================

/// Function with refined return type
#[requires("n >= 0")]
#[trust::returns_refined("result >= 0")]
#[ensures("result >= 0")]
fn abs_nonneg(n: i32) -> i32 {
    n  // Already non-negative from precondition
}

/// Both parameter and return refinement (using small values)
#[trust::refined(x, "x > 0")]
#[trust::returns_refined("result > 0")]
#[requires("x > 0 && x < 100")]
#[ensures("result > 0 && result == x + 1")]
fn increment_small(x: u8) -> u8 {
    x + 1  // No overflow: max 99 + 1 = 100
}

/// Refined return with relation to input
#[trust::refined(n, "n >= 0")]
#[trust::returns_refined("result >= n")]
#[requires("n >= 0")]
#[ensures("result >= n")]
fn max_with_ten(n: i32) -> i32 {
    if n > 10 { n } else { 10 }
}

// ============================================================================
// Part 3: Refinement with other specification attributes
// ============================================================================

/// Refinement combined with requires/ensures
#[trust::refined(n, "n > 0")]
#[requires("n > 0 && n < 1000")]
#[ensures("result >= 1")]
#[ensures("result <= n")]
fn clamp_to_range(n: i32, val: i32) -> i32 {
    if val < 1 { 1 }
    else if val > n { n }
    else { val }
}

/// Pure function with refinement (using safe operations)
#[pure]
#[trust::refined(a, "a >= 0")]
#[trust::refined(b, "b >= 0")]
#[trust::returns_refined("result >= 0")]
#[requires("a >= 0 && a < 100")]
#[requires("b >= 0 && b < 100")]
#[ensures("result >= 0")]
fn pure_max_nonneg(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

// ============================================================================
// Part 4: Division and selection use cases
// ============================================================================

/// Selection with refinement
#[trust::refined(idx, "idx == 0 || idx == 1")]
#[requires("idx <= 1")]
fn select_bool(idx: usize, a: i32, b: i32) -> i32 {
    if idx == 0 { a } else { b }
}

/// Clamped percentage
#[trust::refined(pct, "pct >= 0 && pct <= 100")]
#[trust::returns_refined("result >= 0 && result <= 100")]
// Note: No explicit requires needed - function handles all i32 inputs safely
#[ensures("result >= 0 && result <= 100")]
fn normalize_percentage(pct: i32) -> i32 {
    if pct < 0 { 0 }
    else if pct > 100 { 100 }
    else { pct }
}

// ============================================================================
// Part 5: Boolean and comparison refinements
// ============================================================================

/// Non-negative check with refinement
#[trust::refined(x, "true")]
#[trust::returns_refined("result == (x >= 0)")]
#[ensures("result == (x >= 0)")]
fn is_nonnegative(x: i32) -> bool {
    x >= 0
}

/// Bounded value check
#[trust::refined(x, "true")]
#[trust::refined(lo, "true")]
#[trust::refined(hi, "lo <= hi")]
#[requires("lo <= hi")]
#[trust::returns_refined("result == (x >= lo && x <= hi)")]
#[ensures("result == (x >= lo && x <= hi)")]
fn is_in_range(x: i32, lo: i32, hi: i32) -> bool {
    x >= lo && x <= hi
}

fn main() {
    // Part 1: Basic parameter refinement
    let x = positive_identity(5);
    assert!(x >= 1);

    let max = max_positives(3, 4);
    assert!(max > 0);

    let n = nonnegative_identity(7);
    assert!(n >= 0);

    // Part 2: Return type refinement
    let abs_val = abs_nonneg(10);
    assert!(abs_val >= 0);

    let inc = increment_small(5);
    assert!(inc > 0);

    let max_val = max_with_ten(5);
    assert!(max_val >= 5);

    // Part 3: Combined specs
    let clamped = clamp_to_range(100, 150);
    assert!(clamped == 100);

    let max_res = pure_max_nonneg(3, 4);
    assert!(max_res >= 0);

    // Part 4: Selection and percentage
    let selected = select_bool(0, 10, 20);
    assert!(selected == 10);

    let pct = normalize_percentage(150);
    assert!(pct >= 0 && pct <= 100);

    // Part 5: Boolean refinements
    let is_pos = is_nonnegative(5);
    assert!(is_pos);

    let in_range = is_in_range(5, 0, 10);
    assert!(in_range);

    println!("All refinement type syntax tests passed!");
}
