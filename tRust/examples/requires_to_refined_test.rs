//! Integration test for Phase 12.3 requires-to-refined conversion
//!
//! This test demonstrates that tRust can convert #[requires] attributes
//! into equivalent #[trust::refined] suggestions. This enables migration
//! from function-level preconditions to parameter-level refinement types
//! that propagate automatically through the program.
//!
//! Example conversion:
//!   Before: #[requires("x > 0")]
//!   After:  #[trust::refined(x, "x > 0")]
//!
//! When requires-to-refined conversion runs, tRust reports:
//! "[tRust] Phase 12.3: #[requires] → #[trust::refined] suggestions for function_name:"
//!   - #[trust::refined(param, "predicate")]

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Single parameter constraint (basic conversion)
// ============================================================================

/// Function with simple requires that constrains one parameter
/// #[requires("x > 0")] converts to #[trust::refined(x, "x > 0")]
#[requires("x > 0")]
#[ensures("result == x")]
fn positive_only(x: i32) -> i32 {
    // The #[requires] can be converted to:
    // #[trust::refined(x, "x > 0")]
    x
}

/// Function with non-zero constraint
/// #[requires("n != 0")] converts to #[trust::refined(n, "n != 0")]
#[requires("n != 0")]
#[ensures("true")]
fn nonzero(n: i32) -> i32 {
    // Can be converted to: #[trust::refined(n, "n != 0")]
    n
}

// ============================================================================
// Part 2: Multiple parameters with separate constraints
// ============================================================================

/// Function with two separate requires, each constraining one parameter
/// #[requires("a >= 0")] and #[requires("b > 0")] convert separately
#[requires("a >= 0")]
#[requires("b > 0")]
#[ensures("result >= 0")]
fn divide_nonneg_by_pos(a: i32, b: i32) -> i32 {
    // Can be converted to:
    // #[trust::refined(a, "a >= 0")]
    // #[trust::refined(b, "b > 0")]
    a / b
}

/// Function with multiple parameters, single combined requires
/// #[requires("x > 0 && y > 0")] produces suggestions for both params
#[requires("x > 0 && x < 1000 && y > 0 && y < 1000")]
#[ensures("result > 0")]
fn both_positive(x: i32, y: i32) -> i32 {
    // Can be converted to:
    // #[trust::refined(x, "x > 0 && ...")] (mentions x)
    // #[trust::refined(y, "y > 0 && ...")] (mentions y)
    x + y
}

// ============================================================================
// Part 3: Cross-parameter constraints
// ============================================================================

/// Function with constraint involving multiple parameters
/// #[requires("low < high")] applies to both parameters
#[requires("low >= 0 && low < high && high < 500")]
#[ensures("result == low")]
fn select_low(low: i32, high: i32) -> i32 {
    // Can be converted to:
    // #[trust::refined(low, "low >= 0 && low < high && high < 500")]
    // #[trust::refined(high, "low >= 0 && low < high && high < 500")]
    // Simple selection avoids overflow concerns
    low
}

/// Range constraint between parameters
/// #[requires("min <= max")] with explicit zero constraint
#[requires("min <= max")]
#[requires("max > 0")]
#[ensures("result >= min")]
fn clamp_above_min(value: i32, min: i32, max: i32) -> i32 {
    // Can be converted to:
    // #[trust::refined(min, "min <= max")]
    // #[trust::refined(max, "min <= max")]  and  #[trust::refined(max, "max > 0")]
    if value < min { min }
    else if value > max { max }
    else { value }
}

// ============================================================================
// Part 4: Complex predicates
// ============================================================================

/// Function with complex boolean predicate
/// #[requires("a > 0 && b > 0 && a < b")] mentions a and b
#[requires("a > 0 && b > 0 && a < b")]
#[ensures("result >= 0 && result < b")]
fn difference(a: i32, b: i32) -> i32 {
    // Can be converted to refined annotations for both params
    b - a
}

/// Function with division requiring multiple conditions
#[requires("divisor != 0")]
#[requires("dividend >= 0")]
#[ensures("result >= 0")]
fn safe_divide_nonneg(dividend: i32, divisor: i32) -> i32 {
    // Two separate refined annotations:
    // #[trust::refined(dividend, "dividend >= 0")]
    // #[trust::refined(divisor, "divisor != 0")]
    let q = dividend / divisor;
    if q < 0 { 0 } else { q }
}

// ============================================================================
// Part 5: Edge cases
// ============================================================================

/// Function with no parameters mentioned in requires (constant constraint)
/// This should not produce any refined suggestions for parameters
#[requires("true")]
#[ensures("result == 42")]
fn always_42() -> i32 {
    // No parameter mentioned in #[requires], so no refined suggestions
    42
}

/// Function where parameter name is substring of another word
/// Tests word boundary detection
#[requires("max > 0")]
#[ensures("result >= 0 && result <= max")]
fn bounded_value(value: i32, max: i32) -> i32 {
    // Should only suggest #[trust::refined(max, "max > 0")]
    // NOT match "max" in "maximum" etc.
    if value < 0 { 0 }
    else if value > max { max }
    else { value }
}

/// Function with underscore in parameter name
/// Tests proper word boundary handling with underscores
#[requires("start_idx >= 0")]
#[requires("end_idx > start_idx")]
#[ensures("result >= 0")]
fn range_len(start_idx: i32, end_idx: i32) -> i32 {
    // Should suggest:
    // #[trust::refined(start_idx, "start_idx >= 0")]
    // #[trust::refined(start_idx, "end_idx > start_idx")]
    // #[trust::refined(end_idx, "end_idx > start_idx")]
    end_idx - start_idx
}

// ============================================================================
// Part 6: Integration with existing #[trust::refined]
// ============================================================================

/// Function that already has #[trust::refined] (manual annotation)
/// Shows equivalence between requires and refined
#[trust::refined(divisor, "divisor != 0")]
#[requires("divisor != 0")]
#[ensures("true")]
fn already_refined(dividend: i32, divisor: i32) -> i32 {
    // Already has both forms - demonstrates equivalence
    dividend / divisor
}

/// Function with mixed manual and convertible specs
#[trust::refined(a, "a > 0 && a < 500")]  // Already refined
#[requires("b > 0 && b < 500")]           // Could be converted
#[ensures("result == a")]
fn mixed_refinements(a: i32, b: i32) -> i32 {
    // Just return a to avoid overflow in addition
    a
}

// ============================================================================
// Part 7: Generic-looking constraints (for future expansion)
// ============================================================================

/// Function with array-like index constraint
/// In future, could support: #[refined("idx < self.len()")]
#[requires("idx >= 0 && idx < 10")]
#[ensures("true")]
fn array_access_simulated(arr: [i32; 10], idx: usize) -> i32 {
    // Refined suggestion for idx
    arr[idx]
}

/// Function with method-like constraint (simplified)
#[requires("n > 0 && n < 256")]
#[ensures("result <= n")]
fn constrained_u8(n: i32) -> i32 {
    n / 2
}

// ============================================================================
// Main function to run all tests
// ============================================================================

fn main() {
    // Part 1: Single parameter
    assert_eq!(positive_only(5), 5);
    assert_eq!(nonzero(42), 42);

    // Part 2: Multiple parameters
    assert_eq!(divide_nonneg_by_pos(10, 2), 5);
    assert_eq!(both_positive(3, 4), 7);

    // Part 3: Cross-parameter constraints
    assert_eq!(select_low(0, 10), 0);
    assert_eq!(clamp_above_min(5, 0, 10), 5);
    assert_eq!(clamp_above_min(-5, 0, 10), 0);
    assert_eq!(clamp_above_min(15, 0, 10), 10);

    // Part 4: Complex predicates
    assert_eq!(difference(3, 7), 4);
    assert_eq!(safe_divide_nonneg(10, 3), 3);

    // Part 5: Edge cases
    assert_eq!(always_42(), 42);
    assert_eq!(bounded_value(5, 10), 5);
    assert_eq!(bounded_value(-1, 10), 0);
    assert_eq!(bounded_value(100, 10), 10);
    assert_eq!(range_len(2, 7), 5);

    // Part 6: Integration
    assert_eq!(already_refined(20, 4), 5);
    assert_eq!(mixed_refinements(3, 4), 3);

    // Part 7: Generic-looking constraints
    let arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    assert_eq!(array_access_simulated(arr, 5), 5);
    assert_eq!(constrained_u8(100), 50);

    println!("All requires-to-refined conversion tests passed!");
}
