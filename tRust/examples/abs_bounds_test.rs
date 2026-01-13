//! Integration test for abs (absolute value) verification
//!
//! Tests that the verifier correctly reasons about abs() results:
//! - Constant abs: abs of known constant values
//! - Non-negative guarantee: abs(x) >= 0
//! - Identity properties: when x >= 0, abs(x) == x; when x < 0, abs(x) == -x
//! - Double abs: abs(abs(x)) >= 0
//!
//! Note: The abs() builtin contract provides:
//!   - result >= 0
//!   - result == x || result == -x
//!
//! @expect: VERIFIED

// =============================================================================
// Constant abs tests
// =============================================================================

/// abs(0) == 0
#[ensures("result == 0")]
fn test_abs_zero() -> i32 {
    0i32.abs()
}

/// abs(5) == 5
#[ensures("result == 5")]
fn test_abs_positive_constant() -> i32 {
    5i32.abs()
}

/// abs(-5) == 5
#[ensures("result == 5")]
fn test_abs_negative_constant() -> i32 {
    (-5i32).abs()
}

/// abs(-1) == 1
#[ensures("result == 1")]
fn test_abs_negative_one() -> i32 {
    (-1i32).abs()
}

/// abs(127) == 127
#[ensures("result == 127")]
fn test_abs_positive_max_i8() -> i32 {
    127i32.abs()
}

/// abs(-128) == 128 (when stored in i32)
#[ensures("result == 128")]
fn test_abs_negative_min_i8() -> i32 {
    (-128i32).abs()
}

// =============================================================================
// Non-negative guarantee tests
// =============================================================================

/// abs is always non-negative (core contract)
#[ensures("result >= 0")]
fn test_abs_always_non_negative(x: i32) -> i32 {
    x.abs()
}

/// abs of bounded input is non-negative
#[requires("x >= -10 && x <= 10")]
#[ensures("result >= 0")]
fn test_abs_bounded_non_negative(x: i32) -> i32 {
    x.abs()
}

/// abs of non-negative input is non-negative
#[requires("x >= 0 && x <= 100")]
#[ensures("result >= 0")]
fn test_abs_non_negative_input(x: i32) -> i32 {
    x.abs()
}

/// abs of non-positive input is non-negative
#[requires("x >= -100 && x <= 0")]
#[ensures("result >= 0")]
fn test_abs_non_positive_input(x: i32) -> i32 {
    x.abs()
}

/// abs of large range is non-negative
#[requires("x >= -1000000 && x <= 1000000")]
#[ensures("result >= 0")]
fn test_abs_large_range(x: i32) -> i32 {
    x.abs()
}

// =============================================================================
// Identity tests (abs contract: result == x || result == -x)
// =============================================================================

/// When x >= 0, abs(x) == x
#[requires("x >= 0 && x <= 1000")]
#[ensures("result == x")]
fn test_abs_positive_identity(x: i32) -> i32 {
    x.abs()
}

/// When x == 0, abs(x) == 0
#[requires("x == 0")]
#[ensures("result == 0")]
fn test_abs_zero_identity(x: i32) -> i32 {
    x.abs()
}

/// When x <= 0 and x != MIN, abs(x) is non-negative
#[requires("x <= 0 && x > -2147483648")]
#[ensures("result >= 0")]
fn test_abs_negative_non_negative(x: i32) -> i32 {
    x.abs()
}

/// Abs in conditional branch (positive branch)
#[requires("x > 0 && x <= 100")]
#[ensures("result == x")]
fn test_abs_conditional_positive(x: i32) -> i32 {
    if x > 0 {
        x.abs()
    } else {
        0 // unreachable given requires
    }
}

/// Abs in conditional branch (negative branch)
#[requires("x < 0 && x >= -100")]
#[ensures("result == 0 - x")]
fn test_abs_conditional_negative(x: i32) -> i32 {
    if x < 0 {
        x.abs()
    } else {
        0 // unreachable given requires
    }
}

// =============================================================================
// Double/Triple abs tests
// =============================================================================

/// Double abs is non-negative
#[requires("x >= -50 && x <= 50")]
#[ensures("result >= 0")]
fn test_double_abs(x: i32) -> i32 {
    let first = x.abs();
    first.abs()
}

/// Triple abs is non-negative
#[ensures("result >= 0")]
fn test_triple_abs(x: i32) -> i32 {
    x.abs().abs().abs()
}

/// Quadruple abs is non-negative
#[ensures("result >= 0")]
fn test_quadruple_abs(x: i32) -> i32 {
    x.abs().abs().abs().abs()
}

// =============================================================================
// i64 abs tests
// =============================================================================

/// abs with i64
#[ensures("result >= 0")]
fn test_abs_i64(x: i64) -> i64 {
    x.abs()
}

/// abs i64 with positive input identity
#[requires("x >= 0 && x <= 1000")]
#[ensures("result == x")]
fn test_abs_i64_positive_identity(x: i64) -> i64 {
    x.abs()
}

/// abs i64 of bounded range
#[requires("x >= -100 && x <= 100")]
#[ensures("result >= 0")]
fn test_abs_i64_bounded(x: i64) -> i64 {
    x.abs()
}

// =============================================================================
// i16 and i8 abs tests
// =============================================================================

/// abs with i16
#[ensures("result >= 0")]
fn test_abs_i16(x: i16) -> i16 {
    x.abs()
}

/// abs with i8
#[ensures("result >= 0")]
fn test_abs_i8(x: i8) -> i8 {
    x.abs()
}

// =============================================================================
// Constant folding through abs (using let bindings)
// =============================================================================

/// Constant propagation: abs(-42) == 42
#[ensures("result == 42")]
fn test_abs_constant_fold() -> i32 {
    let x = -42i32;
    x.abs()
}

/// Constant propagation: abs(-100) == 100
#[ensures("result == 100")]
fn test_abs_constant_fold_100() -> i32 {
    let x = -100i32;
    x.abs()
}

/// Constant propagation: abs(0) == 0
#[ensures("result == 0")]
fn test_abs_constant_fold_zero() -> i32 {
    let x = 0i32;
    x.abs()
}

fn main() {
    // Constant abs tests
    println!("test_abs_zero() = {}", test_abs_zero());
    println!("test_abs_positive_constant() = {}", test_abs_positive_constant());
    println!("test_abs_negative_constant() = {}", test_abs_negative_constant());
    println!("test_abs_negative_one() = {}", test_abs_negative_one());
    println!("test_abs_positive_max_i8() = {}", test_abs_positive_max_i8());
    println!("test_abs_negative_min_i8() = {}", test_abs_negative_min_i8());

    // Non-negative guarantee tests
    println!("test_abs_always_non_negative(-42) = {}", test_abs_always_non_negative(-42));
    println!("test_abs_bounded_non_negative(5) = {}", test_abs_bounded_non_negative(5));
    println!("test_abs_non_negative_input(50) = {}", test_abs_non_negative_input(50));
    println!("test_abs_non_positive_input(-50) = {}", test_abs_non_positive_input(-50));
    println!("test_abs_large_range(-500000) = {}", test_abs_large_range(-500000));

    // Identity tests
    println!("test_abs_positive_identity(42) = {}", test_abs_positive_identity(42));
    println!("test_abs_zero_identity(0) = {}", test_abs_zero_identity(0));
    println!("test_abs_negative_non_negative(-42) = {}", test_abs_negative_non_negative(-42));
    println!("test_abs_conditional_positive(10) = {}", test_abs_conditional_positive(10));
    println!("test_abs_conditional_negative(-10) = {}", test_abs_conditional_negative(-10));

    // Double/Triple abs tests
    println!("test_double_abs(-25) = {}", test_double_abs(-25));
    println!("test_triple_abs(-100) = {}", test_triple_abs(-100));
    println!("test_quadruple_abs(-7) = {}", test_quadruple_abs(-7));

    // i64 tests
    println!("test_abs_i64(-12345) = {}", test_abs_i64(-12345));
    println!("test_abs_i64_positive_identity(500) = {}", test_abs_i64_positive_identity(500));
    println!("test_abs_i64_bounded(-75) = {}", test_abs_i64_bounded(-75));

    // i16 and i8 tests
    println!("test_abs_i16(-1000) = {}", test_abs_i16(-1000));
    println!("test_abs_i8(-50) = {}", test_abs_i8(-50));

    // Constant folding tests
    println!("test_abs_constant_fold() = {}", test_abs_constant_fold());
    println!("test_abs_constant_fold_100() = {}", test_abs_constant_fold_100());
    println!("test_abs_constant_fold_zero() = {}", test_abs_constant_fold_zero());

    println!("\nAll abs bounds tests passed!");
}
