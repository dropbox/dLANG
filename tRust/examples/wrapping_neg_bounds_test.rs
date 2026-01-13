// Test wrapping_neg verification contracts
// The wrapping_neg builtin contract provides:
// - x == 0 => result == 0 (negating zero gives zero)
//
// This test verifies that the verifier correctly reasons about
// wrapping_neg operations and their zero-preservation property.
//
// @expect: VERIFIED

// =============================================================================
// Zero negation tests
// =============================================================================

/// Negating zero gives zero (i8)
#[ensures("result == 0")]
fn test_wrapping_neg_zero_i8() -> i8 {
    0i8.wrapping_neg()
}

/// Negating zero gives zero (i16)
#[ensures("result == 0")]
fn test_wrapping_neg_zero_i16() -> i16 {
    0i16.wrapping_neg()
}

/// Negating zero gives zero (i32)
#[ensures("result == 0")]
fn test_wrapping_neg_zero_i32() -> i32 {
    0i32.wrapping_neg()
}

/// Negating zero gives zero (i64)
#[ensures("result == 0")]
fn test_wrapping_neg_zero_i64() -> i64 {
    0i64.wrapping_neg()
}

// =============================================================================
// Conditional zero negation tests
// =============================================================================

/// Conditional negation where input is zero
#[requires("x == 0")]
#[ensures("result == 0")]
fn test_wrapping_neg_precond_zero_i8(x: i8) -> i8 {
    x.wrapping_neg()
}

/// Conditional negation where input is zero (i32)
#[requires("x == 0")]
#[ensures("result == 0")]
fn test_wrapping_neg_precond_zero_i32(x: i32) -> i32 {
    x.wrapping_neg()
}

// =============================================================================
// Unsigned zero tests (wrapping_neg exists for unsigned types)
// =============================================================================

/// Negating zero gives zero (u8)
#[ensures("result == 0")]
fn test_wrapping_neg_zero_u8() -> u8 {
    0u8.wrapping_neg()
}

/// Negating zero gives zero (u16)
#[ensures("result == 0")]
fn test_wrapping_neg_zero_u16() -> u16 {
    0u16.wrapping_neg()
}

/// Negating zero gives zero (u32)
#[ensures("result == 0")]
fn test_wrapping_neg_zero_u32() -> u32 {
    0u32.wrapping_neg()
}

/// Negating zero gives zero (u64)
#[ensures("result == 0")]
fn test_wrapping_neg_zero_u64() -> u64 {
    0u64.wrapping_neg()
}

// =============================================================================
// Chained operations
// =============================================================================

/// Double wrapping_neg of zero is zero
#[ensures("result == 0")]
fn test_wrapping_neg_double_zero_i8() -> i8 {
    0i8.wrapping_neg().wrapping_neg()
}

/// Double wrapping_neg of zero is zero (i32)
#[ensures("result == 0")]
fn test_wrapping_neg_double_zero_i32() -> i32 {
    0i32.wrapping_neg().wrapping_neg()
}

/// Triple wrapping_neg of zero is zero
#[ensures("result == 0")]
fn test_wrapping_neg_triple_zero_i32() -> i32 {
    0i32.wrapping_neg().wrapping_neg().wrapping_neg()
}

// =============================================================================
// Combination with other zero-producing operations
// =============================================================================

/// Zero from clamp then wrapping_neg
fn test_wrapping_neg_after_clamp() {
    for x in 0..100i8 {
        let clamped = x.clamp(0, 0);  // Always 0
        let result = clamped.wrapping_neg();  // wrapping_neg(0) = 0
        assert!(result == 0);
    }
    println!("test_wrapping_neg_after_clamp PASS");
}

/// Zero from min then wrapping_neg
fn test_wrapping_neg_from_min() {
    for x in 0..100i32 {
        let zeroed = std::cmp::min(x, 0);  // Always 0 (min of x and 0)
        let result = zeroed.wrapping_neg();  // wrapping_neg(0) = 0
        assert!(result == 0);
    }
    println!("test_wrapping_neg_from_min PASS");
}

fn main() {
    // Zero negation tests
    assert!(test_wrapping_neg_zero_i8() == 0);
    assert!(test_wrapping_neg_zero_i16() == 0);
    assert!(test_wrapping_neg_zero_i32() == 0);
    assert!(test_wrapping_neg_zero_i64() == 0);

    // Conditional tests
    assert!(test_wrapping_neg_precond_zero_i8(0) == 0);
    assert!(test_wrapping_neg_precond_zero_i32(0) == 0);

    // Unsigned zero tests
    assert!(test_wrapping_neg_zero_u8() == 0);
    assert!(test_wrapping_neg_zero_u16() == 0);
    assert!(test_wrapping_neg_zero_u32() == 0);
    assert!(test_wrapping_neg_zero_u64() == 0);

    // Chained tests
    assert!(test_wrapping_neg_double_zero_i8() == 0);
    assert!(test_wrapping_neg_double_zero_i32() == 0);
    assert!(test_wrapping_neg_triple_zero_i32() == 0);

    // Loop tests
    test_wrapping_neg_after_clamp();
    test_wrapping_neg_from_min();

    println!("All wrapping_neg_bounds_test tests passed!");
}
