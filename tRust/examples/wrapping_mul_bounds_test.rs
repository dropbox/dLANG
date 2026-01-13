// Test wrapping_mul verification contracts
// The wrapping_mul builtin contract provides:
// - (a == 0 || b == 0) => result == 0  (zero multiplication)
//
// This test verifies that the verifier correctly reasons about
// wrapping_mul operations and their zero-preservation property.
//
// @expect: VERIFIED

// =============================================================================
// Zero multiplication tests
// =============================================================================

/// Zero times anything is zero
#[ensures("result == 0")]
fn test_wrapping_mul_zero_left() -> u8 {
    let a: u8 = 0;
    let b: u8 = 42;
    a.wrapping_mul(b)
}

/// Anything times zero is zero
#[ensures("result == 0")]
fn test_wrapping_mul_zero_right() -> u8 {
    let a: u8 = 42;
    let b: u8 = 0;
    a.wrapping_mul(b)
}

/// Zero times zero is zero
#[ensures("result == 0")]
fn test_wrapping_mul_both_zero() -> u8 {
    0u8.wrapping_mul(0u8)
}

// =============================================================================
// Conditional zero multiplication tests
// =============================================================================

/// Conditional multiplication where result is zero
#[requires("x == 0")]
#[ensures("result == 0")]
fn test_wrapping_mul_precond_zero(x: u8, y: u8) -> u8 {
    x.wrapping_mul(y)
}

/// Conditional multiplication with zero second operand
#[requires("y == 0")]
#[ensures("result == 0")]
fn test_wrapping_mul_precond_zero_rhs(x: u8, y: u8) -> u8 {
    x.wrapping_mul(y)
}

/// Either operand zero means result is zero
#[requires("x == 0 || y == 0")]
#[ensures("result == 0")]
fn test_wrapping_mul_either_zero(x: u8, y: u8) -> u8 {
    x.wrapping_mul(y)
}

// =============================================================================
// Different integer types
// =============================================================================

/// u16 wrapping_mul zero preservation
#[ensures("result == 0")]
fn test_wrapping_mul_u16_zero() -> u16 {
    0u16.wrapping_mul(1000u16)
}

/// u32 wrapping_mul zero preservation
#[ensures("result == 0")]
fn test_wrapping_mul_u32_zero() -> u32 {
    12345u32.wrapping_mul(0u32)
}

/// i32 wrapping_mul zero preservation
#[ensures("result == 0")]
fn test_wrapping_mul_i32_zero() -> i32 {
    0i32.wrapping_mul(-100i32)
}

/// i64 wrapping_mul zero preservation
#[ensures("result == 0")]
fn test_wrapping_mul_i64_zero() -> i64 {
    (-50i64).wrapping_mul(0i64)
}

// =============================================================================
// Chained operations with wrapping_mul
// =============================================================================

/// Chained multiplication where one operand is zero
#[ensures("result == 0")]
fn test_wrapping_mul_chain_zero() -> u8 {
    let a: u8 = 5;
    let b: u8 = 0;
    let c: u8 = 10;
    a.wrapping_mul(b).wrapping_mul(c)
}

/// Zero propagates through multiplication chain
#[ensures("result == 0")]
fn test_wrapping_mul_zero_propagation() -> u8 {
    let zero: u8 = 0;
    let x = zero.wrapping_mul(5);  // x == 0
    x.wrapping_mul(10)  // 0 * 10 == 0
}

// =============================================================================
// Combination with other operations
// =============================================================================

/// Zero after clamp multiplication
fn test_wrapping_mul_after_clamp() {
    for x in 0..100u8 {
        let clamped = x.clamp(0, 0);  // Always 0
        let result = clamped.wrapping_mul(50);  // 0 * 50 = 0
        assert!(result == 0);
    }
    println!("test_wrapping_mul_after_clamp PASS");
}

/// Zero from min gives zero product
fn test_wrapping_mul_from_min() {
    for x in 0..100u8 {
        let zeroed = std::cmp::min(x, 0);  // Always 0 (min of x and 0)
        let result = zeroed.wrapping_mul(100);  // 0 * 100 = 0
        assert!(result == 0);
    }
    println!("test_wrapping_mul_from_min PASS");
}

fn main() {
    // Zero multiplication tests
    assert!(test_wrapping_mul_zero_left() == 0);
    assert!(test_wrapping_mul_zero_right() == 0);
    assert!(test_wrapping_mul_both_zero() == 0);

    // Conditional tests
    assert!(test_wrapping_mul_precond_zero(0, 50) == 0);
    assert!(test_wrapping_mul_precond_zero_rhs(50, 0) == 0);
    assert!(test_wrapping_mul_either_zero(0, 100) == 0);
    assert!(test_wrapping_mul_either_zero(100, 0) == 0);

    // Type tests
    assert!(test_wrapping_mul_u16_zero() == 0);
    assert!(test_wrapping_mul_u32_zero() == 0);
    assert!(test_wrapping_mul_i32_zero() == 0);
    assert!(test_wrapping_mul_i64_zero() == 0);

    // Chain tests
    assert!(test_wrapping_mul_chain_zero() == 0);
    assert!(test_wrapping_mul_zero_propagation() == 0);

    // Loop tests
    test_wrapping_mul_after_clamp();
    test_wrapping_mul_from_min();

    println!("All wrapping_mul_bounds_test tests passed!");
}
