// Test wrapping_pow verification contracts
//
// wrapping_pow semantics: exponentiation with wrapping for overflow cases.
// This test focuses on solver-verified properties that are captured by the
// builtin contract:
// - exp == 0 => result == 1
// - base == 0 && exp > 0 => result == 0
// - base == 1 => result == 1
//
// Note: The VC IR models these special-case properties for wrapping_pow but
// does not try to prove exact results for general base/exp.
//
// @expect: VERIFIED

// =============================================================================
// Constant tests
// =============================================================================

#[ensures("result == 1")]
fn test_wrapping_pow_exp_zero_u8_const() -> u8 {
    5u8.wrapping_pow(0)
}

#[ensures("result == 1")]
fn test_wrapping_pow_base_zero_exp_zero_u32_const() -> u32 {
    0u32.wrapping_pow(0)
}

#[ensures("result == 0")]
fn test_wrapping_pow_base_zero_u32_const() -> u32 {
    0u32.wrapping_pow(5)
}

#[ensures("result == 1")]
fn test_wrapping_pow_base_one_u64_const() -> u64 {
    1u64.wrapping_pow(123)
}

// =============================================================================
// Parameterized tests
// =============================================================================

#[requires("exp == 0")]
#[ensures("result == 1")]
fn test_wrapping_pow_exp_zero_u8(base: u8, exp: u32) -> u8 {
    base.wrapping_pow(exp)
}

#[requires("exp == 0")]
#[ensures("result == 1")]
fn test_wrapping_pow_exp_zero_u16(base: u16, exp: u32) -> u16 {
    base.wrapping_pow(exp)
}

#[requires("exp == 0")]
#[ensures("result == 1")]
fn test_wrapping_pow_exp_zero_u32(base: u32, exp: u32) -> u32 {
    base.wrapping_pow(exp)
}

#[requires("exp == 0")]
#[ensures("result == 1")]
fn test_wrapping_pow_exp_zero_u64(base: u64, exp: u32) -> u64 {
    base.wrapping_pow(exp)
}

#[requires("base == 0")]
#[requires("exp > 0")]
#[ensures("result == 0")]
fn test_wrapping_pow_base_zero_u8(base: u8, exp: u32) -> u8 {
    base.wrapping_pow(exp)
}

#[requires("base == 0")]
#[requires("exp > 0")]
#[ensures("result == 0")]
fn test_wrapping_pow_base_zero_u32(base: u32, exp: u32) -> u32 {
    base.wrapping_pow(exp)
}

#[requires("base == 1")]
#[ensures("result == 1")]
fn test_wrapping_pow_base_one_u32(base: u32, exp: u32) -> u32 {
    base.wrapping_pow(exp)
}

#[requires("base == 1")]
#[ensures("result == 1")]
fn test_wrapping_pow_base_one_i32(base: i32, exp: u32) -> i32 {
    base.wrapping_pow(exp)
}

// =============================================================================
// Chained operations (zero base propagates)
// =============================================================================

#[requires("exp1 > 0")]
#[requires("exp2 > 0")]
#[ensures("result == 0")]
fn test_wrapping_pow_chain_zero_u32(exp1: u32, exp2: u32) -> u32 {
    0u32.wrapping_pow(exp1).wrapping_pow(exp2)
}

// =============================================================================
// Runtime checks (not verified)
// =============================================================================

fn test_wrapping_pow_runtime() {
    for base in 0u32..10u32 {
        assert_eq!(base.wrapping_pow(0), 1);
    }
    for exp in 1u32..10u32 {
        assert_eq!(0u32.wrapping_pow(exp), 0);
    }
    for exp in 0u32..20u32 {
        assert_eq!(1u32.wrapping_pow(exp), 1);
    }
    assert_eq!((-7i32).wrapping_pow(0), 1);
    assert_eq!(0i32.wrapping_pow(1), 0);

    println!("test_wrapping_pow_runtime PASS");
}

fn main() {
    // Constant tests
    assert!(test_wrapping_pow_exp_zero_u8_const() == 1);
    assert!(test_wrapping_pow_base_zero_exp_zero_u32_const() == 1);
    assert!(test_wrapping_pow_base_zero_u32_const() == 0);
    assert!(test_wrapping_pow_base_one_u64_const() == 1);

    // Parameterized tests
    assert!(test_wrapping_pow_exp_zero_u8(37, 0) == 1);
    assert!(test_wrapping_pow_exp_zero_u16(1234, 0) == 1);
    assert!(test_wrapping_pow_exp_zero_u32(9999, 0) == 1);
    assert!(test_wrapping_pow_exp_zero_u64(5555, 0) == 1);

    assert!(test_wrapping_pow_base_zero_u8(0, 5) == 0);
    assert!(test_wrapping_pow_base_zero_u32(0, 123) == 0);

    assert!(test_wrapping_pow_base_one_u32(1, 999) == 1);
    assert!(test_wrapping_pow_base_one_i32(1, 999) == 1);

    // Chain test
    assert!(test_wrapping_pow_chain_zero_u32(3, 7) == 0);

    // Runtime tests
    test_wrapping_pow_runtime();

    println!("All wrapping_pow_bounds_test tests passed!");
}
