// Test saturating_mul verification contracts
// The saturating_mul builtin contract provides:
// - result >= 0 (unsigned types)
// - (a > 0 && b > 0) => result >= a && result >= b (growth property)
//
// This test verifies that the verifier correctly reasons about
// saturating_mul operations and their growth guarantees.
//
// @expect: VERIFIED

// =============================================================================
// Non-negative result tests (unsigned types)
// =============================================================================

/// saturating_mul result is non-negative
#[ensures("result >= 0")]
fn test_saturating_mul_nonneg() -> u8 {
    let a: u8 = 5;
    let b: u8 = 42;
    a.saturating_mul(b)
}

/// saturating_mul from zero is non-negative
#[ensures("result >= 0")]
fn test_saturating_mul_from_zero() -> u8 {
    0u8.saturating_mul(100u8)
}

/// saturating_mul to zero is non-negative
#[ensures("result >= 0")]
fn test_saturating_mul_to_zero() -> u8 {
    100u8.saturating_mul(0u8)
}

// =============================================================================
// Growth property tests (when both operands positive)
// =============================================================================

/// When both operands > 0, result >= a
#[requires("a > 0")]
#[requires("b > 0")]
#[ensures("result >= a")]
fn test_saturating_mul_grows_a(a: u8, b: u8) -> u8 {
    a.saturating_mul(b)
}

/// When both operands > 0, result >= b
#[requires("a > 0")]
#[requires("b > 0")]
#[ensures("result >= b")]
fn test_saturating_mul_grows_b(a: u8, b: u8) -> u8 {
    a.saturating_mul(b)
}

/// Combined growth property
#[requires("a > 0 && b > 0")]
#[ensures("result >= a && result >= b")]
fn test_saturating_mul_growth_combined(a: u8, b: u8) -> u8 {
    a.saturating_mul(b)
}

// =============================================================================
// Different integer types
// =============================================================================

/// u16 saturating_mul non-negative
#[ensures("result >= 0")]
fn test_saturating_mul_u16_nonneg() -> u16 {
    50u16.saturating_mul(1000u16)
}

/// u16 growth property
#[requires("a > 0 && b > 0")]
#[ensures("result >= a")]
fn test_saturating_mul_u16_growth(a: u16, b: u16) -> u16 {
    a.saturating_mul(b)
}

/// u32 saturating_mul non-negative
#[ensures("result >= 0")]
fn test_saturating_mul_u32_nonneg() -> u32 {
    12345u32.saturating_mul(67890u32)
}

/// u32 growth property
#[requires("a > 0 && b > 0")]
#[ensures("result >= a && result >= b")]
fn test_saturating_mul_u32_growth(a: u32, b: u32) -> u32 {
    a.saturating_mul(b)
}

/// u64 saturating_mul non-negative
#[ensures("result >= 0")]
fn test_saturating_mul_u64_nonneg() -> u64 {
    1000u64.saturating_mul(2000u64)
}

// =============================================================================
// Bounded inputs (to avoid saturation in test assertions)
// =============================================================================

/// Bounded multiplication with known non-saturation
#[requires("a >= 1 && a <= 10")]
#[requires("b >= 1 && b <= 10")]
#[ensures("result >= a")]
#[ensures("result >= b")]
fn test_saturating_mul_bounded(a: u8, b: u8) -> u8 {
    a.saturating_mul(b)
}

/// Bounded u32 multiplication
#[requires("a > 0 && a < 100")]
#[requires("b > 0 && b < 100")]
#[ensures("result >= a")]
fn test_saturating_mul_u32_bounded(a: u32, b: u32) -> u32 {
    a.saturating_mul(b)
}

// =============================================================================
// Chained operations
// =============================================================================

/// Chained multiplication maintains non-negative
#[ensures("result >= 0")]
fn test_saturating_mul_chain_nonneg() -> u8 {
    let a: u8 = 2;
    let b: u8 = 3;
    let c: u8 = 4;
    a.saturating_mul(b).saturating_mul(c)
}

// =============================================================================
// Runtime tests (non-verified)
// =============================================================================

fn test_saturating_mul_runtime() {
    // Verify runtime behavior matches contract semantics
    assert!(5u8.saturating_mul(10) >= 5);
    assert!(5u8.saturating_mul(10) >= 10);

    // Saturation at max
    assert!(200u8.saturating_mul(200) == u8::MAX);
    assert!(u8::MAX.saturating_mul(2) == u8::MAX);

    println!("test_saturating_mul_runtime PASS");
}

fn test_saturating_mul_growth_runtime() {
    for a in 1..10u8 {
        for b in 1..10u8 {
            let result = a.saturating_mul(b);
            assert!(result >= a, "growth property a failed");
            assert!(result >= b, "growth property b failed");
        }
    }
    println!("test_saturating_mul_growth_runtime PASS");
}

fn main() {
    // Non-negative tests
    assert!(test_saturating_mul_nonneg() >= 0);
    assert!(test_saturating_mul_from_zero() >= 0);
    assert!(test_saturating_mul_to_zero() >= 0);

    // Growth tests
    assert!(test_saturating_mul_grows_a(5, 10) >= 5);
    assert!(test_saturating_mul_grows_b(5, 10) >= 10);
    assert!(test_saturating_mul_growth_combined(3, 7) >= 3);

    // Type tests
    assert!(test_saturating_mul_u16_nonneg() >= 0);
    assert!(test_saturating_mul_u16_growth(100, 200) >= 100);
    assert!(test_saturating_mul_u32_nonneg() >= 0);
    assert!(test_saturating_mul_u32_growth(1000, 2000) >= 1000);
    assert!(test_saturating_mul_u64_nonneg() >= 0);

    // Bounded tests
    assert!(test_saturating_mul_bounded(5, 5) >= 5);
    assert!(test_saturating_mul_u32_bounded(50, 50) >= 50);

    // Chain test
    assert!(test_saturating_mul_chain_nonneg() >= 0);

    // Runtime tests
    test_saturating_mul_runtime();
    test_saturating_mul_growth_runtime();

    println!("All saturating_mul_bounds_test tests passed!");
}
