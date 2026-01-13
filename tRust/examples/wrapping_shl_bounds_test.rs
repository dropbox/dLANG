// Test wrapping_shl verification contracts
//
// wrapping_shl semantics: shift left by (n mod bits) with modular wraparound.
// This test focuses on simple, solver-friendly properties that should hold under
// wrapping semantics:
// - (x == 0) => (x.wrapping_shl(n) == 0)
// - Zero propagates through chains of wrapping_shl
//
// @expect: VERIFIED

// =============================================================================
// Zero shift tests (constants)
// =============================================================================

#[ensures("result == 0")]
fn test_wrapping_shl_zero_u8_const() -> u8 {
    0u8.wrapping_shl(3)
}

#[ensures("result == 0")]
fn test_wrapping_shl_zero_u16_const() -> u16 {
    0u16.wrapping_shl(7)
}

#[ensures("result == 0")]
fn test_wrapping_shl_zero_u32_const() -> u32 {
    0u32.wrapping_shl(31)
}

#[ensures("result == 0")]
fn test_wrapping_shl_zero_i32_const() -> i32 {
    0i32.wrapping_shl(17)
}

#[ensures("result == 0")]
fn test_wrapping_shl_zero_i64_const() -> i64 {
    0i64.wrapping_shl(63)
}

// =============================================================================
// Zero shift tests (parameterized)
// =============================================================================

#[requires("x == 0")]
#[requires("n < 8")]
#[ensures("result == 0")]
fn test_wrapping_shl_zero_u8(x: u8, n: u32) -> u8 {
    x.wrapping_shl(n)
}

#[requires("x == 0")]
#[requires("n < 16")]
#[ensures("result == 0")]
fn test_wrapping_shl_zero_u16(x: u16, n: u32) -> u16 {
    x.wrapping_shl(n)
}

#[requires("x == 0")]
#[requires("n < 32")]
#[ensures("result == 0")]
fn test_wrapping_shl_zero_u32(x: u32, n: u32) -> u32 {
    x.wrapping_shl(n)
}

#[requires("x == 0")]
#[requires("n < 32")]
#[ensures("result == 0")]
fn test_wrapping_shl_zero_i32(x: i32, n: u32) -> i32 {
    x.wrapping_shl(n)
}

#[requires("x == 0")]
#[requires("n < 64")]
#[ensures("result == 0")]
fn test_wrapping_shl_zero_i64(x: i64, n: u32) -> i64 {
    x.wrapping_shl(n)
}

// =============================================================================
// Chained operations
// =============================================================================

#[requires("n < 32")]
#[requires("m < 32")]
#[ensures("result == 0")]
fn test_wrapping_shl_chain_u32(n: u32, m: u32) -> u32 {
    0u32.wrapping_shl(n).wrapping_shl(m)
}

#[requires("n < 32")]
#[requires("m < 32")]
#[ensures("result == 0")]
fn test_wrapping_shl_chain_i32(n: u32, m: u32) -> i32 {
    0i32.wrapping_shl(n).wrapping_shl(m)
}

// =============================================================================
// Combination with other operations (derive zero, then shift)
// =============================================================================

fn test_wrapping_shl_after_clamp_u32() {
    for x in 0u32..100u32 {
        let zeroed = x.clamp(0, 0);
        let shifted = zeroed.wrapping_shl(5);
        assert!(shifted == 0);
    }
    println!("test_wrapping_shl_after_clamp_u32 PASS");
}

fn test_wrapping_shl_after_clamp_i32() {
    for x in -50i32..50i32 {
        let zeroed = x.clamp(0, 0);
        let shifted = zeroed.wrapping_shl(13);
        assert!(shifted == 0);
    }
    println!("test_wrapping_shl_after_clamp_i32 PASS");
}

fn test_wrapping_shl_in_loop_u32() {
    for n in 0u32..32u32 {
        let shifted = 0u32.wrapping_shl(n);
        assert!(shifted == 0);
    }
    println!("test_wrapping_shl_in_loop_u32 PASS");
}

fn main() {
    // Constant zero shifts
    assert!(test_wrapping_shl_zero_u8_const() == 0);
    assert!(test_wrapping_shl_zero_u16_const() == 0);
    assert!(test_wrapping_shl_zero_u32_const() == 0);
    assert!(test_wrapping_shl_zero_i32_const() == 0);
    assert!(test_wrapping_shl_zero_i64_const() == 0);

    // Parameterized zero shifts
    assert!(test_wrapping_shl_zero_u8(0, 0) == 0);
    assert!(test_wrapping_shl_zero_u8(0, 7) == 0);
    assert!(test_wrapping_shl_zero_u16(0, 15) == 0);
    assert!(test_wrapping_shl_zero_u32(0, 31) == 0);
    assert!(test_wrapping_shl_zero_i32(0, 0) == 0);
    assert!(test_wrapping_shl_zero_i64(0, 63) == 0);

    // Chain tests
    assert!(test_wrapping_shl_chain_u32(3, 7) == 0);
    assert!(test_wrapping_shl_chain_i32(9, 11) == 0);

    // Loop tests
    test_wrapping_shl_after_clamp_u32();
    test_wrapping_shl_after_clamp_i32();
    test_wrapping_shl_in_loop_u32();

    println!("All wrapping_shl_bounds_test tests passed!");
}

