// Test wrapping_rem verification contracts
//
// wrapping_rem semantics: remainder operation with wrapping for overflow cases.
// This test focuses on solver-verified properties for unsigned types:
// - (x == 0 && y > 0) => (x.wrapping_rem(y) == 0)
// - Zero propagates through chains of wrapping_rem (when divisors are positive)
//
// Note: Signed wrapping_rem (i32, i64) not tested here due to solver limitations
// with signed modulo semantics. Unsigned types verify correctly.
//
// @expect: VERIFIED

// =============================================================================
// Zero remainder tests (constants)
// =============================================================================

#[ensures("result == 0")]
fn test_wrapping_rem_zero_u8_const() -> u8 {
    0u8.wrapping_rem(7)
}

#[ensures("result == 0")]
fn test_wrapping_rem_zero_u16_const() -> u16 {
    0u16.wrapping_rem(100)
}

#[ensures("result == 0")]
fn test_wrapping_rem_zero_u32_const() -> u32 {
    0u32.wrapping_rem(42)
}

#[ensures("result == 0")]
fn test_wrapping_rem_zero_u64_const() -> u64 {
    0u64.wrapping_rem(999)
}

// =============================================================================
// Zero remainder tests (parameterized)
// =============================================================================

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_wrapping_rem_zero_u8(x: u8, y: u8) -> u8 {
    x.wrapping_rem(y)
}

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_wrapping_rem_zero_u16(x: u16, y: u16) -> u16 {
    x.wrapping_rem(y)
}

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_wrapping_rem_zero_u32(x: u32, y: u32) -> u32 {
    x.wrapping_rem(y)
}

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_wrapping_rem_zero_u64(x: u64, y: u64) -> u64 {
    x.wrapping_rem(y)
}

// =============================================================================
// Chained operations (zero propagates through remainder chains)
// =============================================================================

#[requires("y > 0")]
#[requires("z > 0")]
#[ensures("result == 0")]
fn test_wrapping_rem_chain_u32(y: u32, z: u32) -> u32 {
    0u32.wrapping_rem(y).wrapping_rem(z)
}

#[requires("y > 0")]
#[requires("z > 0")]
#[ensures("result == 0")]
fn test_wrapping_rem_chain_u64(y: u64, z: u64) -> u64 {
    0u64.wrapping_rem(y).wrapping_rem(z)
}

// =============================================================================
// Combination with other operations (derive zero, then remainder)
// =============================================================================

fn test_wrapping_rem_after_clamp_u32() {
    for x in 0u32..100u32 {
        let zeroed = x.clamp(0, 0);
        let remainder = zeroed.wrapping_rem(13);
        assert!(remainder == 0);
    }
    println!("test_wrapping_rem_after_clamp_u32 PASS");
}

fn test_wrapping_rem_in_loop_u32() {
    for d in 1u32..32u32 {
        let remainder = 0u32.wrapping_rem(d);
        assert!(remainder == 0);
    }
    println!("test_wrapping_rem_in_loop_u32 PASS");
}

fn main() {
    // Constant zero remainder
    assert!(test_wrapping_rem_zero_u8_const() == 0);
    assert!(test_wrapping_rem_zero_u16_const() == 0);
    assert!(test_wrapping_rem_zero_u32_const() == 0);
    assert!(test_wrapping_rem_zero_u64_const() == 0);

    // Parameterized zero remainder
    assert!(test_wrapping_rem_zero_u8(0, 5) == 0);
    assert!(test_wrapping_rem_zero_u8(0, 255) == 0);
    assert!(test_wrapping_rem_zero_u16(0, 1000) == 0);
    assert!(test_wrapping_rem_zero_u32(0, 1) == 0);
    assert!(test_wrapping_rem_zero_u64(0, 100) == 0);

    // Chain tests
    assert!(test_wrapping_rem_chain_u32(3, 7) == 0);
    assert!(test_wrapping_rem_chain_u64(11, 13) == 0);

    // Loop tests
    test_wrapping_rem_after_clamp_u32();
    test_wrapping_rem_in_loop_u32();

    println!("All wrapping_rem_bounds_test tests passed!");
}
