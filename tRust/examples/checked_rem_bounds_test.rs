// Test checked_rem verification contracts
//
// checked_rem semantics: remainder operation that returns Option.
// Returns Some(x % y) when y != 0, returns None when y == 0.
//
// This test focuses on solver-verified properties for unsigned types:
// - (x == 0 && y > 0) => checked_rem returns Some(0) (zero numerator)
// - Zero propagates through chains of checked_rem (when divisors are positive)
//
// Note: Array bounds propagation through checked_rem not tested here due to
// solver limitations. Remainder bounds (result < divisor for positive divisors)
// require additional VC IR modeling.
//
// @expect: VERIFIED

// =============================================================================
// Zero numerator tests (constants)
// =============================================================================

#[ensures("result == 0")]
fn test_checked_rem_zero_u8_const() -> u8 {
    if let Some(r) = 0u8.checked_rem(7) {
        r
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_rem_zero_u16_const() -> u16 {
    if let Some(r) = 0u16.checked_rem(100) {
        r
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_rem_zero_u32_const() -> u32 {
    if let Some(r) = 0u32.checked_rem(42) {
        r
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_rem_zero_u64_const() -> u64 {
    if let Some(r) = 0u64.checked_rem(999) {
        r
    } else {
        0
    }
}

// =============================================================================
// Zero numerator tests (parameterized)
// =============================================================================

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_checked_rem_zero_u8(x: u8, y: u8) -> u8 {
    if let Some(r) = x.checked_rem(y) {
        r
    } else {
        0
    }
}

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_checked_rem_zero_u16(x: u16, y: u16) -> u16 {
    if let Some(r) = x.checked_rem(y) {
        r
    } else {
        0
    }
}

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_checked_rem_zero_u32(x: u32, y: u32) -> u32 {
    if let Some(r) = x.checked_rem(y) {
        r
    } else {
        0
    }
}

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_checked_rem_zero_u64(x: u64, y: u64) -> u64 {
    if let Some(r) = x.checked_rem(y) {
        r
    } else {
        0
    }
}

// =============================================================================
// Chained operations (zero numerator propagates through remainder chains)
// =============================================================================

#[requires("y > 0")]
#[requires("z > 0")]
#[ensures("result == 0")]
fn test_checked_rem_chain_u32(y: u32, z: u32) -> u32 {
    let first = if let Some(r) = 0u32.checked_rem(y) { r } else { return 0; };
    if let Some(r) = first.checked_rem(z) { r } else { 0 }
}

#[requires("y > 0")]
#[requires("z > 0")]
#[ensures("result == 0")]
fn test_checked_rem_chain_u64(y: u64, z: u64) -> u64 {
    let first = if let Some(r) = 0u64.checked_rem(y) { r } else { return 0; };
    if let Some(r) = first.checked_rem(z) { r } else { 0 }
}

// =============================================================================
// Combination with other operations (derive zero, then compute remainder)
// =============================================================================

fn test_checked_rem_after_clamp_u32() {
    for x in 0u32..100u32 {
        let zeroed = x.clamp(0, 0);
        if let Some(remainder) = zeroed.checked_rem(13) {
            assert!(remainder == 0);
        }
    }
    println!("test_checked_rem_after_clamp_u32 PASS");
}

fn test_checked_rem_in_loop_u32() {
    for d in 1u32..32u32 {
        if let Some(remainder) = 0u32.checked_rem(d) {
            assert!(remainder == 0);
        }
    }
    println!("test_checked_rem_in_loop_u32 PASS");
}

// =============================================================================
// Zero divisor returns None
// =============================================================================

fn test_checked_rem_zero_divisor() {
    // Zero divisor should return None
    assert!(100u8.checked_rem(0).is_none());
    assert!(100u16.checked_rem(0).is_none());
    assert!(100u32.checked_rem(0).is_none());
    assert!(100u64.checked_rem(0).is_none());
    println!("test_checked_rem_zero_divisor PASS");
}

// =============================================================================
// Runtime verification of remainder properties
// =============================================================================

fn test_checked_rem_runtime_verification() {
    // Verify: result < divisor for positive divisors (when result is Some)
    for x in 0u32..256u32 {
        for d in 1u32..10u32 {
            if let Some(r) = x.checked_rem(d) {
                assert!(r < d, "Remainder {} should be < divisor {}", r, d);
            }
        }
    }

    // Verify: remainder of 0 % d is always 0
    for d in 1u32..256u32 {
        if let Some(r) = 0u32.checked_rem(d) {
            assert_eq!(r, 0, "Remainder of 0 should be 0");
        }
    }

    // Verify: x % 1 is always 0
    for x in 0u32..256u32 {
        if let Some(r) = x.checked_rem(1) {
            assert_eq!(r, 0, "Remainder by 1 should be 0");
        }
    }

    println!("test_checked_rem_runtime_verification PASS");
}

fn main() {
    // Constant zero numerator tests
    assert!(test_checked_rem_zero_u8_const() == 0);
    assert!(test_checked_rem_zero_u16_const() == 0);
    assert!(test_checked_rem_zero_u32_const() == 0);
    assert!(test_checked_rem_zero_u64_const() == 0);

    // Parameterized zero numerator tests
    assert!(test_checked_rem_zero_u8(0, 5) == 0);
    assert!(test_checked_rem_zero_u8(0, 255) == 0);
    assert!(test_checked_rem_zero_u16(0, 1000) == 0);
    assert!(test_checked_rem_zero_u32(0, 1) == 0);
    assert!(test_checked_rem_zero_u64(0, 100) == 0);

    // Chain tests
    assert!(test_checked_rem_chain_u32(3, 7) == 0);
    assert!(test_checked_rem_chain_u64(11, 13) == 0);

    // Zero divisor test
    test_checked_rem_zero_divisor();

    // Loop tests
    test_checked_rem_after_clamp_u32();
    test_checked_rem_in_loop_u32();

    // Runtime verification
    test_checked_rem_runtime_verification();

    println!("All checked_rem_bounds_test tests passed!");
}
