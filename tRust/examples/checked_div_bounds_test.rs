// Test checked_div verification contracts
//
// checked_div semantics: division operation that returns Option.
// Returns Some(x / y) when y != 0, returns None when y == 0.
//
// This test focuses on solver-verified properties for unsigned types:
// - (x == 0 && y > 0) => checked_div returns Some(0) (zero numerator)
// - Zero propagates through chains of checked_div (when divisors are positive)
//
// Note: Array bounds propagation through checked_div not tested here due to
// solver limitations. Division bounds (result <= operand for positive divisors)
// require additional VC IR modeling.
//
// @expect: VERIFIED

// =============================================================================
// Zero numerator tests (constants)
// =============================================================================

#[ensures("result == 0")]
fn test_checked_div_zero_u8_const() -> u8 {
    if let Some(q) = 0u8.checked_div(7) {
        q
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_div_zero_u16_const() -> u16 {
    if let Some(q) = 0u16.checked_div(100) {
        q
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_div_zero_u32_const() -> u32 {
    if let Some(q) = 0u32.checked_div(42) {
        q
    } else {
        0
    }
}

#[ensures("result == 0")]
fn test_checked_div_zero_u64_const() -> u64 {
    if let Some(q) = 0u64.checked_div(999) {
        q
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
fn test_checked_div_zero_u8(x: u8, y: u8) -> u8 {
    if let Some(q) = x.checked_div(y) {
        q
    } else {
        0
    }
}

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_checked_div_zero_u16(x: u16, y: u16) -> u16 {
    if let Some(q) = x.checked_div(y) {
        q
    } else {
        0
    }
}

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_checked_div_zero_u32(x: u32, y: u32) -> u32 {
    if let Some(q) = x.checked_div(y) {
        q
    } else {
        0
    }
}

#[requires("x == 0")]
#[requires("y > 0")]
#[ensures("result == 0")]
fn test_checked_div_zero_u64(x: u64, y: u64) -> u64 {
    if let Some(q) = x.checked_div(y) {
        q
    } else {
        0
    }
}

// =============================================================================
// Chained operations (zero numerator propagates through division chains)
// =============================================================================

#[requires("y > 0")]
#[requires("z > 0")]
#[ensures("result == 0")]
fn test_checked_div_chain_u32(y: u32, z: u32) -> u32 {
    let first = if let Some(q) = 0u32.checked_div(y) { q } else { return 0; };
    if let Some(q) = first.checked_div(z) { q } else { 0 }
}

#[requires("y > 0")]
#[requires("z > 0")]
#[ensures("result == 0")]
fn test_checked_div_chain_u64(y: u64, z: u64) -> u64 {
    let first = if let Some(q) = 0u64.checked_div(y) { q } else { return 0; };
    if let Some(q) = first.checked_div(z) { q } else { 0 }
}

// =============================================================================
// Combination with other operations (derive zero, then divide)
// =============================================================================

fn test_checked_div_after_clamp_u32() {
    for x in 0u32..100u32 {
        let zeroed = x.clamp(0, 0);
        if let Some(quotient) = zeroed.checked_div(13) {
            assert!(quotient == 0);
        }
    }
    println!("test_checked_div_after_clamp_u32 PASS");
}

fn test_checked_div_in_loop_u32() {
    for d in 1u32..32u32 {
        if let Some(quotient) = 0u32.checked_div(d) {
            assert!(quotient == 0);
        }
    }
    println!("test_checked_div_in_loop_u32 PASS");
}

// =============================================================================
// Zero divisor returns None
// =============================================================================

fn test_checked_div_zero_divisor() {
    // Zero divisor should return None
    assert!(100u8.checked_div(0).is_none());
    assert!(100u16.checked_div(0).is_none());
    assert!(100u32.checked_div(0).is_none());
    assert!(100u64.checked_div(0).is_none());
    println!("test_checked_div_zero_divisor PASS");
}

// =============================================================================
// Runtime verification of division properties
// =============================================================================

fn test_checked_div_runtime_verification() {
    // Verify: result <= numerator for positive divisors
    for x in 0u32..256u32 {
        for d in 1u32..10u32 {
            if let Some(q) = x.checked_div(d) {
                assert!(q <= x, "Division result {} should be <= numerator {}", q, x);
            }
        }
    }

    // Verify: division by 1 preserves value
    for x in 0u32..256u32 {
        if let Some(q) = x.checked_div(1) {
            assert_eq!(q, x, "Division by 1 should preserve value");
        }
    }

    println!("test_checked_div_runtime_verification PASS");
}

fn main() {
    // Constant zero numerator tests
    assert!(test_checked_div_zero_u8_const() == 0);
    assert!(test_checked_div_zero_u16_const() == 0);
    assert!(test_checked_div_zero_u32_const() == 0);
    assert!(test_checked_div_zero_u64_const() == 0);

    // Parameterized zero numerator tests
    assert!(test_checked_div_zero_u8(0, 5) == 0);
    assert!(test_checked_div_zero_u8(0, 255) == 0);
    assert!(test_checked_div_zero_u16(0, 1000) == 0);
    assert!(test_checked_div_zero_u32(0, 1) == 0);
    assert!(test_checked_div_zero_u64(0, 100) == 0);

    // Chain tests
    assert!(test_checked_div_chain_u32(3, 7) == 0);
    assert!(test_checked_div_chain_u64(11, 13) == 0);

    // Zero divisor test
    test_checked_div_zero_divisor();

    // Loop tests
    test_checked_div_after_clamp_u32();
    test_checked_div_in_loop_u32();

    // Runtime verification
    test_checked_div_runtime_verification();

    println!("All checked_div_bounds_test tests passed!");
}
