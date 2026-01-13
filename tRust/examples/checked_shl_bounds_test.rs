// Test checked_shl verification contracts
//
// checked_shl semantics: shift left that returns Option.
// Returns Some(x << n) when n < bit_width, returns None when n >= bit_width.
//
// This test focuses on solver-friendly properties:
// - (x == 0 && n < bit_width) => checked_shl returns Some(0)
// - Zero propagates through chains of checked_shl (when shift amounts are in-range)
//
// @expect: VERIFIED

// =============================================================================
// Constant tests (zero input)
// =============================================================================

#[ensures("result == 0")]
fn test_checked_shl_zero_u8_const() -> u8 {
    if let Some(r) = 0u8.checked_shl(3) { r } else { 0 }
}

#[ensures("result == 0")]
fn test_checked_shl_zero_u16_const() -> u16 {
    if let Some(r) = 0u16.checked_shl(7) { r } else { 0 }
}

#[ensures("result == 0")]
fn test_checked_shl_zero_u32_const() -> u32 {
    if let Some(r) = 0u32.checked_shl(31) { r } else { 0 }
}

#[ensures("result == 0")]
fn test_checked_shl_zero_i32_const() -> i32 {
    if let Some(r) = 0i32.checked_shl(17) { r } else { 0 }
}

#[ensures("result == 0")]
fn test_checked_shl_zero_i64_const() -> i64 {
    if let Some(r) = 0i64.checked_shl(63) { r } else { 0 }
}

// =============================================================================
// Constant tests (shift by zero is in-range)
// =============================================================================

#[ensures("result == 123")]
fn test_checked_shl_by_zero_u8_const() -> u8 {
    if let Some(r) = 123u8.checked_shl(0) { r } else { 0 }
}

#[ensures("result == 4567")]
fn test_checked_shl_by_zero_u16_const() -> u16 {
    if let Some(r) = 4567u16.checked_shl(0) { r } else { 0 }
}

#[ensures("result == 0xDEADBEEF")]
fn test_checked_shl_by_zero_u32_const() -> u32 {
    if let Some(r) = 0xDEADBEEFu32.checked_shl(0) { r } else { 0 }
}

// =============================================================================
// Parameterized tests (zero input)
// =============================================================================

#[requires("x == 0")]
#[requires("n < 8")]
#[ensures("result == 0")]
fn test_checked_shl_zero_u8(x: u8, n: u32) -> u8 {
    if let Some(r) = x.checked_shl(n) { r } else { 0 }
}

#[requires("x == 0")]
#[requires("n < 16")]
#[ensures("result == 0")]
fn test_checked_shl_zero_u16(x: u16, n: u32) -> u16 {
    if let Some(r) = x.checked_shl(n) { r } else { 0 }
}

#[requires("x == 0")]
#[requires("n < 32")]
#[ensures("result == 0")]
fn test_checked_shl_zero_u32(x: u32, n: u32) -> u32 {
    if let Some(r) = x.checked_shl(n) { r } else { 0 }
}

#[requires("x == 0")]
#[requires("n < 32")]
#[ensures("result == 0")]
fn test_checked_shl_zero_i32(x: i32, n: u32) -> i32 {
    if let Some(r) = x.checked_shl(n) { r } else { 0 }
}

#[requires("x == 0")]
#[requires("n < 64")]
#[ensures("result == 0")]
fn test_checked_shl_zero_i64(x: i64, n: u32) -> i64 {
    if let Some(r) = x.checked_shl(n) { r } else { 0 }
}

// =============================================================================
// Chained operations
// =============================================================================

#[requires("n < 32")]
#[requires("m < 32")]
#[ensures("result == 0")]
fn test_checked_shl_chain_u32(n: u32, m: u32) -> u32 {
    let first = if let Some(r) = 0u32.checked_shl(n) { r } else { return 0; };
    if let Some(r) = first.checked_shl(m) { r } else { 0 }
}

#[requires("n < 32")]
#[requires("m < 32")]
#[ensures("result == 0")]
fn test_checked_shl_chain_i32(n: u32, m: u32) -> i32 {
    let first = if let Some(r) = 0i32.checked_shl(n) { r } else { return 0; };
    if let Some(r) = first.checked_shl(m) { r } else { 0 }
}

// =============================================================================
// Runtime verification of None cases and basic behavior
// =============================================================================

fn test_checked_shl_out_of_range_is_none() {
    assert!(1u8.checked_shl(8).is_none());
    assert!(1u16.checked_shl(16).is_none());
    assert!(1u32.checked_shl(32).is_none());
    assert!(1u64.checked_shl(64).is_none());
    assert!(1i32.checked_shl(32).is_none());
    assert!(1i64.checked_shl(64).is_none());
    println!("test_checked_shl_out_of_range_is_none PASS");
}

fn test_checked_shl_zero_is_some_zero_in_range() {
    for n in 0u32..32u32 {
        let r = 0u32.checked_shl(n);
        assert!(r.is_some());
        assert!(r.unwrap() == 0);
    }
    println!("test_checked_shl_zero_is_some_zero_in_range PASS");
}

fn test_checked_shl_shift_by_zero_is_identity_runtime() {
    for x in 0u32..256u32 {
        assert_eq!(x.checked_shl(0).unwrap(), x);
    }
    println!("test_checked_shl_shift_by_zero_is_identity_runtime PASS");
}

fn main() {
    // Constant zero input tests
    assert!(test_checked_shl_zero_u8_const() == 0);
    assert!(test_checked_shl_zero_u16_const() == 0);
    assert!(test_checked_shl_zero_u32_const() == 0);
    assert!(test_checked_shl_zero_i32_const() == 0);
    assert!(test_checked_shl_zero_i64_const() == 0);

    // Constant shift-by-zero tests
    assert!(test_checked_shl_by_zero_u8_const() == 123);
    assert!(test_checked_shl_by_zero_u16_const() == 4567);
    assert!(test_checked_shl_by_zero_u32_const() == 0xDEADBEEF);

    // Parameterized zero input tests
    assert!(test_checked_shl_zero_u8(0, 0) == 0);
    assert!(test_checked_shl_zero_u8(0, 7) == 0);
    assert!(test_checked_shl_zero_u16(0, 15) == 0);
    assert!(test_checked_shl_zero_u32(0, 31) == 0);
    assert!(test_checked_shl_zero_i32(0, 0) == 0);
    assert!(test_checked_shl_zero_i64(0, 63) == 0);

    // Chain tests
    assert!(test_checked_shl_chain_u32(3, 7) == 0);
    assert!(test_checked_shl_chain_i32(9, 11) == 0);

    // Runtime verification
    test_checked_shl_out_of_range_is_none();
    test_checked_shl_zero_is_some_zero_in_range();
    test_checked_shl_shift_by_zero_is_identity_runtime();

    println!("All checked_shl_bounds_test tests passed!");
}

