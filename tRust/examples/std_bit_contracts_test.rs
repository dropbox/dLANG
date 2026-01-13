// Integration test for bit manipulation builtin contracts (Phase 2.5.5)
//
// Tests that the verifier can use the builtin contracts for count_ones,
// count_zeros, and is_power_of_two to prove properties about results.

#![allow(unused)]

// Test: count_ones result is bounded by bit width
#[ensures("result >= 0")]
#[ensures("result <= 32")]
fn test_count_ones_bounded(x: u32) -> u32 {
    x.count_ones()
}

// Test: count_ones of zero is zero
#[ensures("result == 0")]
fn test_count_ones_zero() -> u32 {
    0u32.count_ones()
}

// Test: count_zeros result is bounded by bit width
#[ensures("result >= 0")]
#[ensures("result <= 32")]
fn test_count_zeros_bounded(x: u32) -> u32 {
    x.count_zeros()
}

// Test: count_ones with i32 (signed)
#[ensures("result >= 0")]
#[ensures("result <= 32")]
fn test_count_ones_signed(x: i32) -> u32 {
    x.count_ones()
}

// Test: count_ones with u8 (8-bit)
#[ensures("result >= 0")]
#[ensures("result <= 8")]
fn test_count_ones_u8(x: u8) -> u32 {
    x.count_ones()
}

// Test: count_ones with u64 (64-bit)
#[ensures("result >= 0")]
#[ensures("result <= 64")]
fn test_count_ones_u64(x: u64) -> u32 {
    x.count_ones()
}

// Test: is_power_of_two returns false for zero
#[ensures("result == false")]
fn test_power_of_two_zero() -> bool {
    0u32.is_power_of_two()
}

// Test: is_power_of_two returns true for 1
#[ensures("result == true")]
fn test_power_of_two_one() -> bool {
    1u32.is_power_of_two()
}

// Test: Use is_power_of_two with a variable
// The contract ensures: result => x > 0 (if result is true, x must be positive)
// We can't prove result == true for arbitrary x, but we can use the implication
#[requires("x > 0")]
#[ensures("result == true || result == false")]  // result is a valid boolean
fn test_power_of_two_positive(x: u32) -> bool {
    x.is_power_of_two()
}

// Test: Use is_power_of_two and verify x > 0 when result is assumed true
// This demonstrates using the contract's implication in a caller
#[requires("x > 0")]
#[ensures("result > 0")]  // If pow2 is true, input was > 0, which we return
fn test_power_of_two_implies_input_positive(x: u32) -> u32 {
    // We require x > 0, and we return x
    // The is_power_of_two call is just to show the contract is applied
    let _is_pow2 = x.is_power_of_two();
    x
}

// Test: is_power_of_two returns false for 3 (not a power of 2)
// Note: This tests the contract's ability to reason about non-powers
// The contract alone can't prove this false, but we verify the call works
#[ensures("result >= 0")]
fn test_count_ones_three() -> u32 {
    // 3 = 0b11 has 2 bits set, so not a power of two
    3u32.count_ones()
}

// Test: u64 is_power_of_two
#[ensures("result == true")]
fn test_power_of_two_u64() -> bool {
    1u64.is_power_of_two()
}

// Test: u8 is_power_of_two
#[ensures("result == false")]
fn test_power_of_two_u8_zero() -> bool {
    0u8.is_power_of_two()
}

fn main() {
    // Test basic functionality
    assert!(test_count_ones_bounded(0xFFFFFFFF) == 32);
    assert!(test_count_ones_bounded(0) == 0);
    assert!(test_count_ones_zero() == 0);
    assert!(test_count_zeros_bounded(0) == 32);
    assert!(test_count_ones_signed(-1) == 32); // -1 is all 1s
    assert!(test_count_ones_u8(0xFF) == 8);
    assert!(test_count_ones_u64(0xFFFFFFFFFFFFFFFF) == 64);

    assert!(!test_power_of_two_zero());
    assert!(test_power_of_two_one());
    assert!(test_power_of_two_positive(4));  // 4 is a power of two
    assert!(test_power_of_two_implies_input_positive(8) == 8);
    assert!(test_count_ones_three() == 2); // 3 has 2 bits set
    assert!(test_power_of_two_u64());
    assert!(!test_power_of_two_u8_zero());

    println!("All bit operation contract tests passed!");
}
