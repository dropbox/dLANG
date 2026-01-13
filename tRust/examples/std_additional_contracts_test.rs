//! Test file for additional builtin contracts of std library functions.
//!
//! This tests the builtin contracts for:
//! - signum: result is -1, 0, or 1
//! - rem_euclid (signed): result is non-negative
//! - rem_euclid (unsigned): result < rhs
//! - wrapping_abs: result == x || result == -x
//!
//! These builtin contracts are assumed as postconditions when calling these functions,
//! allowing callers to prove their own postconditions based on these assumptions.
//!
//! @expect: VERIFIED

// Test: signum postcondition - result is -1, 0, or 1
#[ensures("result == 0 || result == 1 || result == -1")]
fn test_signum_contract(x: i32) -> i32 {
    x.signum()
}

// Test: using signum's postcondition to prove caller's postcondition
// signum returns -1, 0, or 1, so abs(signum(x)) <= 1
#[ensures("result <= 1")]
#[ensures("result >= 0")]
fn signum_abs_bounded(x: i32) -> i32 {
    let s = x.signum();
    // Since s is -1, 0, or 1, abs(s) is 0 or 1
    s.abs()
}

// Test: rem_euclid postcondition for signed - result is non-negative
// The builtin contract: (>= result 0)
#[requires("divisor != 0")]
#[ensures("result >= 0")]
fn test_rem_euclid_signed_contract(dividend: i32, divisor: i32) -> i32 {
    dividend.rem_euclid(divisor)
}

// Test: rem_euclid postcondition for unsigned - result < rhs
// The builtin contract: (and (>= result 0) (< result rhs))
#[requires("divisor > 0")]
#[ensures("result < divisor")]
fn test_rem_euclid_unsigned_contract(dividend: u32, divisor: u32) -> u32 {
    dividend.rem_euclid(divisor)
}

// Test: using rem_euclid's postcondition for array indexing
// If we use rem_euclid(x, len) where len > 0, result < len is always true
#[requires("len > 0")]
#[ensures("result < len")]
fn safe_index_via_rem_euclid(idx: u32, len: u32) -> u32 {
    // rem_euclid guarantees 0 <= result < len
    idx.rem_euclid(len)
}

// Test: wrapping_abs postcondition - result == x || result == -x
// This is useful when we don't need the non-negative guarantee of abs()
// but want to know the magnitude relationship
#[ensures("result == x || result == 0 - x")]
fn test_wrapping_abs_contract(x: i32) -> i32 {
    x.wrapping_abs()
}

// Test: combining signum with comparison
// signum(x) > 0 implies x > 0
// But we test that signum(positive) == 1
#[requires("x > 0")]
#[ensures("result == 1")]
fn signum_of_positive(x: i32) -> i32 {
    x.signum()
}

// Test: combining signum with comparison for negative
#[requires("x < 0")]
#[ensures("result == -1")]
fn signum_of_negative(x: i32) -> i32 {
    x.signum()
}

// Test: signum of zero
#[ensures("result == 0")]
fn signum_of_zero() -> i32 {
    0i32.signum()
}

fn main() {
    // Test signum contracts
    println!("test_signum_contract(-42) = {}", test_signum_contract(-42));
    println!("test_signum_contract(0) = {}", test_signum_contract(0));
    println!("test_signum_contract(42) = {}", test_signum_contract(42));
    println!("signum_abs_bounded(-5) = {}", signum_abs_bounded(-5));
    println!("signum_of_positive(10) = {}", signum_of_positive(10));
    println!("signum_of_negative(-10) = {}", signum_of_negative(-10));
    println!("signum_of_zero() = {}", signum_of_zero());

    // Test rem_euclid contracts (signed)
    println!("test_rem_euclid_signed_contract(-7, 4) = {}", test_rem_euclid_signed_contract(-7, 4));
    println!("test_rem_euclid_signed_contract(7, -4) = {}", test_rem_euclid_signed_contract(7, -4));
    println!("test_rem_euclid_signed_contract(-7, -4) = {}", test_rem_euclid_signed_contract(-7, -4));

    // Test rem_euclid contracts (unsigned)
    println!("test_rem_euclid_unsigned_contract(17, 5) = {}", test_rem_euclid_unsigned_contract(17, 5));
    println!("safe_index_via_rem_euclid(100, 10) = {}", safe_index_via_rem_euclid(100, 10));

    // Test wrapping_abs contracts
    println!("test_wrapping_abs_contract(-42) = {}", test_wrapping_abs_contract(-42));
    println!("test_wrapping_abs_contract(42) = {}", test_wrapping_abs_contract(42));
    // Note: wrapping_abs of MIN returns MIN (still negative), this is allowed by contract
    println!("test_wrapping_abs_contract(i32::MIN) = {}", test_wrapping_abs_contract(i32::MIN));

    println!("All additional std contracts tests passed!");
}
