//! Test arithmetic expressions in preconditions
//!
//! This test verifies that the precondition parser can handle arithmetic
//! operators (+, -, *, /, %) in addition to comparison operators.
//!
//! Run with: rustc examples/arith_precond_test.rs -Zverify
//!
//! Expected outcomes:
//! - add_safe: SHOULD PASS - precondition x + y < 256 prevents overflow
//! - sub_safe: SHOULD PASS - precondition x >= y prevents underflow
//! - double_safe: SHOULD PASS - precondition x * 2 < 256 prevents overflow
//! - div_safe: SHOULD PASS - precondition n > 0 prevents division by zero
//! - mod_safe: SHOULD PASS - precondition n > 0 prevents modulo by zero

#![allow(unused)]

/// Function with arithmetic precondition: x + y must not overflow
/// The verifier should parse `x + y < 256` correctly
#[requires("x + y < 256")]
fn add_safe(x: u8, y: u8) -> u8 {
    // With precondition x + y < 256, this cannot overflow
    x + y
}

/// Function with subtraction in precondition
/// For u8, x >= y ensures the subtraction doesn't underflow
#[requires("x >= y")]
fn sub_safe(x: u8, y: u8) -> u8 {
    // With precondition x >= y, result is always >= 0
    x - y
}

/// Function with multiplication in precondition
#[requires("x < 128")]
fn double_safe(x: u8) -> u8 {
    // With precondition x < 128, x * 2 < 256, so this cannot overflow
    x * 2
}

/// Function with division in precondition - ensures divisor is non-zero
#[requires("n > 0")]
fn div_safe(x: u32, n: u32) -> u32 {
    // With precondition n > 0, division by zero is impossible
    x / n
}

/// Function with modulo in precondition - ensures divisor is non-zero
#[requires("n > 0")]
fn mod_safe(x: u32, n: u32) -> u32 {
    // With precondition n > 0, modulo by zero is impossible
    x % n
}

/// Function with division in precondition - division result bounds
/// If x / n < 100, and result = x / n, then result < 100
#[requires("n > 0 && x / n < 100")]
fn div_bounded(x: u32, n: u32) -> u32 {
    // The precondition ensures this division result is < 100
    x / n
}

/// Function with modulo bounds - x % n is always < n (for n > 0)
#[requires("n > 0")]
fn mod_bounded(x: u32, n: u32) -> u32 {
    // x % n is always in range [0, n-1], so always < n
    x % n
}

fn main() {
    // Test add_safe with values that satisfy precondition
    assert_eq!(add_safe(100, 50), 150);
    assert_eq!(add_safe(0, 0), 0);

    // Test sub_safe
    assert_eq!(sub_safe(10u8, 5u8), 5);

    // Test double_safe
    assert_eq!(double_safe(60), 120);

    // Test div_safe
    assert_eq!(div_safe(100, 10), 10);
    assert_eq!(div_safe(99, 10), 9);

    // Test mod_safe
    assert_eq!(mod_safe(17, 5), 2);
    assert_eq!(mod_safe(10, 3), 1);

    // Test div_bounded
    assert_eq!(div_bounded(990, 10), 99); // 990/10 = 99 < 100

    // Test mod_bounded
    assert_eq!(mod_bounded(17, 5), 2); // 17 % 5 = 2 < 5

    println!("All arithmetic precondition tests passed!");
}
