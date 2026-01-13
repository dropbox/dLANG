//! Integration test for L8: Nonlinear Arithmetic
//!
//! Tests verification of specs involving multiplication, division, and modulo,
//! demonstrating the automatic switch to QF_NIA logic when nonlinear operations
//! are detected in spec expressions.
//!
//! Expected: All test functions should VERIFY.

#![allow(dead_code)]

// Basic multiplication in postcondition (with bounds to prevent overflow)
#[requires("a >= 0 && a <= 1000")]
#[requires("b >= 0 && b <= 1000")]
#[ensures("result == a * b")]
fn multiply_bounded(a: i32, b: i32) -> i32 {
    a * b
}

// Simple power of 2 (constant multiplication, bounded to prevent overflow)
#[requires("x >= 0 && x <= 1000000")]
#[ensures("result == x * 2")]
fn double(x: i32) -> i32 {
    x * 2
}

// Square function (with tight bounds to prevent overflow)
#[requires("x >= 0")]
#[requires("x <= 46340")] // sqrt(i32::MAX) ~ 46340, prevents overflow
#[ensures("result >= 0")]
fn square(x: i32) -> i32 {
    x * x
}

// Division in specs (also requires NIA)
#[requires("divisor != 0")]
#[ensures("result == dividend / divisor")]
fn integer_divide(dividend: i32, divisor: i32) -> i32 {
    dividend / divisor
}

// Modulo in specs (also requires NIA)
#[requires("divisor != 0")]
#[ensures("result == dividend % divisor")]
fn modulo(dividend: i32, divisor: i32) -> i32 {
    dividend % divisor
}

// Product identity: 0 * anything = 0
#[requires("a >= 0 && a <= 100")]
#[ensures("result == 0")]
fn multiply_by_zero(a: i32) -> i32 {
    a * 0
}

// Product identity: 1 * anything = anything
#[requires("a >= 0 && a <= 1000000")]
#[ensures("result == a")]
fn multiply_by_one(a: i32) -> i32 {
    a * 1
}

// Division identity: x / 1 = x
#[ensures("result == x")]
fn divide_by_one(x: i32) -> i32 {
    x / 1
}

// Modulo identity: x % 1 = 0
#[ensures("result == 0")]
fn modulo_by_one(x: i32) -> i32 {
    x % 1
}

fn main() {
    // Test multiply
    assert_eq!(multiply_bounded(3, 4), 12);

    // Test double
    assert_eq!(double(7), 14);

    // Test square
    assert_eq!(square(5), 25);

    // Test division
    assert_eq!(integer_divide(17, 5), 3);
    assert_eq!(modulo(17, 5), 2);

    // Test identities
    assert_eq!(multiply_by_zero(42), 0);
    assert_eq!(multiply_by_one(42), 42);
    assert_eq!(divide_by_one(42), 42);
    assert_eq!(modulo_by_one(42), 0);

    println!("All nonlinear arithmetic tests pass!");
}
