//! Purity test - Phase 5.1
//!
//! Tests verification of pure functions.
//! Pure functions can only call other pure functions.
//!
//! Expected outcomes:
//! square: @expect: VERIFIED
//! sum_of_squares: @expect: VERIFIED
//! abs: @expect: VERIFIED
//! impure_increment: @expect: VERIFIED
//! pure_calling_impure: @expect: DISPROVEN
//!
//! NOTE: Use saturating/checked arithmetic to prevent overflow while testing purity.

// A pure function that computes the square of a number
// Use checked multiplication for safety
fn square(x: i32) -> i32 {
    x.saturating_mul(x)
}

// Another pure function that uses square
fn sum_of_squares(x: i32, y: i32) -> i32 {
    square(x).saturating_add(square(y))
}

// A pure function that doesn't call anything - should always pass purity check
// Precondition prevents negation overflow
#[requires("x > -2147483648")]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

// An impure function (no pure annotation) - modifies global state conceptually
fn impure_increment(x: i32) -> i32 {
    // In a real scenario, this might do I/O or modify global state
    x.saturating_add(1)
}

// A pure function that calls an impure function - should FAIL purity check
// This demonstrates that pure functions cannot call impure functions
fn pure_calling_impure(x: i32) -> i32 {
    impure_increment(x)  // Purity violation: calling impure function
}

fn main() {
    // Test pure functions
    println!("square(5) = {}", square(5));
    println!("sum_of_squares(3, 4) = {}", sum_of_squares(3, 4));
    println!("abs(-5) = {}", abs(-5));

    // Test impure function
    println!("impure_increment(10) = {}", impure_increment(10));

    // Test pure function calling impure
    println!("pure_calling_impure(10) = {}", pure_calling_impure(10));
}
