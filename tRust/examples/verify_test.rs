//! Test file for tRust verification
//!
//! Tests basic verification scenarios with specs.
//! Note: Specs use string literals due to attribute parsing limitations.
//!
//! Expected outcomes:
//! abs: @expect: VERIFIED
//! max: @expect: VERIFIED
//! should_fail: @expect: DISPROVEN

// Simple function with specs
// Expected: VERIFIED (postcondition always holds when precondition met)
// Precondition also prevents -x overflow (x != i32::MIN)
#[requires("x > 0")]
#[ensures("result >= 0")]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

// Function with two specs
// Expected: VERIFIED (both postconditions hold)
#[requires("a >= 0")]
#[requires("b >= 0")]
#[ensures("result >= a")]
#[ensures("result >= b")]
fn max(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

// Function that should FAIL verification (ensures false)
// Expected: DISPROVEN (postcondition result < 0 is false when x > 0)
#[requires("x > 0")]
#[ensures("result < 0")]
fn should_fail(x: i32) -> i32 {
    x
}

// Function with precondition to prevent overflow
// Demonstrates bounds checking
#[requires("x < 2147483647")]
fn no_specs(x: i32) -> i32 {
    x + 1
}

fn main() {
    println!("abs(-5) = {}", abs(-5));
    println!("max(3, 7) = {}", max(3, 7));
    println!("no_specs(10) = {}", no_specs(10));
}
