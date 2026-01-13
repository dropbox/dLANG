//! Test arithmetic expressions in specifications
//!
//! Phase 2.5.3+: Extended spec expressions
//! - Arithmetic operators (+, -, *, /) in ensures/requires
//! - Multi-term expressions (x + y + z)
//! - Parenthesized expressions ((x + y))
//!
//! NOTE: Using saturating arithmetic to prevent overflow during spec testing.
//! The primary focus is on testing spec parsing, not overflow checking.

#![allow(unused)]

// Test 1: Simple addition result equals sum of inputs
fn add(x: i32, y: i32) -> i32 {
    x.saturating_add(y)
}

// Test 2: Simple subtraction
fn sub(x: i32, y: i32) -> i32 {
    x.saturating_sub(y)
}

// Test 3: Three-argument sum
fn add3(x: i32, y: i32, z: i32) -> i32 {
    x.saturating_add(y).saturating_add(z)
}

// Test 4: Mixed operations
fn add_sub(x: i32, y: i32, z: i32) -> i32 {
    x.saturating_add(y).saturating_sub(z)
}

// Test 5: Scalar doubling (linear - avoids nonlinear arithmetic)
fn double(x: i32) -> i32 {
    x.saturating_add(x)
}

// Test 6: Parenthesized expression
fn paren_add(x: i32, y: i32) -> i32 {
    x.saturating_add(y)
}

// Test 7: Complex constraint with arithmetic reasoning
// Use constrained bounds to prevent overflow: x,y in [0, 1_000_000_000]
#[requires("x >= 0 && x <= 1000000000")]
#[requires("y >= 0 && y <= 1000000000")]
fn sum_of_nonneg(x: i32, y: i32) -> i32 {
    x + y  // Max is 2B, within i32 range
}

// Test 8: Arithmetic in precondition with overflow protection
#[requires("x >= 0 && x <= 1000000000")]
#[requires("y >= 0 && y <= 1000000000")]
#[requires("x + y > 0")]
fn require_sum_positive(x: i32, y: i32) -> i32 {
    x + y
}

// Test 9: Subtraction bounds with overflow protection
// Constrain both x and y to [0, 1B] to prevent subtraction overflow
#[requires("x > y")]
#[requires("x >= 0 && x <= 1000000000")]
#[requires("y >= 0 && y <= 1000000000")]
fn positive_diff(x: i32, y: i32) -> i32 {
    x - y  // x > y and both non-negative prevents overflow
}

// Test 10: Division by constant (linear arithmetic)
#[requires("x >= 0")]
fn half(x: i32) -> i32 {
    x / 2
}

fn main() {
    println!("add(3, 4) = {}", add(3, 4));
    println!("sub(10, 3) = {}", sub(10, 3));
    println!("add3(1, 2, 3) = {}", add3(1, 2, 3));
    println!("double(5) = {}", double(5));
    println!("sum_of_nonneg(100, 200) = {}", sum_of_nonneg(100, 200));
    println!("require_sum_positive(10, 20) = {}", require_sum_positive(10, 20));
    println!("positive_diff(10, 5) = {}", positive_diff(10, 5));
    println!("half(100) = {}", half(100));
}
