//! Example: Functions with actual #[requires] and #[ensures] attributes
//!
//! This example demonstrates using Rust attributes for specifications.
//! The tRust compiler parses these directly at compile time.
//!
//! Syntax:
//!   #[requires("condition")]
//!   #[ensures("condition")]
//!   fn my_function(x: i32) -> i32 { ... }
//!
//! Expected outcomes:
//! increment: @expect: VERIFIED
//! add_positive: @expect: VERIFIED
//! double: @expect: VERIFIED
//! decrement_capped: @expect: VERIFIED
//! increment_old: @expect: VERIFIED

#[requires("x >= 0 && x < 2147483647")]
#[ensures("result == x + 1")]
fn increment(x: i32) -> i32 {
    x + 1
}

#[requires("x > 0 && y > 0 && x < 1073741823 && y < 1073741823")]
#[ensures("result == x + y")]
fn add_positive(x: i32, y: i32) -> i32 {
    x + y
}

#[requires("n >= 1 && n < 1073741824")]
#[ensures("result == n * 2")]
fn double(n: i32) -> i32 {
    n + n
}

#[requires("n > 0")]
#[ensures("result >= 0")]
#[ensures("result <= n - 1")]
fn decrement_capped(n: i32) -> i32 {
    if n <= 1 { 0 } else { n - 1 }
}

// Function with old() in postcondition
#[requires("x >= 0 && x < 2147483647")]
#[ensures("result == old(x) + 1")]
fn increment_old(x: i32) -> i32 {
    x + 1
}

fn main() {
    println!("increment(5) = {}", increment(5));
    println!("add_positive(3, 4) = {}", add_positive(3, 4));
    println!("double(7) = {}", double(7));
    println!("decrement_capped(10) = {}", decrement_capped(10));
    println!("increment_old(5) = {}", increment_old(5));
}
