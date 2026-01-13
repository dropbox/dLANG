//! Example: Increment function with arithmetic in specs
//!
//! Tests arithmetic expression support in specifications.
//! Uses #[requires] attributes for overflow protection.
//!
//! Expected outcomes:
//! increment: @expect: VERIFIED
//! add: @expect: VERIFIED
//! double: @expect: VERIFIED
//! decrement_capped: @expect: VERIFIED

#[requires("x >= 0 && x < 2147483647")]
#[ensures("result == x + 1")]
fn increment(x: i32) -> i32 {
    x + 1
}

#[requires("x > 0 && y > 0 && x < 1073741823 && y < 1073741823")]
#[ensures("result == x + y")]
fn add(x: i32, y: i32) -> i32 {
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

fn main() {
    println!("increment(5) = {}", increment(5));
    println!("add(3, 4) = {}", add(3, 4));
    println!("double(7) = {}", double(7));
    println!("decrement_capped(10) = {}", decrement_capped(10));
}
