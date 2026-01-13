//! Multi-file spec parsing test module.
//!
//! Expected outcomes:
//! abs: @expect: VERIFIED

#![allow(unused)]

// Precondition prevents negation overflow on i32::MIN
#[requires("x > -2147483648")]
pub fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

fn main() {
    println!("abs(-5) = {}", abs(-5));
}
