//! Test modular verification with precondition checking
//!
//! This file tests that cargo-trust can:
//! 1. Check preconditions at call sites
//! 2. Provide counterexamples when preconditions aren't satisfied
//!
//! Expected outcomes:
//! safe_div: @expect: VERIFIED
//! wrapper_safe: @expect: VERIFIED
//! wrapper_unsafe: @expect: DISPROVEN

#![allow(unused)]

// safe_div requires divisor is not zero (and no i32::MIN / -1 overflow)
#[requires("b != 0")]
#[requires("a != -2147483648 || b != -1")]
fn safe_div(a: i32, b: i32) -> i32 {
    a / b
}

// This function satisfies safe_div's precondition because it has the same precondition
#[requires("y != 0")]
#[requires("x != -2147483648 || y != -1")]
fn wrapper_safe(x: i32, y: i32) -> i32 {
    safe_div(x, y)
}

// This function may NOT satisfy safe_div's precondition
// because it doesn't require n != 0
// (Expected: DISPROVEN due to missing precondition)
fn wrapper_unsafe(m: i32, n: i32) -> i32 {
    safe_div(m, n)
}

fn main() {
    println!("wrapper_safe(10, 2) = {}", wrapper_safe(10, 2));
}
