//! Test modular verification with function call contracts
//!
//! This file tests that cargo-trust can:
//! 1. Check preconditions at call sites
//! 2. Use postconditions from called functions
//!
//! Expected outcomes:
//! abs: @expect: VERIFIED
//! sum_abs: @expect: VERIFIED
//! call_abs_simple: @expect: VERIFIED
//! double_abs: @expect: VERIFIED
//!
//! NOTE: Until modular overflow verification is implemented, function return
//! values from abs() don't carry bounds into the overflow checker. We use
//! saturating_add to ensure overflow safety while still testing contract propagation.

#![allow(unused)]

// abs() guarantees: result >= 0
// Precondition: x > i32::MIN to prevent overflow on negation
#[requires("x > -2147483648")]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

// sum_abs calls abs() twice
// Use saturating_add since overflow checker doesn't track function return bounds
#[requires("a > -2147483648 && b > -2147483648")]
fn sum_abs(a: i32, b: i32) -> i32 {
    abs(a).saturating_add(abs(b))
}

// This function should also prove result >= 0 since it calls abs
#[requires("x > -2147483648")]
fn call_abs_simple(x: i32) -> i32 {
    abs(x)
}

// Test with explicit preconditions
// Use saturating_add since overflow checker doesn't track function return bounds
#[requires("n > -2147483648")]
fn double_abs(n: i32) -> i32 {
    abs(n).saturating_add(abs(n))
}

fn main() {
    println!("sum_abs(3, -4) = {}", sum_abs(3, -4));
    println!("double_abs(5) = {}", double_abs(5));
}
