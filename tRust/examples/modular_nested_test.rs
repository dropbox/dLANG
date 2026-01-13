//! Test modular verification with nested calls and transitive preconditions
//!
//! This tests:
//! 1. Multi-level call chains with preconditions
//! 2. Precondition propagation through wrappers
//! 3. Preconditions that depend on postconditions from earlier calls
//!
//! Expected outcomes:
//! log_ish: @expect: VERIFIED
//! safe_wrapper: @expect: VERIFIED
//! double_wrapper: @expect: VERIFIED
//! uses_abs_first: @expect: VERIFIED
//! unsafe_call: @expect: DISPROVEN
//! sequential_safe: @expect: VERIFIED
//!
//! NOTE: Use saturating arithmetic to prevent overflow while testing modular verification.

#![allow(unused)]

// Base function: requires x > 0
#[requires("x > 0")]
fn log_ish(x: i32) -> i32 {
    if x >= 100 { 2 } else if x >= 10 { 1 } else { 0 }
}

// Wrapper that propagates the precondition correctly
#[requires("n > 0")]
fn safe_wrapper(n: i32) -> i32 {
    log_ish(n)
}

// Double wrapper - should also work
#[requires("m > 0")]
fn double_wrapper(m: i32) -> i32 {
    safe_wrapper(m)
}

// Uses abs to ensure precondition
// abs(x) + 1 > 0 always holds (since abs(x) >= 0)
// Use saturating arithmetic to prevent overflow on negation
#[requires("x > -2147483648")]
fn uses_abs_first(x: i32) -> i32 {
    let positive = if x >= 0 { x } else { 0i32.saturating_sub(x) };
    // positive >= 0, so positive + 1 > 0
    log_ish(positive.saturating_add(1))
}

// This function SHOULD FAIL: no precondition and argument can be <= 0
fn unsafe_call(x: i32) -> i32 {
    log_ish(x)  // ERROR: x might be <= 0
}

// Multiple calls: first call satisfies precondition for second
// Use saturating arithmetic to prevent overflow
#[requires("a >= 0 && a <= 2147483645")]
fn sequential_safe(a: i32) -> i32 {
    let first = log_ish(a + 1);  // a+1 > 0 when a >= 0
    let second = log_ish(a + 2); // a+2 > 0 when a >= 0
    first.saturating_add(second)
}

fn main() {
    println!("safe_wrapper(5) = {}", safe_wrapper(5));
    println!("double_wrapper(5) = {}", double_wrapper(5));
}
