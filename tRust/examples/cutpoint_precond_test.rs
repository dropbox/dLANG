//! Test file for cutpoint (loop) precondition checking in tRust
//!
//! This tests that call-site preconditions inside loops are properly
//! checked using block-level state substitutions.
//!
//! NOTE: Using saturating arithmetic to prevent overflow during loop testing.

#![allow(unused)]

// A function with a precondition and postcondition
#[requires("x > 0")]
#[ensures("result >= 0")]
fn safe_log(x: i32) -> i32 {
    x.saturating_sub(1)
}

// Loop that calls safe_log with a value derived from loop variable
// The precondition should be checked at the call point, not block entry
#[requires("n >= 1")]
#[invariant("i >= 0 && sum >= 0")]
fn loop_with_safe_call(n: i32) -> i32 {
    let mut i = 0;
    let mut sum: i32 = 0;
    while i < n {
        // At this call site, x = i + 1 which is > 0 since i >= 0
        let x = i.saturating_add(1);  // x is assigned in-block before call
        sum = sum.saturating_add(safe_log(x));  // Call happens after assignment
        i = i.saturating_add(1);
    }
    sum
}

// Loop that calls safe_log with potentially unsafe value
// This should DISPROVE because when i = 0, x = i = 0 violates precondition
#[requires("n >= 1")]
#[invariant("i >= 0 && sum >= 0")]
fn loop_with_unsafe_call(n: i32) -> i32 {
    let mut i = 0;
    let mut sum: i32 = 0;
    while i < n {
        // At this call site, x = i which could be 0 on first iteration
        let x = i;  // x is assigned in-block before call
        sum = sum.saturating_add(safe_log(x));  // UNSAFE: when i = 0, x = 0 violates x > 0
        i = i.saturating_add(1);
    }
    sum
}

// Loop with conditional call - should verify since branch ensures precondition
#[requires("n >= 1")]
#[invariant("i >= 0 && sum >= 0")]
fn loop_with_guarded_call(n: i32) -> i32 {
    let mut i = 0;
    let mut sum: i32 = 0;
    while i < n {
        if i > 0 {
            // Only call safe_log when i > 0
            sum = sum.saturating_add(safe_log(i));
        }
        i = i.saturating_add(1);
    }
    sum
}

fn main() {
    println!("loop_with_safe_call(5) = {}", loop_with_safe_call(5));
    println!("loop_with_guarded_call(5) = {}", loop_with_guarded_call(5));
    // Uncomment to see unsafe behavior:
    // println!("loop_with_unsafe_call(5) = {}", loop_with_unsafe_call(5));
}
