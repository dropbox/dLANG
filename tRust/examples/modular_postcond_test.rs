//! Test modular verification with postcondition propagation
//!
//! This file tests that cargo-trust can:
//! 1. Check preconditions at call sites (callee requires)
//! 2. Use postconditions from called functions (callee ensures -> caller facts)
//!
//! Expected outcomes:
//! helper_positive: @expect: VERIFIED
//! use_helper_postcond: @expect: VERIFIED (key test - proves postcond propagation)
//! step_one: @expect: VERIFIED
//! step_two: @expect: VERIFIED
//! chain_postconds: @expect: VERIFIED (proves chained postconditions work)
//! add_one_bounded: @expect: VERIFIED
//! add_one_again: @expect: VERIFIED
//! math_chain: @expect: VERIFIED (proves bounded postconditions chain)
//! double_bound: @expect: VERIFIED
//! postcond_not_propagated: @expect: DISPROVEN (proves verification isn't unsound)
//!
//! The key tests are:
//! - use_helper_postcond: ONLY verifies if callee postconditions are assumed
//! - chain_postconds: ONLY verifies if chained postconditions flow correctly
//! - postcond_not_propagated: MUST fail to prove verification is sound

#![allow(unused)]

// Helper that guarantees positive result
// Bound x to prevent overflow on x + 1
#[requires("x >= 0 && x < 2147483647")]
#[ensures("result > 0")]
fn helper_positive(x: i32) -> i32 {
    x + 1
}

// This function uses helper_positive's postcondition to prove its own ensures
// Without postcondition propagation, this would NOT verify
#[requires("n >= 0 && n < 2147483647")]
#[ensures("result > 0")]
fn use_helper_postcond(n: i32) -> i32 {
    helper_positive(n)  // Caller knows: result > 0 (from callee's ensures)
}

// Chain of postconditions: A -> B -> C
// Include upper bound in postcondition so caller can verify step_two's requires
#[requires("x >= 0 && x < 2147483646")]
#[ensures("result >= 1 && result < 2147483647")]
fn step_one(x: i32) -> i32 {
    x + 1
}

#[requires("x >= 1 && x < 2147483647")]
#[ensures("result >= 2")]
fn step_two(x: i32) -> i32 {
    x + 1
}

// This function chains postconditions:
// 1. step_one(a) returns result >= 1 AND result < 2147483647
// 2. That satisfies step_two's requires (x >= 1 && x < 2147483647)
// 3. step_two returns result >= 2
#[requires("a >= 0 && a < 2147483646")]
#[ensures("result >= 2")]
fn chain_postconds(a: i32) -> i32 {
    let intermediate = step_one(a);  // intermediate >= 1 && intermediate < 2147483647
    step_two(intermediate)           // result >= 2
}

// Math operations with postcondition propagation
#[requires("x >= 0 && x < 100")]
#[ensures("result >= 0 && result < 101")]
fn add_one_bounded(x: i32) -> i32 {
    x + 1
}

#[requires("y >= 0 && y < 101")]
#[ensures("result >= 0 && result < 102")]
fn add_one_again(y: i32) -> i32 {
    y + 1
}

// Chain math operations using postconditions
#[requires("n >= 0 && n < 100")]
#[ensures("result >= 0 && result < 102")]
fn math_chain(n: i32) -> i32 {
    let first = add_one_bounded(n);   // first >= 0 && first < 101
    add_one_again(first)               // result >= 0 && result < 102
}

// Double bound: use helper and return first result
// This tests that postcondition (result > 0) is preserved through simple return
#[requires("a >= 0 && a < 2147483647")]
#[ensures("result > 0")]
fn double_bound(a: i32) -> i32 {
    helper_positive(a)  // x > 0, return x directly
}

// FAILURE CASE: This function should DISPROVE
// It claims result > 10, but helper_positive only guarantees result > 0
#[requires("n >= 0 && n < 2147483647")]
#[ensures("result > 10")]  // Wrong! helper_positive only gives result > 0
fn postcond_not_propagated(n: i32) -> i32 {
    helper_positive(n)  // Only guarantees result > 0, NOT result > 10
}

fn main() {
    println!("use_helper_postcond(5) = {}", use_helper_postcond(5));
    println!("chain_postconds(0) = {}", chain_postconds(0));
    println!("math_chain(50) = {}", math_chain(50));
    println!("double_bound(3) = {}", double_bound(3));
}
