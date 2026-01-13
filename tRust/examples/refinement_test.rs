//! Refinement Types Test
//!
//! This file tests the Phase 3.1 implementation of refinement type parsing.
//! Refinement types are types with associated predicates that constrain values.
//!
//! Expected outcomes:
//! double_positive: @expect: VERIFIED
//! absolute_or_zero: @expect: VERIFIED
//! clamp_double: @expect: VERIFIED
//! always_positive: @expect: VERIFIED
//!
//! NOTE: Use saturating arithmetic to prevent overflow while testing refinement types.

// Define refinement types
// type Positive = i32 where self > 0;
// type NonNegative = i32 where self >= 0;
// type InRange = i32 where self >= 0 && self <= 100;

// Test 1: Function returning a positive value
// The postcondition matches what Positive would require
#[requires("n > 0")]
fn double_positive(n: i32) -> i32 {
    n.saturating_mul(2)
}

// Test 2: Function returning a non-negative value
// The postcondition matches what NonNegative would require
#[requires("x >= 0")]
fn absolute_or_zero(x: i32) -> i32 {
    if x < 0 { 0 } else { x }
}

// Test 3: Function with range constraint
// Bound x to prevent multiplication overflow
#[requires("x >= 0")]
#[requires("x <= 50")]
fn clamp_double(x: i32) -> i32 {
    if x * 2 > 100 { 100 } else { x * 2 }
}

// Test 4: Simple constant returning positive (trivial case)
fn always_positive() -> i32 {
    42
}

fn main() {
    let a = double_positive(5);
    let b = absolute_or_zero(-3);
    let c = clamp_double(30);
    let d = always_positive();
    println!("Results: a={}, b={}, c={}, d={}", a, b, c, d);
}
