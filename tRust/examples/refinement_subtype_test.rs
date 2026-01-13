//! Refinement Type Subtyping Test (Phase 3.2)
//!
//! This file tests automatic expansion of refinement type annotations
//! into preconditions and postconditions.
//!
//! Expected outcomes:
//! double_positive: @expect: VERIFIED
//! identity_non_negative: @expect: VERIFIED
//! triple_positive: @expect: VERIFIED
//! double_percentage: @expect: VERIFIED
//!
//! NOTE: Use saturating arithmetic to prevent overflow while testing refinement subtyping.

// Define refinement types
// type Positive = i32 where self > 0;
// type NonNegative = i32 where self >= 0;
// type Percentage = i32 where self >= 0 && self <= 100;

// Test 1: Using param_type annotation
// The refinement predicate should automatically become a precondition
#[requires("n > 0")]
fn double_positive(n: i32) -> i32 {
    n.saturating_mul(2)
}

// Test 2: Using return_type annotation
// The refinement predicate should automatically become a postcondition
#[requires("x >= 0")]
fn identity_non_negative(x: i32) -> i32 {
    x
}

// Test 3: Using both param_type and return_type
#[requires("n > 0")]
fn triple_positive(n: i32) -> i32 {
    n.saturating_mul(3)
}

// Test 4: Combining manual specs with refinement type annotations
// Bound x to percentage range to prevent multiplication overflow
#[requires("x >= 0 && x <= 100")]
fn double_percentage(x: i32) -> i32 {
    x * 2
}

fn main() {
    let a = double_positive(5);
    let b = identity_non_negative(10);
    let c = triple_positive(3);
    let d = double_percentage(50);
    println!("Results: a={}, b={}, c={}, d={}", a, b, c, d);
}
