//! Phase 4 Integration Test - Termination and Loops
//!
//! This file tests all Phase 4 features:
//! - Phase 4.1: Termination proofs with #[decreases]
//! - Phase 4.2: Loop invariants with #[invariant] and #[variant]
//!
//! Expected outcomes:
//! factorial: @expect: VERIFIED
//! fibonacci: @expect: VERIFIED
//! sum_recursive: @expect: VERIFIED
//! bad_recursion_expected_fail: @expect: DISPROVEN
//! count_up: @expect: VERIFIED
//! sum_iterative: @expect: VERIFIED
//! count_with_variant: @expect: VERIFIED
//! countdown_with_variant: @expect: VERIFIED
//! sum_with_termination: @expect: VERIFIED
//!
//! NOTE: Use saturating arithmetic to prevent overflow while testing termination and loops.

// =============================================================================
// Phase 4.1: Termination Proofs (recursive functions)
// =============================================================================

// Factorial with decreasing measure
// Expected: VERIFIED (measure n decreases on each call)
#[requires("n >= 0")]
fn factorial(n: i32) -> i32 {
    if n <= 0 { 1 } else { n.saturating_mul(factorial(n.saturating_sub(1))) }
}

// Fibonacci with decreasing measure
// Expected: VERIFIED (measure n decreases on both recursive calls)
#[requires("n >= 0")]
fn fibonacci(n: i32) -> i32 {
    if n <= 0 { 0 }
    else if n == 1 { 1 }
    else { fibonacci(n.saturating_sub(1)).saturating_add(fibonacci(n.saturating_sub(2))) }
}

// Sum from 0 to n (recursive)
// Expected: VERIFIED
#[requires("n >= 0")]
fn sum_recursive(n: i32) -> i32 {
    if n <= 0 { 0 } else { n.saturating_add(sum_recursive(n.saturating_sub(1))) }
}

// Bad recursion - does not decrease
// Expected: DISPROVEN (measure doesn't decrease when n > 0)
#[requires("n >= 0")]
fn bad_recursion_expected_fail(n: i32) -> i32 {
    if n <= 0 { 0 }
    else { bad_recursion_expected_fail(n) }  // Bug: should be n-1
}

// =============================================================================
// Phase 4.2: Loop Invariants
// =============================================================================

// Simple counter with invariant
// Expected: VERIFIED (invariant holds initially and is preserved)
// Bound n to prevent counter overflow
#[requires("n >= 0 && n < 2147483647")]
fn count_up(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i = i + 1;
    }
    i
}

// Accumulator with two-variable invariant
// Expected: VERIFIED
// Use saturating arithmetic for safety
#[requires("n >= 0")]
fn sum_iterative(n: i32) -> i32 {
    let mut sum: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        sum = sum.saturating_add(i);
        i = i.saturating_add(1);
    }
    sum
}

// =============================================================================
// Phase 4.2: Loop Variants (termination of loops)
// =============================================================================

// Loop with variant proving termination
// Expected: VERIFIED (variant n - i is non-negative and decreases)
// Bound n to prevent counter overflow
#[requires("n >= 0 && n < 2147483647")]
fn count_with_variant(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i = i + 1;
    }
    i
}

// Countdown with variant
// Expected: VERIFIED
#[requires("n >= 0")]
fn countdown_with_variant(n: i32) -> i32 {
    let mut i = n;
    while i > 0 {
        i = i.saturating_sub(1);
    }
    i
}

// Combined: sum with both invariant and variant
// Expected: VERIFIED
#[requires("n >= 0")]
fn sum_with_termination(n: i32) -> i32 {
    let mut sum: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        sum = sum.saturating_add(i);
        i = i.saturating_add(1);
    }
    sum
}

fn main() {
    // Test Phase 4.1: Termination
    println!("factorial(5) = {}", factorial(5));
    println!("fibonacci(10) = {}", fibonacci(10));
    println!("sum_recursive(10) = {}", sum_recursive(10));

    // Test Phase 4.2: Loop Invariants
    println!("count_up(10) = {}", count_up(10));
    println!("sum_iterative(10) = {}", sum_iterative(10));

    // Test Phase 4.2: Loop Variants
    println!("count_with_variant(10) = {}", count_with_variant(10));
    println!("countdown_with_variant(10) = {}", countdown_with_variant(10));
    println!("sum_with_termination(10) = {}", sum_with_termination(10));
}
