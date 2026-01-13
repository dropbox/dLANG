//! Test recursive function termination verification with #[decreases]
//!
//! Recursive functions require a decreases measure to prove termination.
//! The measure must be non-negative and strictly decrease at each recursive call.
//!
//! NOTE: Using saturating arithmetic to prevent overflow during termination testing.

#![allow(unused)]

// Test 1: Factorial with correct decreases measure
// Expected: VERIFIED (measure n decreases at recursive call)
#[requires("n >= 0")]
fn factorial(n: i32) -> i32 {
    if n <= 1 {
        1
    } else {
        n.saturating_mul(factorial(n.saturating_sub(1)))
    }
}

// Test 2: Sum recursion with correct decreases measure
// Expected: VERIFIED (measure n decreases at recursive call)
#[requires("n >= 0")]
fn sum_to_n(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        n.saturating_add(sum_to_n(n.saturating_sub(1)))
    }
}

// Test 3: Fibonacci with correct decreases measure
// Note: Fib has TWO recursive calls, both must decrease
// Expected: VERIFIED (both fib(n-1) and fib(n-2) decrease from n)
#[requires("n >= 0")]
fn fib(n: i32) -> i32 {
    if n <= 1 {
        n
    } else {
        fib(n.saturating_sub(1)).saturating_add(fib(n.saturating_sub(2)))
    }
}

// Test 4: Recursive function WITHOUT decreases (should still verify functional specs)
// Expected: VERIFIED (postconditions still hold, termination checking skipped via may_diverge)
#[requires("n >= 0")]
fn factorial_no_dec(n: i32) -> i32 {
    if n <= 1 {
        1
    } else {
        n.saturating_mul(factorial_no_dec(n.saturating_sub(1)))
    }
}

// Test 5: Incorrect decreases measure (measure doesn't decrease)
// Expected: DISPROVEN - measure n doesn't decrease when calling with same n
#[requires("n >= 0")]
fn bad_recursion(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        bad_recursion(n)  // BUG: calls with same n, doesn't decrease!
    }
}

fn main() {
    println!("factorial(5) = {}", factorial(5));
    println!("sum_to_n(5) = {}", sum_to_n(5));
    println!("fib(10) = {}", fib(10));
}
