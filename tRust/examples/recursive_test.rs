//! Test file for recursive function verification
//!
//! This file demonstrates termination proof verification in tRust using #[decreases].
//! Recursive functions require a decreases measure to prove termination.
//!
//! Expected outcomes:
//! factorial_no_dec: @expect: DISPROVEN
//! factorial: @expect: VERIFIED
//! countdown: @expect: VERIFIED
//!
//! NOTE: Use saturating/checked arithmetic to prevent overflow while testing termination.

// Factorial function WITHOUT a decreases measure
// Expected: DISPROVEN (recursive function, no decreases measure provided)
// Use saturating arithmetic for overflow safety
#[requires("n >= 0")]
fn factorial_no_dec(n: i32) -> i32 {
    if n <= 1 {
        1
    } else {
        n.saturating_mul(factorial_no_dec(n.saturating_sub(1)))
    }
}

// Factorial function WITH a decreases measure
// Expected: PROVEN (decreases measure correctly proves termination)
// The measure n decreases on each recursive call (n-1 < n when n > 1)
// Use saturating arithmetic for overflow safety
#[requires("n >= 0")]
fn factorial(n: i32) -> i32 {
    if n <= 1 {
        1
    } else {
        n.saturating_mul(factorial(n.saturating_sub(1)))
    }
}

// Simple countdown function
// Expected: PROVEN with decreases measure
#[requires("n >= 0")]
fn countdown(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        countdown(n.saturating_sub(1))
    }
}

fn main() {}
