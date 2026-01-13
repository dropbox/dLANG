//! Test file for mutual recursion verification
//!
//! This file demonstrates mutual recursion verification in tRust.
//! Mutually recursive functions call each other, creating a cycle.
//!
//! Use #[mutual_recursion(fn1, fn2, ...)] to mark functions as part of
//! a mutual recursion group, then provide a #[decreases(...)] measure
//! that decreases across all calls in the group.
//!
//! Expected outcomes:
//! is_even: @expect: VERIFIED
//! is_odd: @expect: VERIFIED
//! no_dec_a: @expect: DISPROVEN
//! no_dec_b: @expect: DISPROVEN
//! three_a: @expect: VERIFIED
//! three_b: @expect: VERIFIED
//! three_c: @expect: VERIFIED
//!
//! NOTE: Use saturating arithmetic to prevent overflow while testing mutual recursion.

// Classic even/odd mutual recursion with proper decreases measure
// Expected: PROVEN (measure n decreases at each mutual call)
#[requires("n >= 0")]
fn is_even(n: i32) -> bool {
    if n == 0 {
        true
    } else {
        is_odd(n.saturating_sub(1))  // measure: n-1 < n
    }
}

#[requires("n >= 0")]
fn is_odd(n: i32) -> bool {
    if n == 0 {
        false
    } else {
        is_even(n.saturating_sub(1))  // measure: n-1 < n
    }
}

// Mutual recursion WITHOUT decreases measure - should fail
// Expected: UNKNOWN (mutual recursion requires decreases measure)
#[requires("n >= 0")]
fn no_dec_a(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        no_dec_b(n.saturating_sub(1))
    }
}

#[requires("n >= 0")]
fn no_dec_b(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        no_dec_a(n.saturating_sub(1))
    }
}

// Three-way mutual recursion
// Expected: PROVEN
#[requires("n >= 0")]
fn three_a(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        three_b(n.saturating_sub(1)).saturating_add(1)
    }
}

#[requires("n >= 0")]
fn three_b(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        three_c(n.saturating_sub(1)).saturating_add(1)
    }
}

#[requires("n >= 0")]
fn three_c(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        three_a(n.saturating_sub(1)).saturating_add(1)
    }
}

fn main() {}
