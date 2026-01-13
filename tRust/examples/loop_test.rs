//! Test file for loop verification
//!
//! This file demonstrates loop invariant verification in tRust.
//! Functions with loops require invariants for sound verification.
//!
//! Expected outcomes:
//! sum_to_n_no_inv: @expect: DISPROVEN
//! sum_with_invariant: @expect: VERIFIED
//! count_up: @expect: VERIFIED

// Sum numbers from 0 to n-1 WITHOUT an invariant
// Expected: UNKNOWN (contains loop, no invariant provided)
// #[requires(n >= 0)]
// #[ensures(result >= 0)]
fn sum_to_n_no_inv(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n {
        sum = sum + i;
        i = i + 1;
    }
    sum
}

// Sum numbers from 0 to n-1 WITH an invariant
// Expected: PROVEN (invariant correctly describes loop state)
// The invariant must constrain BOTH sum and i for preservation to work:
// - sum >= 0: the sum is always non-negative
// - i >= 0: the loop counter is always non-negative
// NOTE: Now uses source variable names (sum, i) instead of MIR names (_2, _3)!
// #[requires(n >= 0)]
// #[ensures(result >= 0)]
// #[invariant(sum >= 0 && i >= 0)]
fn sum_with_invariant(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n {
        sum = sum + i;
        i = i + 1;
    }
    sum
}

// Simple counter that always stays non-negative
// Expected: PROVEN (invariant i >= 0 holds throughout loop)
// NOTE: Now uses source variable name (i) instead of MIR name (_2)!
// #[requires(n >= 0)]
// #[ensures(result >= 0)]
// #[invariant(i >= 0)]
fn count_up(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i = i + 1;
    }
    i
}

fn main() {}
