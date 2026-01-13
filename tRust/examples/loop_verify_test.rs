//! Test file for loop verification in tRust
//!
//! Tests loop invariant verification scenarios.
//!
//! Expected outcomes:
//! count_up: @expect: VERIFIED
//! sum_no_inv: @expect: DISPROVEN
//! sum_with_inv: @expect: VERIFIED

// Simple counter that stays non-negative
// Loop invariant: i >= 0
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

// Sum to n without invariant - should be UNKNOWN or warn
// #[requires(n >= 0)]
// #[ensures(result >= 0)]
fn sum_no_inv(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n {
        sum = sum + i;
        i = i + 1;
    }
    sum
}

// Sum with invariant
// #[requires(n >= 0)]
// #[ensures(result >= 0)]
// #[invariant(sum >= 0 && i >= 0)]
fn sum_with_inv(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n {
        sum = sum + i;
        i = i + 1;
    }
    sum
}

fn main() {
    println!("count_up(5) = {}", count_up(5));
    println!("sum_no_inv(5) = {}", sum_no_inv(5));
    println!("sum_with_inv(5) = {}", sum_with_inv(5));
}
