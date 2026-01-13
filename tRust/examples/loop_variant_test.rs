//! Test file for loop variant (termination) verification
//!
//! This file demonstrates loop variant verification in tRust.
//! Loop variants prove that loops terminate by showing a decreasing bound.
//!
//! A loop variant is an expression that:
//! 1. Is non-negative when the loop invariant holds
//! 2. Strictly decreases with each iteration
//!
//! Expected outcomes:
//! countdown_with_variant: @expect: VERIFIED
//! count_to_n_with_variant: @expect: VERIFIED
//! accumulate_with_variant: @expect: VERIFIED
//! variant_without_invariant: @expect: DISPROVEN

// Count down from n to 0 with a variant that proves termination
// Expected: PROVEN (variant n - i decreases each iteration)
// #[requires(n >= 0)]
// #[ensures(result == 0)]
// #[invariant(i >= 0 && i <= n)]
// #[variant(n - i)]
fn countdown_with_variant(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i = i + 1;
    }
    // After the loop, i == n
    n - i  // Returns 0
}

// Simple counter with variant equal to remaining iterations
// Expected: PROVEN (variant shows loop terminates)
// #[requires(n >= 0)]
// #[ensures(result >= 0)]
// #[invariant(count >= 0 && count <= n)]
// #[variant(n - count)]
fn count_to_n_with_variant(n: i32) -> i32 {
    let mut count = 0;
    while count < n {
        count = count + 1;
    }
    count
}

// Loop with a more complex variant (decreasing towards 0)
// Expected: PROVEN
// #[requires(n >= 0)]
// #[ensures(result >= 0)]
// #[invariant(i >= 0 && i <= n && sum >= 0)]
// #[variant(n - i)]
fn accumulate_with_variant(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n {
        sum = sum + i;
        i = i + 1;
    }
    sum
}

// Loop with variant but missing invariant - should warn
// Expected: UNKNOWN (variant requires invariant for verification)
// #[requires(n >= 0)]
// #[ensures(result >= 0)]
// #[variant(n - i)]
fn variant_without_invariant(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i = i + 1;
    }
    i
}

fn main() {}
