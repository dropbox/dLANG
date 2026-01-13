//! Test file for loop verification failures
//!
//! This test should FAIL verification - the postcondition is false.
//!
//! Expected outcomes:
//! should_fail_loop: @expect: DISPROVEN

// Expected: DISPROVEN (postcondition requires result > n, but loop returns n)
// #[requires(n > 0)]
// #[ensures(result > n)]
fn should_fail_loop(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i = i + 1;
    }
    i  // i equals n, not greater than n
}

fn main() {}
