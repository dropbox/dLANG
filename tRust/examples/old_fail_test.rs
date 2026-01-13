//! Test that should FAIL verification
//!
//! This spec is incorrect - result is NOT old(x) + 2
//!
//! Expected outcomes:
//! increment: @expect: DISPROVEN

// Expected: DISPROVEN (incorrect spec - returns x+1, not x+2)
// Use saturating_add to prevent overflow error
#[requires("x >= 0")]
#[ensures("result == old(x) + 2")]
fn increment(x: i32) -> i32 {
    x.saturating_add(1)  // Returns x+1, not x+2 -- should FAIL spec verification
}

fn main() {
    println!("increment(5) = {}", increment(5));
}
