//! Test file for may_diverge escape hatch
//!
//! This file demonstrates the #[may_diverge] annotation in tRust.
//! Functions marked with may_diverge can have loops without invariants
//! or recursion without decreases measures.
//!
//! Expected outcomes:
//! loop_may_diverge: @expect: VERIFIED
//! recursive_may_diverge: @expect: VERIFIED
//! loop_with_invariant: @expect: VERIFIED

// Loop WITHOUT invariant, but WITH may_diverge
// Expected: PROVEN (may_diverge skips loop invariant requirement)
// #[may_diverge]
// #[ensures(result >= 0)]
fn loop_may_diverge(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i = i + 1;
    }
    i
}

// Recursive function WITHOUT decreases measure, but WITH may_diverge
// Expected: PROVEN (may_diverge skips decreases requirement)
// #[may_diverge]
// #[requires(n >= 0)]
// #[ensures(result >= 0)]
fn recursive_may_diverge(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        recursive_may_diverge(n - 1)
    }
}

// Event loop example - intentionally infinite
// Expected: Status shows may_diverge is active
// #[may_diverge]
fn event_loop() {
    loop {
        // Process events forever
        let _ = 42;
    }
}

// Normal loop WITH invariant (for comparison)
// Expected: PROVEN (using invariant, not may_diverge)
// #[requires(n >= 0)]
// #[ensures(result >= 0)]
// #[invariant(i >= 0)]
fn loop_with_invariant(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i = i + 1;
    }
    i
}

fn main() {}
