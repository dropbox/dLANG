//! Simple modular verification test - without checked arithmetic complications
//!
//! This tests the core multi-call modular verification without the complexity
//! of checked arithmetic tuples.
//!
//! Expected outcomes:
//! clamp_positive: @expect: VERIFIED
//! single_call: @expect: VERIFIED
//! max_clamp: @expect: VERIFIED

#![allow(unused)]

// Helper that guarantees a non-negative result
// For simplicity: just return input if >= 0, else 0
#[ensures("result >= 0")]
fn clamp_positive(x: i32) -> i32 {
    if x < 0 { 0 } else { x }
}

// Single call - should work
#[ensures("result >= 0")]
fn single_call(x: i32) -> i32 {
    clamp_positive(x)
}

// Double call - tests multi-call invariants
// Since clamp_positive >= 0 for both calls, max >= 0
#[ensures("result >= 0")]
fn max_clamp(a: i32, b: i32) -> i32 {
    let ca = clamp_positive(a);
    let cb = clamp_positive(b);
    if ca > cb { ca } else { cb }
}

fn main() {
    println!("single_call(-5) = {}", single_call(-5));
    println!("max_clamp(3, -4) = {}", max_clamp(3, -4));
}
