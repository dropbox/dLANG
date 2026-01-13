//! Hello Verified World
//!
//! The first real Rust file to be verified by tRust.
//!
//! Expected outcomes:
//! clamp_positive: @expect: VERIFIED

#![trust_level = "verified"]

// Expected: VERIFIED (all postconditions proven)
#[requires("n > 0")]
#[ensures("result >= 1")]
#[ensures("result <= n")]
fn clamp_positive(n: i32, val: i32) -> i32 {
    if val < 1 {
        1
    } else if val > n {
        n
    } else {
        val
    }
}

fn main() {
    let x = clamp_positive(10, 15);
    println!("Clamped: {}", x);
}
