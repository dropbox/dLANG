//! Integration test for trust_level crate attribute (Phase 2.5.4)
//!
//! This test verifies that #![trust_level = "..."] crate attribute is recognized
//! and affects verification behavior.

#![trust_level = "verified"]
#![allow(dead_code)]

/// A simple function with a verifiable contract
#[requires("x >= 0")]
#[ensures("result >= x")]
fn identity_nonneg(x: i32) -> i32 {
    x
}

/// Another simple function
#[requires("n > 0")]
#[ensures("result <= n")]
fn clamp_to_n(val: i32, n: i32) -> i32 {
    if val > n { n } else { val }
}

fn main() {}
