//! Dependency crate for spec lockfile testing
//!
//! This crate provides contracts that will be tracked in the spec lockfile.
//! The spec_hash of these contracts is recorded when the main crate verifies.

#![crate_type = "lib"]
#![crate_name = "dep"]
#![trust_level = "verified"]

/// A function with a simple postcondition.
/// spec_hash is computed from the normalized spec text.
#[ensures("result >= 0")]
pub fn abs_value(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

/// A function with both precondition and postcondition.
/// Both are included in the spec_hash computation.
#[requires("n > 0")]
#[requires("val >= 0")]
#[ensures("result <= n")]
#[ensures("result >= 0")]
pub fn clamp_max(val: i32, n: i32) -> i32 {
    if val > n { n } else { val }
}

/// A function with multiple ensures clauses.
/// All postconditions are included in spec_hash.
#[ensures("result >= 0")]
#[ensures("result <= 100")]
pub fn bounded_percent(x: i32) -> i32 {
    if x < 0 { 0 }
    else if x > 100 { 100 }
    else { x }
}
