//! Main crate that uses specs from an audited external crate
//!
//! This test verifies that:
//! 1. External crate trust levels are correctly detected
//! 2. Specs from audited crates can be used in verification
//! 3. Trust level is properly tracked through cross-crate calls

#![crate_type = "bin"]
#![trust_level = "verified"]

extern crate dep;

/// Uses the audited_abs function from the external crate.
/// Should use the postcondition (result >= 0) from dep.
#[ensures("result >= 0")]
fn use_audited_abs(x: i32) -> i32 {
    dep::audited_abs(x)
}

/// Uses the audited_clamp function from the external crate.
/// Should verify that caller satisfies precondition (n > 0).
#[requires("n > 0")]
#[ensures("result <= n")]
fn use_audited_clamp(val: i32, n: i32) -> i32 {
    dep::audited_clamp(val, n)
}

fn main() {}
