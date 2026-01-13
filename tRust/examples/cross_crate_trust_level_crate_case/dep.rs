//! Dependency crate with "audited" trust level
//!
//! This crate provides specifications from an external (audited) source.
//! The specs are trusted but not machine-verified.

#![crate_type = "lib"]
#![crate_name = "dep"]
#![trust_level = "audited"]

/// A function with an audited contract.
/// The postcondition is trusted but from an external source.
#[ensures("result >= 0")]
pub fn audited_abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

/// Another audited function for testing.
#[requires("n > 0")]
#[ensures("result <= n")]
pub fn audited_clamp(val: i32, n: i32) -> i32 {
    if val > n { n } else { val }
}
