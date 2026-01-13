//! Integration test for "assumed" trust level (Phase 2.5.4)
//!
//! When a crate has #![trust_level = "assumed"], all function specifications
//! are assumed to hold without verification. This is useful for legacy code
//! or third-party libraries where verification isn't possible.
//!
//! Expected behavior:
//! - Functions with specs should have status "assumed" in JSON output
//! - Verification should be skipped (faster compilation)
//! - The specs are still available for modular verification of callers

#![trust_level = "assumed"]
#![allow(dead_code)]

/// This function's postcondition would FAIL verification (incorrect!)
/// But with trust_level="assumed", it won't be verified - just assumed.
#[requires("x > 0")]
#[ensures("result > x")]  // Incorrect! identity doesn't satisfy result > x
fn assumed_identity(x: i32) -> i32 {
    x  // Bug: returns x, not x+1
}

/// This function has a correct spec but we skip verification anyway.
#[requires("a >= 0")]
#[requires("b >= 0")]
#[ensures("result >= a")]
#[ensures("result >= b")]
fn assumed_max(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

fn main() {}
