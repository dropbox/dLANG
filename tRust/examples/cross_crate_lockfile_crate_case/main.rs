//! Main crate for spec lockfile testing
//!
//! This test verifies that:
//! 1. External contracts are tracked with spec_hashes
//! 2. --write-spec-lockfile generates a lockfile
//! 3. --spec-lockfile loads and checks expected hashes
//!
//! Test workflow (handled by run_tests.sh):
//! 1. Compile dep.rs as library with -Zverify
//! 2. Compile main.rs with --write-spec-lockfile=test.lock
//! 3. Verify lockfile contains dep::abs_value, dep::clamp_max, dep::bounded_percent
//! 4. Compile again with --spec-lockfile=test.lock (should pass - no changes)

#![crate_type = "bin"]
#![trust_level = "verified"]

extern crate dep;

/// Uses abs_value from dep - should use its postcondition (result >= 0)
#[ensures("result >= 0")]
fn use_abs(x: i32) -> i32 {
    dep::abs_value(x)
}

/// Uses clamp_max from dep - should verify preconditions (n > 0, val >= 0)
#[requires("n > 0")]
#[requires("val >= 0")]
#[ensures("result <= n")]
#[ensures("result >= 0")]
fn use_clamp(val: i32, n: i32) -> i32 {
    dep::clamp_max(val, n)
}

/// Uses bounded_percent from dep - should use both postconditions
#[ensures("result >= 0")]
#[ensures("result <= 100")]
fn use_bounded(x: i32) -> i32 {
    dep::bounded_percent(x)
}

/// Combines multiple external calls
#[requires("n > 0")]
#[ensures("result >= 0")]
#[ensures("result <= n")]
fn combined_usage(x: i32, n: i32) -> i32 {
    let abs_x = dep::abs_value(x);
    dep::clamp_max(abs_x, n)
}

fn main() {}
