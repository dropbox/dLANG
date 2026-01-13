//! Integration test for spec_hash (Phase 2.5.4 - Spec Compatibility)
//!
//! This test verifies that spec_hash is computed for functions with specifications.
//! The spec_hash is a FNV-1a hash of the canonical form of specifications:
//! - Preconditions sorted alphabetically
//! - Postconditions sorted alphabetically
//! - Canonical string: "requires:{sorted}\nensures:{sorted}"
//!
//! Use with JSON output to see spec_hash values:
//!   TRUST_OUTPUT_FORMAT=json ./bin/trustc examples/spec_hash_test.rs
//!
//! Expected behavior:
//! - Functions with specs should have spec_hash in JSON output
//! - Functions without specs should have spec_hash: null
//! - Two functions with identical specs should have the same spec_hash

#![allow(dead_code)]

/// Function with single requires and ensures
/// Expected spec_hash: computed from "requires:x > 0\nensures:result > 0"
#[requires("x > 0")]
#[ensures("result > 0")]
fn single_spec(x: i32) -> i32 {
    x
}

/// Another function with SAME specs as single_spec
/// Should have the SAME spec_hash
#[requires("x > 0")]
#[ensures("result > 0")]
fn same_specs_as_single(x: i32) -> i32 {
    x  // Simplified to avoid overflow check
}

/// Function with different specs
/// Should have a DIFFERENT spec_hash
#[requires("x >= 0")]
#[ensures("result >= 0")]
fn different_specs(x: i32) -> i32 {
    x
}

/// Function with multiple specs (hash should be deterministic regardless of order)
/// Specs are sorted alphabetically for canonical form
#[requires("y > 0")]
#[requires("x > 0")]
#[requires("x < 1000000")]  // Constrain inputs to prevent overflow
#[requires("y < 1000000")]
#[ensures("result > y")]
#[ensures("result > x")]
fn multi_spec(x: i32, y: i32) -> i32 {
    x + y
}

/// Function with no specs
/// Should have spec_hash: null in JSON output
fn no_specs() -> i32 {
    42
}

fn main() {}
