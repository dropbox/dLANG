//! Integration test for builtin callee preconditions (Phase 2.5.5)
//!
//! These functions intentionally violate implicit preconditions of some
//! standard-library methods (e.g., ilog2 requires x > 0).
//!
//! @expect: ERROR

#![allow(unused)]

// ilog2(x) panics for x == 0; verifier should require x > 0 at call site.
#[ensures("result < 32")]
fn ilog2_without_requires(x: u32) -> u32 {
    x.ilog2()
}

// rem_euclid(rhs) panics for rhs == 0; verifier should require rhs != 0 at call site.
#[ensures("result >= 0")]
fn rem_euclid_without_requires(x: i32, rhs: i32) -> i32 {
    x.rem_euclid(rhs)
}

// clamp(min, max) panics if min > max; verifier should require min <= max at call site.
#[ensures("result >= min")]
#[ensures("result <= max")]
fn clamp_without_requires(x: i32, min: i32, max: i32) -> i32 {
    x.clamp(min, max)
}

fn main() {}

