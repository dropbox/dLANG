//! Integration test for builtin callee preconditions (Phase 2.5.5)
//!
//! Tests preconditions for rounding and square root functions:
//! - div_ceil(rhs) requires rhs != 0
//! - next_multiple_of(rhs) requires rhs != 0
//! - isqrt() for signed types requires x >= 0
//!
//! @expect: ERROR

#![allow(unused)]
#![feature(int_roundings)]
#![feature(isqrt)]

// div_ceil(rhs) panics for rhs == 0; verifier should require rhs != 0 at call site.
#[ensures("result >= 0")]
fn div_ceil_without_requires(x: u32, rhs: u32) -> u32 {
    x.div_ceil(rhs)
}

// next_multiple_of(rhs) panics for rhs == 0; verifier should require rhs != 0 at call site.
#[ensures("result >= x")]
fn next_multiple_without_requires(x: u32, rhs: u32) -> u32 {
    x.next_multiple_of(rhs)
}

// isqrt() for signed types panics if x < 0; verifier should require x >= 0 at call site.
#[ensures("result >= 0")]
fn isqrt_without_requires(x: i32) -> i32 {
    x.isqrt()
}

fn main() {}
