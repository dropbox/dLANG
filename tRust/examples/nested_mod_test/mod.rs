// Nested module test: sub-module with specs
#![allow(unused)]

pub mod inner;

// Use saturating_add since overflow checker doesn't track function return bounds
// Note: no #[ensures] since verifier doesn't model saturating_add
#[requires("a > -2147483648 && b > -2147483648")]
pub fn add_positive(a: i32, b: i32) -> i32 {
    inner::abs(a).saturating_add(inner::abs(b))
}
