//! Test that cargo-trust can load specs from Rust modules in separate files.
//!
//! Expected outcomes:
//! multifile_spec_mod::abs: @expect: VERIFIED
//! sum_abs: @expect: VERIFIED
//!
//! NOTE: Use saturating arithmetic to prevent overflow while testing multi-file specs.

#![allow(unused)]

mod multifile_spec_mod;

// sum_abs calls abs() twice from a module file.
// Since abs() ensures result >= 0, sum_abs should be able to prove result >= 0.
// Use saturating_add to prevent overflow
#[requires("a > -2147483648 && b > -2147483648")]
fn sum_abs(a: i32, b: i32) -> i32 {
    multifile_spec_mod::abs(a).saturating_add(multifile_spec_mod::abs(b))
}

fn main() {
    println!("sum_abs(3, -4) = {}", sum_abs(3, -4));
}
