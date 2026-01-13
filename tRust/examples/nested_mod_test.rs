//! Test nested module spec loading
//! This tests that cargo-trust can load specs from nested module trees
//!
//! Expected outcomes:
//! nested_mod_test::inner::abs: @expect: VERIFIED
//! nested_mod_test::add_positive: @expect: VERIFIED
//! call_nested: @expect: VERIFIED

#![allow(unused)]

#[path = "nested_mod_test/mod.rs"]
mod nested_mod_test;

// #[ensures(result >= 0)]
fn call_nested(a: i32, b: i32) -> i32 {
    nested_mod_test::add_positive(a, b)
}

fn main() {
    println!("call_nested(3, -4) = {}", call_nested(3, -4));
}
