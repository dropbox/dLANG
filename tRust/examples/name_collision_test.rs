//! Test file for function name collision handling
//!
//! This test demonstrates that when two modules define functions with the same name,
//! the correct specifications are applied based on module path.
//!
//! Both name_collision_test::process and name_collision_test::inner::process exist
//! with different specifications.
//!
//! Expected outcomes:
//! name_collision_test::inner::process: @expect: VERIFIED
//! name_collision_test::process: @expect: VERIFIED
//! use_outer_process: @expect: VERIFIED
//! use_inner_process: @expect: VERIFIED

#![allow(unused)]

#[path = "name_collision_test/mod.rs"]
mod name_collision_test;

// Caller that uses the outer process (requires x >= 0, ensures result > 0)
// #[requires(a >= 0)]
// #[ensures(result > 0)]
fn use_outer_process(a: i32) -> i32 {
    name_collision_test::process(a)
}

// Caller that uses the inner process (requires x >= 5, ensures result >= 10)
// #[requires(a >= 5)]
// #[ensures(result >= 10)]
fn use_inner_process(a: i32) -> i32 {
    name_collision_test::inner::process(a)
}

fn main() {
    println!("outer: {}", use_outer_process(5));
    println!("inner: {}", use_inner_process(10));
}
