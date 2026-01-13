//! Test module for function name collision handling
//! Both this module and inner.rs define a function called `process`
//! with DIFFERENT specifications.

#![allow(unused)]

pub mod inner;

/// This process ensures result > 0 (positive)
#[requires("x >= 0 && x < 2147483646")]
#[ensures("result > 0")]
pub fn process(x: i32) -> i32 {
    x + 1
}
