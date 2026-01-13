//! Inner module with a different spec for `process`
//! This version ensures result >= 10 (larger bound)

#![allow(unused)]

/// This process ensures result >= 10 (larger bound)
#[requires("x >= 5 && x < 2147483642")]
#[ensures("result >= 10")]
pub fn process(x: i32) -> i32 {
    x + 5
}
