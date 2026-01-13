#![allow(dead_code)]

// Inner function: doubles a positive value
#[requires("x > 0")]
#[ensures("result > x")]
pub fn double_positive(x: i32) -> i32 {
    x * 2
}

// Outer function: doubles and adds one
// Relies on double_positive's postcondition (result > x)
// to establish result > x + 1 (since result = double(x) + 1 > x + 1)
#[requires("x > 0")]
#[ensures("result > x")]
pub fn double_plus_one(x: i32) -> i32 {
    double_positive(x) + 1
}

