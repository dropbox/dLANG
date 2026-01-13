// Inner module with specs
#![allow(unused)]

// Precondition: x > i32::MIN to prevent overflow on negation
#[requires("x > -2147483648")]
#[ensures("result >= 0")]
pub fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
