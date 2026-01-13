#![allow(dead_code)]

#[requires("x >= 0")]
#[ensures("result >= 0")]
pub fn id_nonneg(x: i32) -> i32 {
    x
}

