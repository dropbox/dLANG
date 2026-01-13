//! Tests for restricted closure desugaring in spec translation.
//!
//! Expected outcomes:
//! option_some_and: @expect: VERIFIED
//! option_none_and: @expect: VERIFIED
//! result_ok_and: @expect: VERIFIED
//! result_err_and: @expect: VERIFIED

#![allow(dead_code)]

#[ensures("result.is_some_and(|x: i32| { x > 0 && x < 10 })")]
fn option_some_and() -> Option<i32> {
    Some(5)
}

#[ensures("!result.is_some_and(|x| x > 0)")]
fn option_none_and() -> Option<i32> {
    None
}

#[ensures("result.is_ok_and(|x| x == 42)")]
fn result_ok_and() -> Result<i32, i32> {
    Ok(42)
}

#[ensures("result.is_err_and(|e| e == -7)")]
fn result_err_and() -> Result<i32, i32> {
    Err(-7)
}

fn main() {
    println!("{:?}", option_some_and());
    println!("{:?}", option_none_and());
    println!("{:?}", result_ok_and());
    println!("{:?}", result_err_and());
}

