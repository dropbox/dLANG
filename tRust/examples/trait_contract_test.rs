//! Integration test for trait method specs (Phase 2.5.1)
//!
//! Tests that:
//! 1. Trait methods can have #[requires] and #[ensures] specs
//! 2. Impl methods inherit trait postconditions (must prove them)
//! 3. Impl methods can assume trait preconditions (callers must satisfy them)
//! 4. Callers using the trait can rely on the trait's contract

#![allow(dead_code)]

// Define a trait with specifications on its methods
trait Absolute {
    /// Precondition: x must not be i32::MIN (to avoid overflow)
    /// Postcondition: result is non-negative
    #[requires("x != -2147483648")]  // x != i32::MIN
    #[ensures("result >= 0")]
    fn abs(&self, x: i32) -> i32;
}

// Implement the trait - the impl must satisfy the trait's postcondition
struct MyAbs;

impl Absolute for MyAbs {
    // The impl inherits #[ensures("result >= 0")] from the trait
    // The impl can assume #[requires("x != -2147483648")]
    fn abs(&self, x: i32) -> i32 {
        if x < 0 { -x } else { x }
    }
}

// Test that a caller using the trait can rely on the contract
#[requires("val != -2147483648")]
#[ensures("result >= 0")]
fn use_absolute<A: Absolute>(a: &A, val: i32) -> i32 {
    // Can rely on trait's postcondition: result >= 0
    a.abs(val)
}

// Test with a concrete impl
#[requires("val != -2147483648")]
#[ensures("result >= 0")]
fn use_my_abs(val: i32) -> i32 {
    let a = MyAbs;
    a.abs(val)
}

fn main() {
    let a = MyAbs;
    println!("abs(-5) = {}", a.abs(-5));
    println!("abs(10) = {}", a.abs(10));
}
