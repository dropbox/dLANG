//! Test for pure method inlining (L3 limitation fix)
//!
//! This test demonstrates the fix for L3: result.method() in specs.
//! When a method is marked with #[pure] and #[pure_returns("expr")],
//! the verifier can inline the method call in specs.
//!
//! Expected: VERIFIED (all functions pass verification)

#![allow(dead_code)]

// Simple tuple struct wrapper
pub struct Wrap(pub usize);

impl Wrap {
    // The #[pure_returns] attribute tells the verifier what this method returns
    // When we see result.get() in a spec, it will be replaced with result.0
    #[pure]
    #[pure_returns("self.0")]
    pub fn get(&self) -> usize {
        self.0
    }

    // Another accessor method
    #[pure]
    #[pure_returns("self.0")]
    pub fn value(&self) -> usize {
        self.0
    }
}

// Test: result.method() in postcondition
// This was L3 in solver_limitations.rs - previously DISPROVEN
// With pure_returns, this should now VERIFY
#[ensures("result.get() == 42")]
pub fn l3_method() -> Wrap {
    Wrap(42)
}

// Test: result.method() with parameter
#[ensures("result.get() == n")]
pub fn make_wrap(n: usize) -> Wrap {
    Wrap(n)
}

// Test: result.method() in comparison
#[ensures("result.value() > 0")]
pub fn positive_wrap() -> Wrap {
    Wrap(100)
}

// Test: Multiple method calls
#[ensures("result.get() == result.value()")]
pub fn self_consistent() -> Wrap {
    Wrap(10)
}

// Test: Method call on both sides of comparison
#[ensures("result.get() == 50")]
pub fn wrap_fifty() -> Wrap {
    Wrap(50)
}

// Baseline tests (no method calls) - these should always work
#[ensures("result == 99")]
pub fn baseline_int() -> usize {
    99
}

#[ensures("result.0 == 88")]
pub fn baseline_field() -> Wrap {
    Wrap(88)
}

fn main() {
    println!("l3_method().get() = {}", l3_method().get());
    println!("make_wrap(100).get() = {}", make_wrap(100).get());
    println!("positive_wrap().value() = {}", positive_wrap().value());
    println!("self_consistent().get() = {}", self_consistent().get());
    println!("wrap_fifty().get() = {}", wrap_fifty().get());
    println!("baseline_int() = {}", baseline_int());
    println!("baseline_field().0 = {}", baseline_field().0);
}
