//! Test upstream #![feature(contracts)] integration with tRust verification.
//!
//! This test uses the upstream Rust contracts feature.
//! The ContractsVerify pass in rustc_mir_transform extracts the contract closures
//! and verifies them using Z3/Z4 SMT solvers.
//!
//! Run with:
//!   TRUST_CONTRACTS_VERIFY=1 rustc examples/upstream_contracts_test.rs -Zcontract-checks --edition 2021
//!
//! Expected outcomes:
//! - positive_only: PROVEN - n > 0 ensures _arg1 > 0
//! - negate_positive: PROVEN - n > 0 ensures result (negated) < 0

#![feature(contracts)]
#![allow(incomplete_features)]

// Use the upstream contracts macros directly via their full path
use core::contracts::requires as contract_requires;
use core::contracts::ensures as contract_ensures;

/// A simple function with a precondition that n > 0.
/// The verifier should prove this at compile time.
#[contract_requires(n > 0)]
fn positive_only(n: i32) -> i32 {
    n
}

/// A function that negates a positive number.
/// Precondition: n > 0
/// Postcondition: result < 0
#[contract_requires(n > 0)]
#[contract_ensures(|result: &i32| *result < 0)]
fn negate_positive(n: i32) -> i32 {
    -n
}

/// A function with a simple addition precondition.
/// This tests arithmetic in contract conditions.
#[contract_requires(a >= 0 && b >= 0)]
fn add_nonneg(a: i32, b: i32) -> i32 {
    a + b
}

/// A function that demonstrates postcondition verification.
/// The postcondition states result >= 0 (which is true since a,b >= 0).
#[contract_requires(a >= 0 && b >= 0)]
#[contract_ensures(|result: &i32| *result >= 0)]
fn add_positive_both(a: i32, b: i32) -> i32 {
    a + b
}

/// A function that accepts either positive or zero values.
/// Tests OR short-circuit evaluation in contract extraction.
#[contract_requires(a > 0 || a == 0)]
fn accept_nonneg(a: i32) -> i32 {
    a
}

/// A function with a more complex OR condition.
/// Either a is positive, or b must be positive.
#[contract_requires(a > 0 || b > 0)]
fn at_least_one_positive(a: i32, b: i32) -> i32 {
    if a > 0 { a } else { b }
}

fn main() {
    // Test positive_only
    let x = positive_only(5);
    assert_eq!(x, 5);

    // Test negate_positive
    let y = negate_positive(10);
    assert_eq!(y, -10);

    // Test add_nonneg
    let z = add_nonneg(3, 4);
    assert_eq!(z, 7);

    // Test add_positive_both
    let w = add_positive_both(5, 3);
    assert_eq!(w, 8);

    // Test accept_nonneg (OR short-circuit)
    let v1 = accept_nonneg(5);  // a > 0 is true (short-circuits)
    assert_eq!(v1, 5);
    let v2 = accept_nonneg(0);  // a > 0 is false, a == 0 is true
    assert_eq!(v2, 0);

    // Test at_least_one_positive (OR short-circuit)
    let u = at_least_one_positive(3, -1);  // a > 0 is true
    assert_eq!(u, 3);

    println!("All upstream contracts tests passed!");
}
