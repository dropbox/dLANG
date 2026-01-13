//! Integration test for LLVM Verified Assumes (Phase 9.6)
//!
//! This test verifies that the LLVM assume injection infrastructure works correctly.
//! When TRUST_VERIFIED_ASSUMES=1 is set, verified operations should result in
//! llvm.assume calls being emitted during codegen.
//!
//! To run with assumes enabled:
//! ```bash
//! TRUST_VERIFIED_ASSUMES=1 cargo build --example llvm_assumes_test
//! ```
//!
//! Expected outcomes:
//! safe_add_u16: @expect: VERIFIED
//! safe_divide: @expect: VERIFIED
//! safe_modulo: @expect: VERIFIED
//! identity_i32: @expect: VERIFIED

#![allow(unused)]

/// A function with proven-safe arithmetic using u16 to avoid overflow.
/// After verification proves no overflow (u16 values fit in u32), this fact
/// can be communicated to LLVM.
#[requires("a <= 100")]
#[requires("b <= 100")]
#[ensures("result <= 200")]
fn safe_add_u16(a: u16, b: u16) -> u16 {
    a + b
}

/// A function with proven-safe division.
/// After verification proves divisor != 0, this fact can be communicated to LLVM.
/// The DivisionByZero assert kind will have an llvm.assume emitted when verified.
#[requires("divisor != 0")]
#[ensures("true")]
fn safe_divide(dividend: u32, divisor: u32) -> u32 {
    dividend / divisor
}

/// A function with proven-safe remainder operation.
/// After verification proves divisor != 0, this fact can be communicated to LLVM.
/// The RemainderByZero assert kind will have an llvm.assume emitted when verified.
#[requires("divisor != 0")]
#[ensures("true")]
fn safe_modulo(dividend: u32, divisor: u32) -> u32 {
    dividend % divisor
}

/// A simple identity function for verification demonstration.
#[requires("x >= 0")]
#[ensures("result == x")]
fn identity_i32(x: i32) -> i32 {
    x
}

fn main() {
    // Test safe arithmetic with assume
    let sum = safe_add_u16(50, 30);
    println!("safe_add_u16: {}", sum);

    // Test safe division with assume
    let quotient = safe_divide(100, 5);
    println!("safe_divide: {}", quotient);

    // Test safe modulo with assume (RemainderByZero)
    let remainder = safe_modulo(100, 7);
    println!("safe_modulo: {}", remainder);

    // Test identity
    let id = identity_i32(42);
    println!("identity_i32: {}", id);

    println!("LLVM assumes test completed successfully!");
}
