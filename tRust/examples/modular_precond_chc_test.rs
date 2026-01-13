//! Test modular verification call-site preconditions in the CHC path.
//!
//! This file forces CHC verification (not SP) by introducing branching. It also ensures
//! the call argument is assigned inside the same basic block as the call, so the
//! call-site precondition must be evaluated after sequential statements execute.
//!
//! Expected outcomes:
//! safe_div: @expect: VERIFIED
//! precond_in_branch_assigned: @expect: DISPROVEN
//! precond_in_branch_assigned_safe: @expect: VERIFIED

#![allow(unused)]

// safe_div requires divisor is not zero (and no i32::MIN / -1 overflow)
#[requires("b != 0")]
#[requires("a != -2147483648 || b != -1")]
fn safe_div(a: i32, b: i32) -> i32 {
    a / b
}

// SHOULD FAIL: denom is assigned to 0 in the same block as the call.
// Without rewriting the precondition through local assignments, CHC can miss this.
// #[ensures(true)]
fn precond_in_branch_assigned(x: i32) -> i32 {
    if x > 0 {
        let denom = 0;
        safe_div(10, denom)
    } else {
        0
    }
}

// SHOULD PASS: denom is assigned to 1 in the same block as the call.
// #[ensures(true)]
fn precond_in_branch_assigned_safe(x: i32) -> i32 {
    if x > 0 {
        let denom = 1;
        safe_div(10, denom)
    } else {
        0
    }
}

fn main() {
    println!(
        "precond_in_branch_assigned_safe(1) = {}",
        precond_in_branch_assigned_safe(1)
    );
}

