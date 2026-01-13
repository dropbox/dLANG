//! Regression test for ContractsVerify MIR elision.
//!
//! This file is compiled by `./run_tests.sh` with:
//!   TRUST_CONTRACTS_VERIFY=1
//!   -Zcontract-checks
//!   -Zdump-mir=ContractsElide
//!
//! The test asserts that a trivially true contract is marked PROVEN and that the
//! `contract_check_requires` call is removed from MIR after the ContractsElide pass.

#![feature(contracts)]
#![allow(incomplete_features)]

use core::contracts::requires as contract_requires;

#[contract_requires(true)]
fn elide_me(x: i32) -> i32 {
    x
}

fn main() {
    let _ = elide_me(1);
}
