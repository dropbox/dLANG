// Test file for builtin contracts of std::cmp::{min,max} during modular verification.
//
// Verifies that calls to std::cmp::min/max can be used to prove caller postconditions
// even though the standard library functions do not carry #[ensures] attributes.
//
// Also includes a small modular-precondition test that uses `&&` to ensure modular
// precondition translation handles compound expressions.

// SHOULD PASS - builtin contract for std::cmp::min
#[requires("a < 128 && b < 128")]
#[ensures("result <= a")]
#[ensures("result <= b")]
fn min_contract_u8(a: u8, b: u8) -> u8 {
    std::cmp::min(a, b)
}

// SHOULD PASS - builtin contract for std::cmp::max
#[requires("a > -1000 && b > -1000")]
#[ensures("result >= a")]
#[ensures("result >= b")]
fn max_contract_i32(a: i32, b: i32) -> i32 {
    std::cmp::max(a, b)
}

// Callee has a compound precondition that must be checked at call sites.
#[requires("a < 10 && b < 10")]
#[ensures("result < 20")]
fn add_small(a: u8, b: u8) -> u8 {
    a + b
}

// SHOULD PASS - call-site precondition check must handle `&&`
#[requires("x < 5 && y < 5")]
#[ensures("result < 20")]
fn caller_conjunction(x: u8, y: u8) -> u8 {
    add_small(x, y)
}

fn main() {
    println!("min_contract_u8(30, 20) = {}", min_contract_u8(30, 20));
    println!("max_contract_i32(10, -5) = {}", max_contract_i32(10, -5));
    println!("caller_conjunction(3, 4) = {}", caller_conjunction(3, 4));
}

