// Test file for #[ensures] postcondition verification
//
// Tests that postconditions are verified against function implementations.
//
// SHOULD PASS:
// - identity_u8: simple identity returns same value
// - clamp_positive: correctly bounds result between 1 and n
// - add_bounded: result is bounded by sum of bounds
// - abs_u8: absolute value is always non-negative (trivial for u8)
//
// SHOULD FAIL:
// - wrong_ensures: claims wrong property about return value

// SHOULD PASS - identity returns exactly what it received
#[requires("x <= 100")]
#[ensures("result == x")]
fn identity_u8(x: u8) -> u8 {
    x
}

// SHOULD PASS - clamp correctly constrains result
#[requires("n > 0")]
#[ensures("result >= 1")]
#[ensures("result <= n")]
fn clamp_positive(n: i32, val: i32) -> i32 {
    if val < 1 { 1 }
    else if val > n { n }
    else { val }
}

// SHOULD PASS - bounded addition gives bounded result
#[requires("a < 100 && b < 100")]
#[ensures("result < 200")]
fn add_bounded(a: u8, b: u8) -> u8 {
    a + b
}

// SHOULD PASS - inline min implementation (std::cmp::min has no postconditions)
#[requires("a < 128 && b < 128")]
#[ensures("result <= a")]
#[ensures("result <= b")]
fn min_value(a: u8, b: u8) -> u8 {
    if a <= b { a } else { b }
}

// SHOULD PASS - inline max implementation (std::cmp::max has no postconditions)
#[requires("a < 128 && b < 128")]
#[ensures("result >= a")]
#[ensures("result >= b")]
fn max_value(a: u8, b: u8) -> u8 {
    if a >= b { a } else { b }
}

// Test modular verification with a simple helper
#[requires("x < 100")]
#[ensures("result == x")]
fn identity_helper(x: u8) -> u8 {
    x
}

// SHOULD PASS - modular verification: caller uses callee's postcondition
#[requires("a < 50")]
#[ensures("result == a")]  // Since identity_helper(a) == a
fn use_identity_postcondition(a: u8) -> u8 {
    identity_helper(a)  // Callee requires a < 100, we have a < 50, so satisfied
}

// SHOULD FAIL - wrong postcondition (result is x, not x+1)
#[requires("x <= 100")]
#[ensures("result == x + 1")]
fn wrong_ensures(x: u8) -> u8 {
    x  // Wrong! Returns x, not x+1
}

fn main() {
    println!("identity_u8(42) = {}", identity_u8(42));
    println!("clamp_positive(10, 15) = {}", clamp_positive(10, 15));
    println!("add_bounded(50, 60) = {}", add_bounded(50, 60));
    println!("min_value(30, 20) = {}", min_value(30, 20));
    println!("max_value(30, 20) = {}", max_value(30, 20));
    println!("identity_helper(25) = {}", identity_helper(25));
    println!("use_identity_postcondition(25) = {}", use_identity_postcondition(25));
    println!("wrong_ensures(5) = {}", wrong_ensures(5));
}
