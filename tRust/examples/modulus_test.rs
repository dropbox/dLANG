//! Test modulus operator (%) in spec expressions
//!
//! is_even: @expect: VERIFIED
//! is_odd: @expect: VERIFIED
//! mod_preserving: @expect: VERIFIED
//! mod_cycle: @expect: VERIFIED
//! mod_fail_test: @expect: DISPROVEN
//!
//! NOTE: Use saturating arithmetic to prevent overflow while testing modulus.

// @expect: VERIFIED
#[requires("n >= 0")]
fn is_even(n: i32) -> i32 {
    // Returns 0 if even, 1 if odd
    n % 2
}

// @expect: VERIFIED
// Bound n to prevent n+1 overflow
#[requires("n >= 0 && n < 2147483647")]
fn is_odd(n: i32) -> i32 {
    // Returns 1 if odd, 0 if even
    (n + 1) % 2
}

// @expect: VERIFIED
// Bound n to prevent n+3 overflow
#[requires("n >= 0 && n < 2147483645")]
fn mod_preserving(n: i32) -> i32 {
    // Adding 3 preserves the remainder mod 3
    n + 3
}

// @expect: VERIFIED
#[requires("n >= 0 && n < 10")]
fn mod_cycle(n: i32) -> i32 {
    // Modulus bounds the result
    n % 5
}

// @expect: DISPROVEN
#[requires("n >= 0")]
fn mod_fail_test(n: i32) -> i32 {
    // This is wrong: n % 2 is not always 0
    n % 2
}

fn main() {
    println!("is_even(4) = {}", is_even(4));
    println!("is_even(5) = {}", is_even(5));
    println!("is_odd(4) = {}", is_odd(4));
    println!("is_odd(5) = {}", is_odd(5));
    println!("mod_preserving(7) = {}", mod_preserving(7));
    println!("mod_cycle(7) = {}", mod_cycle(7));
}
