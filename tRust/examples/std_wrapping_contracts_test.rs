//! Integration test for wrapping operation builtin contracts (Phase 2.5.5 Extension)
//!
//! Tests contracts for:
//! - wrapping_neg: negation with wrapping
//! - wrapping_add: addition with wrapping
//! - wrapping_sub: subtraction with wrapping
//! - wrapping_mul: multiplication with wrapping
//! - wrapping_shl: left shift with wrapping
//! - wrapping_shr: right shift with wrapping
//! - wrapping_pow: exponentiation with wrapping
//! - wrapping_div: division with wrapping (unsigned only)
//! - wrapping_rem: remainder with wrapping (unsigned only)
//!
//! Note: These tests verify partial contracts that hold even with wrapping semantics.
//! Full bitvector semantics would require SMT bitvector theory.

// ============================================================================
// wrapping_neg tests
// ============================================================================

// Test wrapping_neg zero-preservation for unsigned
// Contract: (x == 0) <=> (result == 0)
#[requires("x == 0")]
#[ensures("result == 0")]
fn test_wrapping_neg_u32_zero(x: u32) -> u32 {
    x.wrapping_neg()
}

// Test wrapping_neg non-zero for unsigned
// Contract: (x == 0) <=> (result == 0), so x != 0 => result != 0
#[requires("x > 0 && x < 1000")]
#[ensures("result != 0")]
fn test_wrapping_neg_u32_nonzero(x: u32) -> u32 {
    x.wrapping_neg()
}

// Test wrapping_neg zero-preservation for signed
#[requires("x == 0")]
#[ensures("result == 0")]
fn test_wrapping_neg_i32_zero(x: i32) -> i32 {
    x.wrapping_neg()
}

// Test wrapping_neg non-zero for signed
#[requires("x != 0 && x > -1000 && x < 1000")]
#[ensures("result != 0")]
fn test_wrapping_neg_i32_nonzero(x: i32) -> i32 {
    x.wrapping_neg()
}

// ============================================================================
// wrapping_add tests
// ============================================================================

// Test wrapping_add zero-preservation
// Contract: (a == 0 && b == 0) => result == 0
#[requires("a == 0")]
#[requires("b == 0")]
#[ensures("result == 0")]
fn test_wrapping_add_zeros_u32(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

// Test wrapping_add zero-preservation for signed
#[requires("a == 0")]
#[requires("b == 0")]
#[ensures("result == 0")]
fn test_wrapping_add_zeros_i32(a: i32, b: i32) -> i32 {
    a.wrapping_add(b)
}

// ============================================================================
// wrapping_sub tests
// ============================================================================

// Test wrapping_sub equal subtraction
// Contract: (a == b) => result == 0
#[requires("a == b")]
#[requires("a >= 0 && a < 1000")]
#[ensures("result == 0")]
fn test_wrapping_sub_equal_u32(a: u32, b: u32) -> u32 {
    a.wrapping_sub(b)
}

// Test wrapping_sub equal subtraction for signed
#[requires("a == b")]
#[requires("a > -500 && a < 500")]
#[ensures("result == 0")]
fn test_wrapping_sub_equal_i32(a: i32, b: i32) -> i32 {
    a.wrapping_sub(b)
}

// ============================================================================
// wrapping_mul tests
// ============================================================================

// Test wrapping_mul zero-absorption
// Contract: (a == 0 || b == 0) => result == 0
#[requires("a == 0")]
#[requires("b >= 0 && b < 1000")]
#[ensures("result == 0")]
fn test_wrapping_mul_zero_left(a: u32, b: u32) -> u32 {
    a.wrapping_mul(b)
}

// Test wrapping_mul zero-absorption from right
#[requires("a >= 0 && a < 1000")]
#[requires("b == 0")]
#[ensures("result == 0")]
fn test_wrapping_mul_zero_right(a: u32, b: u32) -> u32 {
    a.wrapping_mul(b)
}

// Test wrapping_mul zero-absorption for signed
#[requires("a == 0")]
#[requires("b > -500 && b < 500")]
#[ensures("result == 0")]
fn test_wrapping_mul_zero_signed(a: i32, b: i32) -> i32 {
    a.wrapping_mul(b)
}

// ============================================================================
// wrapping_shl tests
// ============================================================================

// Test wrapping_shl zero-preservation
// Contract: (x == 0) => result == 0
#[requires("x == 0")]
#[requires("n >= 0 && n < 32")]
#[ensures("result == 0")]
fn test_wrapping_shl_zero(x: u32, n: u32) -> u32 {
    x.wrapping_shl(n)
}

// Test wrapping_shl zero-preservation for signed
#[requires("x == 0")]
#[requires("n >= 0 && n < 32")]
#[ensures("result == 0")]
fn test_wrapping_shl_zero_signed(x: i32, n: u32) -> i32 {
    x.wrapping_shl(n)
}

// ============================================================================
// wrapping_shr tests
// ============================================================================

// Test wrapping_shr zero-preservation
// Contract: (x == 0) => result == 0
#[requires("x == 0")]
#[requires("n >= 0 && n < 32")]
#[ensures("result == 0")]
fn test_wrapping_shr_zero(x: u32, n: u32) -> u32 {
    x.wrapping_shr(n)
}

// Test wrapping_shr zero-preservation for signed
#[requires("x == 0")]
#[requires("n >= 0 && n < 32")]
#[ensures("result == 0")]
fn test_wrapping_shr_zero_signed(x: i32, n: u32) -> i32 {
    x.wrapping_shr(n)
}

// ============================================================================
// wrapping_pow tests
// ============================================================================

// Test wrapping_pow: base == 1 => result == 1
#[requires("base == 1")]
#[requires("exp >= 0 && exp < 100")]
#[ensures("result == 1")]
fn test_wrapping_pow_base_one(base: u32, exp: u32) -> u32 {
    base.wrapping_pow(exp)
}

// Test wrapping_pow: exp == 0 => result == 1
#[requires("base >= 0 && base < 100")]
#[requires("exp == 0")]
#[ensures("result == 1")]
fn test_wrapping_pow_exp_zero(base: u32, exp: u32) -> u32 {
    base.wrapping_pow(exp)
}

// Test wrapping_pow: base == 0 && exp > 0 => result == 0
#[requires("base == 0")]
#[requires("exp > 0 && exp < 100")]
#[ensures("result == 0")]
fn test_wrapping_pow_zero_base(base: u32, exp: u32) -> u32 {
    base.wrapping_pow(exp)
}

// Test wrapping_pow for signed: base == 1 => result == 1
#[requires("base == 1")]
#[requires("exp >= 0 && exp < 100")]
#[ensures("result == 1")]
fn test_wrapping_pow_signed_base_one(base: i32, exp: u32) -> i32 {
    base.wrapping_pow(exp)
}

// ============================================================================
// wrapping_div tests (unsigned only)
// ============================================================================

// Test wrapping_div bounded result for unsigned
// Contract: result >= 0 and result <= x
#[requires("x >= 0 && x < 1000")]
#[requires("y > 0 && y < 100")]
#[ensures("result >= 0")]
#[ensures("result <= x")]
fn test_wrapping_div_bounded(x: u32, y: u32) -> u32 {
    x.wrapping_div(y)
}

// Test wrapping_div zero divided
#[requires("x == 0")]
#[requires("y > 0 && y < 100")]
#[ensures("result == 0")]
fn test_wrapping_div_zero(x: u32, y: u32) -> u32 {
    x.wrapping_div(y)
}

// ============================================================================
// wrapping_rem tests (unsigned only)
// ============================================================================

// Test wrapping_rem bounded result for unsigned
// Contract: 0 <= result < y (for y > 0)
#[requires("x >= 0 && x < 1000")]
#[requires("y > 0 && y < 100")]
#[ensures("result >= 0")]
#[ensures("result < y")]
fn test_wrapping_rem_bounded(x: u32, y: u32) -> u32 {
    x.wrapping_rem(y)
}

// Test wrapping_rem zero divided
#[requires("x == 0")]
#[requires("y > 0 && y < 100")]
#[ensures("result == 0")]
fn test_wrapping_rem_zero(x: u32, y: u32) -> u32 {
    x.wrapping_rem(y)
}

fn main() {
    // wrapping_neg tests
    println!("wrapping_neg(0u32) = {}", test_wrapping_neg_u32_zero(0));
    println!("wrapping_neg(5u32) = {}", test_wrapping_neg_u32_nonzero(5));
    println!("wrapping_neg(0i32) = {}", test_wrapping_neg_i32_zero(0));
    println!("wrapping_neg(5i32) = {}", test_wrapping_neg_i32_nonzero(5));

    // wrapping_add tests
    println!("wrapping_add(0u32, 0u32) = {}", test_wrapping_add_zeros_u32(0, 0));
    println!("wrapping_add(0i32, 0i32) = {}", test_wrapping_add_zeros_i32(0, 0));

    // wrapping_sub tests
    println!("wrapping_sub(10u32, 10u32) = {}", test_wrapping_sub_equal_u32(10, 10));
    println!("wrapping_sub(42i32, 42i32) = {}", test_wrapping_sub_equal_i32(42, 42));

    // wrapping_mul tests
    println!("wrapping_mul(0u32, 100u32) = {}", test_wrapping_mul_zero_left(0, 100));
    println!("wrapping_mul(100u32, 0u32) = {}", test_wrapping_mul_zero_right(100, 0));
    println!("wrapping_mul(0i32, 50i32) = {}", test_wrapping_mul_zero_signed(0, 50));

    // wrapping_shl tests
    println!("wrapping_shl(0u32, 5) = {}", test_wrapping_shl_zero(0, 5));
    println!("wrapping_shl(0i32, 5) = {}", test_wrapping_shl_zero_signed(0, 5));

    // wrapping_shr tests
    println!("wrapping_shr(0u32, 5) = {}", test_wrapping_shr_zero(0, 5));
    println!("wrapping_shr(0i32, 5) = {}", test_wrapping_shr_zero_signed(0, 5));

    // wrapping_pow tests
    println!("wrapping_pow(1u32, 10) = {}", test_wrapping_pow_base_one(1, 10));
    println!("wrapping_pow(5u32, 0) = {}", test_wrapping_pow_exp_zero(5, 0));
    println!("wrapping_pow(0u32, 5) = {}", test_wrapping_pow_zero_base(0, 5));
    println!("wrapping_pow(1i32, 10) = {}", test_wrapping_pow_signed_base_one(1, 10));

    // wrapping_div tests
    println!("wrapping_div(100u32, 7u32) = {}", test_wrapping_div_bounded(100, 7));
    println!("wrapping_div(0u32, 7u32) = {}", test_wrapping_div_zero(0, 7));

    // wrapping_rem tests
    println!("wrapping_rem(100u32, 7u32) = {}", test_wrapping_rem_bounded(100, 7));
    println!("wrapping_rem(0u32, 7u32) = {}", test_wrapping_rem_zero(0, 7));

    println!("All wrapping operation contract tests completed!");
}
