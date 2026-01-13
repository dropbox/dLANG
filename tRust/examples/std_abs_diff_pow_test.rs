//! Integration test for abs_diff and pow builtin contracts (Phase 2.5.5)
//!
//! Tests that tRust provides correct contracts for:
//! - abs_diff: absolute difference between two integers
//! - pow: exponentiation
//!
//! Note: These contracts provide bounds/invariants, not exact computation.
//! Contracts like "result == 5" for specific values cannot be proven by
//! general contracts alone.
//!
//! Run: ./run_tests.sh (or directly with rustc -Zverify)
//!
//! @expect: VERIFIED

// =============================================================================
// abs_diff tests
// =============================================================================

/// Test that abs_diff returns 0 when both arguments are equal
#[requires("a == b")]
#[ensures("result == 0")]
pub fn abs_diff_equal(a: u32, b: u32) -> u32 {
    a.abs_diff(b)
}

/// Test that abs_diff of unsigned integers is bounded by max(a, b)
#[ensures("result <= a || result <= b")]
pub fn abs_diff_bounded_unsigned(a: u32, b: u32) -> u32 {
    a.abs_diff(b)
}

/// Test abs_diff always returns non-negative for unsigned
#[ensures("result >= 0")]
pub fn abs_diff_unsigned_nonneg(a: u32, b: u32) -> u32 {
    a.abs_diff(b)
}

/// Test signed abs_diff returns non-negative value
#[ensures("result >= 0")]
pub fn abs_diff_signed_nonneg(a: i32, b: i32) -> u32 {
    a.abs_diff(b)
}

/// Test signed abs_diff with equal values
#[requires("a == b")]
#[ensures("result == 0")]
pub fn abs_diff_signed_equal(a: i32, b: i32) -> u32 {
    a.abs_diff(b)
}

/// Test abs_diff with u64
#[requires("a == b")]
#[ensures("result == 0")]
pub fn abs_diff_u64_equal(a: u64, b: u64) -> u64 {
    a.abs_diff(b)
}

/// Test abs_diff with i64
#[ensures("result >= 0")]
pub fn abs_diff_i64_nonneg(a: i64, b: i64) -> u64 {
    a.abs_diff(b)
}

// =============================================================================
// pow tests
// =============================================================================

/// Test that x^0 == 1 for any x
#[ensures("result == 1")]
pub fn pow_zero_exp(x: u32) -> u32 {
    x.pow(0)
}

/// Test that x^1 == x
#[ensures("result == x")]
pub fn pow_one_exp(x: u32) -> u32 {
    x.pow(1)
}

/// Test that 0^n == 0 for n > 0
#[requires("n > 0")]
#[ensures("result == 0")]
pub fn pow_zero_base(n: u32) -> u32 {
    0u32.pow(n)
}

/// Test that 1^n == 1 for any n
#[ensures("result == 1")]
pub fn pow_one_base(n: u32) -> u32 {
    1u32.pow(n)
}

/// Test signed pow: x^0 == 1
#[ensures("result == 1")]
pub fn pow_signed_zero_exp(x: i32) -> i32 {
    x.pow(0)
}

/// Test signed pow: x^1 == x
#[ensures("result == x")]
pub fn pow_signed_one_exp(x: i32) -> i32 {
    x.pow(1)
}

/// Test signed pow: 1^n == 1
#[ensures("result == 1")]
pub fn pow_signed_one_base(n: u32) -> i32 {
    1i32.pow(n)
}

/// Test signed pow: 0^n == 0 for n > 0
#[requires("n > 0")]
#[ensures("result == 0")]
pub fn pow_signed_zero_base(n: u32) -> i32 {
    0i32.pow(n)
}

/// Test pow with u64
#[ensures("result == 1")]
pub fn pow_u64_zero_exp(x: u64) -> u64 {
    x.pow(0)
}

/// Test pow with i64
#[ensures("result == x")]
pub fn pow_i64_one_exp(x: i64) -> i64 {
    x.pow(1)
}

// =============================================================================
// Combined usage tests
// =============================================================================

/// Use abs_diff result in a postcondition
/// Note: This requires knowing that |a-b| <= max(a,b) for a,b <= 10
#[requires("a <= 10")]
#[requires("b <= 10")]
#[ensures("result <= 10")]
pub fn abs_diff_in_range(a: u32, b: u32) -> u32 {
    a.abs_diff(b)
}

/// Use pow: 2^0 = 1 which is >= 1
#[ensures("result >= 1")]
pub fn pow_positive() -> u32 {
    2u32.pow(0)
}

/// Chain: compute diff and verify it's non-negative (using just result >= 0)
#[ensures("result >= 0")]
pub fn diff_squared_concept(a: u32, b: u32) -> u32 {
    let diff = a.abs_diff(b);
    // pow of unsigned is >= 0
    diff.pow(2)
}

fn main() {
    // Test abs_diff contracts
    println!("abs_diff_equal(5, 5) = {}", abs_diff_equal(5, 5));
    println!("abs_diff_bounded_unsigned(10, 3) = {}", abs_diff_bounded_unsigned(10, 3));
    println!("abs_diff_unsigned_nonneg(7, 2) = {}", abs_diff_unsigned_nonneg(7, 2));
    println!("abs_diff_signed_nonneg(-5, 3) = {}", abs_diff_signed_nonneg(-5, 3));
    println!("abs_diff_signed_equal(-10, -10) = {}", abs_diff_signed_equal(-10, -10));
    println!("abs_diff_u64_equal(100, 100) = {}", abs_diff_u64_equal(100, 100));
    println!("abs_diff_i64_nonneg(-50, 50) = {}", abs_diff_i64_nonneg(-50, 50));

    // Test pow contracts
    println!("pow_zero_exp(5) = {}", pow_zero_exp(5));
    println!("pow_one_exp(7) = {}", pow_one_exp(7));
    println!("pow_zero_base(3) = {}", pow_zero_base(3));
    println!("pow_one_base(10) = {}", pow_one_base(10));
    println!("pow_signed_zero_exp(-5) = {}", pow_signed_zero_exp(-5));
    println!("pow_signed_one_exp(-3) = {}", pow_signed_one_exp(-3));
    println!("pow_signed_one_base(5) = {}", pow_signed_one_base(5));
    println!("pow_signed_zero_base(2) = {}", pow_signed_zero_base(2));
    println!("pow_u64_zero_exp(100) = {}", pow_u64_zero_exp(100));
    println!("pow_i64_one_exp(-50) = {}", pow_i64_one_exp(-50));

    // Test combined usage
    println!("abs_diff_in_range(3, 7) = {}", abs_diff_in_range(3, 7));
    println!("pow_positive() = {}", pow_positive());
    println!("diff_squared_concept(4, 2) = {}", diff_squared_concept(4, 2));

    println!("\nAll abs_diff and pow builtin contract tests passed!");
}
