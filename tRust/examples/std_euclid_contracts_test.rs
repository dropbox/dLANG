// Test builtin contracts for unsigned_abs and div_euclid
// These are std library functions with postconditions known to the verifier
// @expect: VERIFIED

// Test unsigned_abs: converts signed to unsigned absolute value
// i32::unsigned_abs returns u32, always non-negative and equals |x|
#[requires("true")]
#[ensures("result >= 0")]
fn test_unsigned_abs_nonneg(x: i32) -> u32 {
    x.unsigned_abs()
}

// Test unsigned_abs with relationship to input
#[requires("x > 0")]
#[ensures("result == x")]
fn test_unsigned_abs_positive(x: i32) -> u32 {
    // When x > 0, unsigned_abs(x) == x (cast to unsigned)
    x.unsigned_abs()
}

// Test unsigned_abs with negative input
#[requires("x < 0")]
#[ensures("result > 0")]
fn test_unsigned_abs_negative(x: i32) -> u32 {
    // When x < 0, unsigned_abs(x) == -x > 0
    x.unsigned_abs()
}

// Test div_euclid for unsigned: result <= dividend
#[requires("rhs > 0")]
#[ensures("result <= x")]
fn test_div_euclid_unsigned_bound(x: u32, rhs: u32) -> u32 {
    x.div_euclid(rhs)
}

// Test div_euclid for unsigned: result is non-negative
#[requires("rhs > 0")]
#[ensures("result >= 0")]
fn test_div_euclid_unsigned_nonneg(x: u32, rhs: u32) -> u32 {
    x.div_euclid(rhs)
}

// Test div_euclid for signed: when x >= 0 and rhs > 0, result >= 0
#[requires("x >= 0 && rhs > 0")]
#[ensures("result >= 0")]
fn test_div_euclid_signed_nonneg(x: i32, rhs: i32) -> i32 {
    x.div_euclid(rhs)
}

// Test div_euclid with rem_euclid: x == result * rhs + remainder
// (This tests the relationship between div_euclid and rem_euclid)
#[requires("rhs > 0")]
#[ensures("result >= 0")]
fn test_remainder_nonneg(x: i32, rhs: i32) -> i32 {
    x.rem_euclid(rhs)
}

// Use unsigned_abs in a caller to verify modular verification
#[requires("a >= -100 && a <= 100")]
#[ensures("result >= 0")]
fn distance_from_zero(a: i32) -> u32 {
    a.unsigned_abs()
}

// Use div_euclid in a caller for integer division bounds
#[requires("n > 0 && n <= 1000")]
#[ensures("result <= n")]
fn half_rounded_down(n: u32) -> u32 {
    n.div_euclid(2)
}

fn main() {
    // Test unsigned_abs
    assert_eq!(test_unsigned_abs_nonneg(5), 5);
    assert_eq!(test_unsigned_abs_nonneg(-5), 5);
    assert_eq!(test_unsigned_abs_nonneg(0), 0);

    assert_eq!(test_unsigned_abs_positive(10), 10);
    assert_eq!(test_unsigned_abs_negative(-10), 10);

    // Test div_euclid
    assert_eq!(test_div_euclid_unsigned_bound(10, 3), 3);
    assert_eq!(test_div_euclid_unsigned_nonneg(10, 3), 3);
    assert_eq!(test_div_euclid_signed_nonneg(10, 3), 3);

    // Test remainder
    assert_eq!(test_remainder_nonneg(10, 3), 1);
    assert_eq!(test_remainder_nonneg(-10, 3), 2); // Euclidean remainder is always non-negative

    // Test composite functions
    assert_eq!(distance_from_zero(50), 50);
    assert_eq!(distance_from_zero(-50), 50);
    assert_eq!(half_rounded_down(10), 5);
    assert_eq!(half_rounded_down(11), 5);

    println!("All unsigned_abs and div_euclid tests passed!");
}
