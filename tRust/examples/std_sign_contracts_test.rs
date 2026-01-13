// Integration test for is_positive and is_negative builtin contracts (Phase 2.5.5)
//
// Tests that the verifier can use the builtin contracts for is_positive/is_negative
// to prove properties about boolean results.

#![allow(unused)]

// Test: Use is_positive to prove result is true when x > 0
#[requires("x > 0")]
#[ensures("result == true")]
fn test_is_positive_positive(x: i32) -> bool {
    x.is_positive()
}

// Test: Use is_negative to prove result is true when x < 0
#[requires("x < 0")]
#[ensures("result == true")]
fn test_is_negative_negative(x: i32) -> bool {
    x.is_negative()
}

// Test: Use is_positive to prove result is false when x <= 0
#[requires("x <= 0")]
#[ensures("result == false")]
fn test_is_positive_nonpositive(x: i32) -> bool {
    x.is_positive()
}

// Test: Use is_negative to prove result is false when x >= 0
#[requires("x >= 0")]
#[ensures("result == false")]
fn test_is_negative_nonnegative(x: i32) -> bool {
    x.is_negative()
}

// Test: Combining is_positive and is_negative gives complementary results
// For non-zero inputs, exactly one of is_positive/is_negative is true
#[requires("x != 0")]
#[ensures("result == true")]
fn test_positive_xor_negative(x: i32) -> bool {
    // One of them is true, but not both
    let pos = x.is_positive();
    let neg = x.is_negative();
    // XOR: one is true, the other is false
    (pos && !neg) || (!pos && neg)
}

// Test: Zero is neither positive nor negative
#[ensures("result == false")]
fn test_zero_not_positive() -> bool {
    0i32.is_positive()
}

#[ensures("result == false")]
fn test_zero_not_negative() -> bool {
    0i32.is_negative()
}

// Test: is_positive with i64
#[requires("x > 0")]
#[ensures("result == true")]
fn test_is_positive_i64(x: i64) -> bool {
    x.is_positive()
}

// Test: is_negative with i64
#[requires("x < 0")]
#[ensures("result == true")]
fn test_is_negative_i64(x: i64) -> bool {
    x.is_negative()
}

fn main() {
    // Test basic functionality
    assert!(test_is_positive_positive(5));
    assert!(test_is_negative_negative(-5));
    assert!(!test_is_positive_nonpositive(0));
    assert!(!test_is_positive_nonpositive(-3));
    assert!(!test_is_negative_nonnegative(0));
    assert!(!test_is_negative_nonnegative(3));
    assert!(test_positive_xor_negative(5));
    assert!(test_positive_xor_negative(-5));
    assert!(!test_zero_not_positive());
    assert!(!test_zero_not_negative());
    assert!(test_is_positive_i64(100));
    assert!(test_is_negative_i64(-100));

    println!("All is_positive/is_negative tests passed!");
}
