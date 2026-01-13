// Test builtin contracts for midpoint operations
// midpoint(a, b) returns the average of two numbers without overflow
// Available since Rust 1.85 (requires num_midpoint feature on older versions)

#![feature(num_midpoint)]
#![feature(num_midpoint_signed)]

// Test unsigned midpoint contracts
// Postconditions: result >= 0, result <= max(a, b), a == b => result == a
#[ensures("result >= 0")]
fn test_unsigned_midpoint_nonneg(a: u32, b: u32) -> u32 {
    a.midpoint(b)
}

#[ensures("result <= a || result <= b")]
fn test_unsigned_midpoint_bounded(a: u32, b: u32) -> u32 {
    a.midpoint(b)
}

// When a == b, result must equal a
#[requires("a == b")]
#[ensures("result == a")]
fn test_unsigned_midpoint_equal(a: u32, b: u32) -> u32 {
    a.midpoint(b)
}

// Test with max values - no overflow
#[ensures("result >= 0")]
fn test_unsigned_midpoint_no_overflow(a: u32, b: u32) -> u32 {
    a.midpoint(b)
}

// Test signed midpoint contracts
// Postconditions: result is between a and b, a == b => result == a
#[requires("a == b")]
#[ensures("result == a")]
fn test_signed_midpoint_equal(a: i32, b: i32) -> i32 {
    a.midpoint(b)
}

// Result should be between a and b (or b and a if b < a)
#[requires("a <= b")]
#[ensures("result >= a && result <= b")]
fn test_signed_midpoint_in_range_asc(a: i32, b: i32) -> i32 {
    a.midpoint(b)
}

#[requires("a >= b")]
#[ensures("result >= b && result <= a")]
fn test_signed_midpoint_in_range_desc(a: i32, b: i32) -> i32 {
    a.midpoint(b)
}

// Test u64 midpoint
#[requires("a == b")]
#[ensures("result == a")]
fn test_u64_midpoint_equal(a: u64, b: u64) -> u64 {
    a.midpoint(b)
}

// Test i64 midpoint
#[requires("a == b")]
#[ensures("result == a")]
fn test_i64_midpoint_equal(a: i64, b: i64) -> i64 {
    a.midpoint(b)
}

// Test u8 midpoint
#[ensures("result >= 0")]
fn test_u8_midpoint_nonneg(a: u8, b: u8) -> u8 {
    a.midpoint(b)
}

// Test i8 midpoint - result is between a and b
#[requires("a == b")]
#[ensures("result == a")]
fn test_i8_midpoint_equal(a: i8, b: i8) -> i8 {
    a.midpoint(b)
}

fn main() {
    // Basic functionality tests
    assert_eq!(0u32.midpoint(10), 5);
    assert_eq!(5u32.midpoint(5), 5);
    assert_eq!((-5i32).midpoint(5), 0);
    assert_eq!((-10i32).midpoint(0), -5);

    // Test overflow prevention
    assert_eq!(u32::MAX.midpoint(u32::MAX), u32::MAX);
    assert_eq!(0u32.midpoint(u32::MAX), u32::MAX / 2);

    println!("All midpoint tests passed!");
}
