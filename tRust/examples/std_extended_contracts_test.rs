//! Integration test for extended std library builtin contracts (Phase 2.5.5 Extension)
//!
//! Tests contracts for:
//! - saturating_mul: for unsigned types
//! - next_power_of_two: for unsigned types
//! - ilog2, ilog10, ilog: integer logarithms
//! - rotate_left, rotate_right: bit rotation
//! - swap_bytes, reverse_bits: bit/byte manipulation
//! - from_be, from_le, to_be, to_le: endianness conversions
//!
//! Note: These tests verify the contract semantics, not exact computation.
//! The contracts provide bounds and invariants, not exact mathematical results.

// Test saturating_mul contract for unsigned types
// Contract: result >= 0, and if a > 0 && b > 0 then result >= max(a, b)
#[requires("a >= 0 && a < 100")]
#[requires("b >= 0 && b < 100")]
#[ensures("result >= 0")]
fn test_saturating_mul_u32(a: u32, b: u32) -> u32 {
    let r = a.saturating_mul(b);
    r
}

// Test saturating_mul grows result
#[requires("a > 0 && a <= 10")]
#[requires("b > 0 && b <= 10")]
#[ensures("result >= a")]
#[ensures("result >= b")]
fn test_saturating_mul_grows(a: u32, b: u32) -> u32 {
    a.saturating_mul(b)
}

// Test next_power_of_two contract
// Contract: result > 0 and (result >= x or x == 0)
#[requires("x > 0 && x <= 64")]
#[ensures("result >= x")]
#[ensures("result > 0")]
fn test_next_power_of_two(x: u32) -> u32 {
    x.next_power_of_two()
}

// Test next_power_of_two returns positive for zero
// Contract guarantees result > 0 even for input 0
#[ensures("result > 0")]
fn test_next_power_of_two_zero() -> u32 {
    0u32.next_power_of_two()
}

// Test ilog2 contract
// Contract: result >= 0 and result < bit_width, and x == 1 => result == 0
#[requires("x > 0")]
#[ensures("result >= 0")]
#[ensures("result < 32")]  // bit_width for u32
fn test_ilog2_basic(x: u32) -> u32 {
    x.ilog2()
}

// Test ilog2 boundary case - x == 1 => result == 0
#[ensures("result == 0")]
fn test_ilog2_one() -> u32 {
    1u32.ilog2()
}

// Test ilog10 contract
// Contract: result >= 0 and result <= max_log10, and x == 1 => result == 0
#[requires("x > 0")]
#[ensures("result >= 0")]
#[ensures("result <= 9")]  // max log10 for u32 is 9 (4_294_967_295 -> 9)
fn test_ilog10_basic(x: u32) -> u32 {
    x.ilog10()
}

// Test ilog10 boundary case - x == 1 => result == 0
#[ensures("result == 0")]
fn test_ilog10_one() -> u32 {
    1u32.ilog10()
}

// Test rotate_left contract
// Contract: x == 0 <=> result == 0 (rotation preserves zero-ness)
#[requires("x > 0")]
#[ensures("result != 0")]
fn test_rotate_left_nonzero(x: u32) -> u32 {
    x.rotate_left(5)
}

#[ensures("result == 0")]
fn test_rotate_left_zero() -> u32 {
    0u32.rotate_left(5)
}

// Test rotate_right contract
// Contract: x == 0 <=> result == 0
#[requires("x > 0")]
#[ensures("result != 0")]
fn test_rotate_right_nonzero(x: u32) -> u32 {
    x.rotate_right(7)
}

#[ensures("result == 0")]
fn test_rotate_right_zero() -> u32 {
    0u32.rotate_right(7)
}

// Test swap_bytes contract
// Contract: x == 0 <=> result == 0
#[requires("x > 0")]
#[ensures("result != 0")]
fn test_swap_bytes_nonzero(x: u32) -> u32 {
    x.swap_bytes()
}

#[ensures("result == 0")]
fn test_swap_bytes_zero() -> u32 {
    0u32.swap_bytes()
}

// Test reverse_bits contract
// Contract: x == 0 <=> result == 0
#[requires("x > 0")]
#[ensures("result != 0")]
fn test_reverse_bits_nonzero(x: u32) -> u32 {
    x.reverse_bits()
}

#[ensures("result == 0")]
fn test_reverse_bits_zero() -> u32 {
    0u32.reverse_bits()
}

// Test to_be/to_le contracts
// Contract: x == 0 <=> result == 0
#[requires("x > 0")]
#[ensures("result != 0")]
fn test_to_be_nonzero(x: u32) -> u32 {
    x.to_be()
}

#[ensures("result == 0")]
fn test_to_be_zero() -> u32 {
    0u32.to_be()
}

#[requires("x > 0")]
#[ensures("result != 0")]
fn test_to_le_nonzero(x: u32) -> u32 {
    x.to_le()
}

// Test from_be/from_le contracts
#[requires("x > 0")]
#[ensures("result != 0")]
fn test_from_be_nonzero(x: u32) -> u32 {
    u32::from_be(x)
}

#[requires("x > 0")]
#[ensures("result != 0")]
fn test_from_le_nonzero(x: u32) -> u32 {
    u32::from_le(x)
}

// Test ilog with explicit base
#[requires("x > 0")]
#[ensures("result >= 0")]
fn test_ilog_base_2(x: u32) -> u32 {
    x.ilog(2)
}

// Test ilog boundary case - x == 1 => result == 0
#[ensures("result == 0")]
fn test_ilog_one() -> u32 {
    // log_b(1) = 0 for any base b > 1
    1u32.ilog(10)
}

// Composition test: combine multiple contracts
#[requires("x > 0 && x <= 100")]
#[ensures("result >= 0")]
fn test_composition_log_and_rotation(x: u32) -> u32 {
    let log_result = x.ilog2();
    // Rotate by the log value
    let rotated = x.rotate_left(log_result);
    // rotated should still be non-zero since x > 0
    rotated.count_ones()
}

// Test different integer sizes for ilog2
#[requires("x > 0")]
#[ensures("result >= 0")]
#[ensures("result < 64")]  // bit_width for u64
fn test_ilog2_u64(x: u64) -> u32 {
    x.ilog2()
}

#[requires("x > 0")]
#[ensures("result >= 0")]
#[ensures("result < 16")]  // bit_width for u16
fn test_ilog2_u16(x: u16) -> u32 {
    x.ilog2()
}

// Test saturating_mul with u64
#[requires("a > 0 && a <= 1000")]
#[requires("b > 0 && b <= 1000")]
#[ensures("result >= a")]
#[ensures("result >= b")]
fn test_saturating_mul_u64(a: u64, b: u64) -> u64 {
    a.saturating_mul(b)
}

fn main() {
    // Run some basic sanity checks
    println!("Testing saturating_mul...");
    assert_eq!(test_saturating_mul_u32(5, 10), 50);
    assert_eq!(test_saturating_mul_grows(3, 4), 12);

    println!("Testing next_power_of_two...");
    assert_eq!(test_next_power_of_two(5), 8);
    assert_eq!(test_next_power_of_two(8), 8);
    assert_eq!(test_next_power_of_two_zero(), 1);

    println!("Testing ilog2...");
    assert_eq!(test_ilog2_one(), 0);
    assert_eq!(test_ilog2_basic(2), 1);
    assert_eq!(test_ilog2_basic(8), 3);

    println!("Testing ilog10...");
    assert_eq!(test_ilog10_one(), 0);
    assert_eq!(test_ilog10_basic(100), 2);

    println!("Testing rotate operations...");
    assert_ne!(test_rotate_left_nonzero(1), 0);
    assert_eq!(test_rotate_left_zero(), 0);
    assert_ne!(test_rotate_right_nonzero(1), 0);
    assert_eq!(test_rotate_right_zero(), 0);

    println!("Testing byte/bit manipulation...");
    assert_ne!(test_swap_bytes_nonzero(1), 0);
    assert_eq!(test_swap_bytes_zero(), 0);
    assert_ne!(test_reverse_bits_nonzero(1), 0);
    assert_eq!(test_reverse_bits_zero(), 0);

    println!("Testing endianness conversions...");
    assert_ne!(test_to_be_nonzero(1), 0);
    assert_eq!(test_to_be_zero(), 0);

    println!("Testing ilog...");
    assert_eq!(test_ilog_one(), 0);

    println!("All runtime tests passed!");
}
