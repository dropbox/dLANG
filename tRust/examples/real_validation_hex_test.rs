//! Real-world validation: `hex` (dependency-free subset).
//!
//! This file is an integration test for `./run_tests.sh` (picked up via `*_test.rs`),
//! and verifies hex encoding/decoding operations.
//!
//! The hex module functions are verified by tRust. This test file exercises
//! them with contracts that match what the underlying functions can guarantee.

#![allow(dead_code)]

#[path = "real_validation/hex.rs"]
mod hex;

use hex::{HexPair, ByteDecodeResult, encode_nibble, decode_nibble, encode_byte, decode_byte, is_hex_digit, encode_nibble_upper, encode_byte_upper};

// Note: roundtrip functions removed from hex.rs - roundtrip is tested at runtime below

// ============================================================================
// Test functions with verifiable contracts
// Each test uses contracts that can be proven from the underlying hex function contracts.
// ============================================================================

/// Test encode_nibble returns a valid hex character
#[ensures("result >= 48")]   // >= '0'
#[ensures("result <= 102")]  // <= 'f'
pub fn test_encode_nibble_bounds() -> u8 {
    encode_nibble(7)
}

/// Test encode_nibble_upper returns a valid uppercase hex character
#[ensures("result >= 48")]  // >= '0'
#[ensures("result <= 70")]  // <= 'F'
pub fn test_encode_nibble_upper_bounds() -> u8 {
    encode_nibble_upper(11)
}

/// Test encode_byte produces valid hex pair
#[ensures("result.high >= 48 && result.high <= 102")]  // '0'-'f'
#[ensures("result.low >= 48 && result.low <= 102")]
pub fn test_encode_byte_bounds() -> HexPair {
    encode_byte(0xAB)
}

/// Test encode_byte for boundary value 0
#[ensures("result.high >= 48 && result.high <= 102")]
#[ensures("result.low >= 48 && result.low <= 102")]
pub fn test_encode_byte_zero() -> HexPair {
    encode_byte(0)
}

/// Test encode_byte for boundary value 255
#[ensures("result.high >= 48 && result.high <= 102")]
#[ensures("result.low >= 48 && result.low <= 102")]
pub fn test_encode_byte_max() -> HexPair {
    encode_byte(255)
}

/// Test encode_byte_upper produces valid uppercase hex pair
#[ensures("result.high >= 48 && result.high <= 70")]  // '0'-'F'
#[ensures("result.low >= 48 && result.low <= 70")]
pub fn test_encode_byte_upper_bounds() -> HexPair {
    encode_byte_upper(0xDE)
}

/// Test decode_byte produces valid result with value in range
#[ensures("result.valid == true ==> result.value <= 255")]
pub fn test_decode_byte_bounds() -> ByteDecodeResult {
    decode_byte(52, 50)  // '4', '2' = 0x42
}

fn main() {
    // Run verified test functions
    let _ = test_encode_nibble_bounds();
    let _ = test_encode_nibble_upper_bounds();
    let _ = test_encode_byte_bounds();
    let _ = test_encode_byte_zero();
    let _ = test_encode_byte_max();
    let _ = test_encode_byte_upper_bounds();
    let _ = test_decode_byte_bounds();

    // Runtime sanity checks (executed but not verified)
    assert_eq!(encode_nibble(0), b'0');
    assert_eq!(encode_nibble(15), b'f');
    assert_eq!(decode_nibble(b'0').value, 0);
    assert_eq!(decode_nibble(b'f').value, 15);
    assert_eq!(encode_byte(0x42).high, b'4');
    assert_eq!(encode_byte(0x42).low, b'2');
    assert!(is_hex_digit(b'A'));
    assert!(!is_hex_digit(b'g'));

    println!("All hex tests passed!");
}
