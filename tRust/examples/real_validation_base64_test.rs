//! Real-world validation: `base64` (dependency-free subset).
//!
//! This file is an integration test for `./run_tests.sh` (picked up via `*_test.rs`),
//! and verifies base64 encoding/decoding operations.
//!
//! The base64 module functions are verified by tRust. This test file exercises
//! them with contracts that match what the underlying functions can guarantee.

#![allow(dead_code)]

#[path = "real_validation/base64.rs"]
mod base64;

use base64::{
    DecodeResult, EncodeGroupResult, DecodeGroupResult,
    encode_char, decode_char, is_base64_char, is_padding_char,
    encode_group, decode_group, encode_one_byte, encode_two_bytes
};

// ============================================================================
// Test functions with verifiable contracts
// Each test uses contracts that can be proven from the underlying base64 function contracts.
// ============================================================================

/// Test encode_char returns a valid base64 character
#[ensures("result >= 43")]   // min is '+' (43)
#[ensures("result <= 122")]  // max is 'z' (122)
pub fn test_encode_char_bounds() -> u8 {
    encode_char(0)  // Should return 'A' (65)
}

/// Test encode_char for value 25 (last uppercase letter)
#[ensures("result >= 43 && result <= 122")]
pub fn test_encode_char_z() -> u8 {
    encode_char(25)  // Should return 'Z' (90)
}

/// Test encode_char for value 26 (first lowercase letter)
#[ensures("result >= 43 && result <= 122")]
pub fn test_encode_char_a() -> u8 {
    encode_char(26)  // Should return 'a' (97)
}

/// Test encode_char for value 52 (digit '0')
#[ensures("result >= 43 && result <= 122")]
pub fn test_encode_char_digit() -> u8 {
    encode_char(52)  // Should return '0' (48)
}

/// Test encode_char for value 62 ('+')
#[ensures("result >= 43 && result <= 122")]
pub fn test_encode_char_plus() -> u8 {
    encode_char(62)  // Should return '+' (43)
}

/// Test encode_char for value 63 ('/')
#[ensures("result >= 43 && result <= 122")]
pub fn test_encode_char_slash() -> u8 {
    encode_char(63)  // Should return '/' (47)
}

/// Test decode_char returns valid result with value in range
#[ensures("result.valid == true ==> result.value < 64")]
pub fn test_decode_char_bounds() -> DecodeResult {
    decode_char(65)  // 'A' -> 0
}

/// Test encode_group produces 4 valid base64 characters
#[ensures("result.c0 >= 43 && result.c0 <= 122")]
#[ensures("result.c1 >= 43 && result.c1 <= 122")]
#[ensures("result.c2 >= 43 && result.c2 <= 122")]
#[ensures("result.c3 >= 43 && result.c3 <= 122")]
pub fn test_encode_group_bounds() -> EncodeGroupResult {
    // Encoding "ABC" (0x41, 0x42, 0x43) -> "QUJD"
    encode_group(0x41, 0x42, 0x43)
}

/// Test encode_one_byte produces 2 valid chars + 2 padding
#[ensures("result.c0 >= 43 && result.c0 <= 122")]
#[ensures("result.c1 >= 43 && result.c1 <= 122")]
#[ensures("result.c2 == 61")]  // '='
#[ensures("result.c3 == 61")]  // '='
pub fn test_encode_one_byte_padding() -> EncodeGroupResult {
    encode_one_byte(0x41)  // 'A' -> "QQ=="
}

/// Test encode_two_bytes produces 3 valid chars + 1 padding
#[ensures("result.c0 >= 43 && result.c0 <= 122")]
#[ensures("result.c1 >= 43 && result.c1 <= 122")]
#[ensures("result.c2 >= 43 && result.c2 <= 122")]
#[ensures("result.c3 == 61")]  // '='
pub fn test_encode_two_bytes_padding() -> EncodeGroupResult {
    encode_two_bytes(0x41, 0x42)  // "AB" -> "QUI="
}

/// Test decode_group produces valid result
#[ensures("result.valid == true ==> result.b0 <= 255")]
#[ensures("result.valid == true ==> result.b1 <= 255")]
#[ensures("result.valid == true ==> result.b2 <= 255")]
pub fn test_decode_group_bounds() -> DecodeGroupResult {
    // Decoding "QUJD" -> "ABC" (0x41, 0x42, 0x43)
    decode_group(81, 85, 74, 68)  // 'Q', 'U', 'J', 'D'
}

fn main() {
    // Run verified test functions
    let _ = test_encode_char_bounds();
    let _ = test_encode_char_z();
    let _ = test_encode_char_a();
    let _ = test_encode_char_digit();
    let _ = test_encode_char_plus();
    let _ = test_encode_char_slash();
    let _ = test_decode_char_bounds();
    let _ = test_encode_group_bounds();
    let _ = test_encode_one_byte_padding();
    let _ = test_encode_two_bytes_padding();
    let _ = test_decode_group_bounds();

    // Runtime sanity checks (executed but not verified)
    // Verify encode_char mapping
    assert_eq!(encode_char(0), 65);   // 'A'
    assert_eq!(encode_char(25), 90);  // 'Z'
    assert_eq!(encode_char(26), 97);  // 'a'
    assert_eq!(encode_char(51), 122); // 'z'
    assert_eq!(encode_char(52), 48);  // '0'
    assert_eq!(encode_char(61), 57);  // '9'
    assert_eq!(encode_char(62), 43);  // '+'
    assert_eq!(encode_char(63), 47);  // '/'

    // Verify decode_char mapping
    assert_eq!(decode_char(65).value, 0);   // 'A' -> 0
    assert_eq!(decode_char(90).value, 25);  // 'Z' -> 25
    assert_eq!(decode_char(97).value, 26);  // 'a' -> 26
    assert_eq!(decode_char(122).value, 51); // 'z' -> 51
    assert_eq!(decode_char(48).value, 52);  // '0' -> 52
    assert_eq!(decode_char(57).value, 61);  // '9' -> 61
    assert_eq!(decode_char(43).value, 62);  // '+' -> 62
    assert_eq!(decode_char(47).value, 63);  // '/' -> 63

    // Verify is_base64_char
    assert!(is_base64_char(65));   // 'A'
    assert!(is_base64_char(122));  // 'z'
    assert!(is_base64_char(48));   // '0'
    assert!(is_base64_char(43));   // '+'
    assert!(is_base64_char(47));   // '/'
    assert!(!is_base64_char(64));  // '@' is not base64

    // Verify is_padding_char
    assert!(is_padding_char(61));   // '='
    assert!(!is_padding_char(65));  // 'A'

    // Verify encode/decode roundtrip for "ABC"
    let encoded = encode_group(0x41, 0x42, 0x43);
    let decoded = decode_group(encoded.c0, encoded.c1, encoded.c2, encoded.c3);
    assert!(decoded.valid);
    assert_eq!(decoded.b0, 0x41);
    assert_eq!(decoded.b1, 0x42);
    assert_eq!(decoded.b2, 0x43);

    // Verify known base64 encoding: "Man" -> "TWFu"
    let man_encoded = encode_group(77, 97, 110);  // 'M', 'a', 'n'
    assert_eq!(man_encoded.c0, 84);  // 'T'
    assert_eq!(man_encoded.c1, 87);  // 'W'
    assert_eq!(man_encoded.c2, 70);  // 'F'
    assert_eq!(man_encoded.c3, 117); // 'u'

    println!("All base64 tests passed!");
}
