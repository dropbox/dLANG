//! Integration tests for char type contracts (Phase 10.1)
//!
//! Tests char methods:
//! - len_utf8(): 1 <= result <= 4
//! - len_utf16(): 1 <= result <= 2
//! - to_digit(radix): is_some ==> value < radix (documented)
//! - is_alphabetic(), is_digit(), is_whitespace(), etc. (documented)

#![allow(dead_code)]

// =========================================================================
// char::len_utf8 - UTF-8 byte length is in [1, 4]
// =========================================================================

/// Test 1: len_utf8 result is bounded [1, 4]
#[ensures("result >= 1 && result <= 4")]
fn test_len_utf8_bounds(c: char) -> usize {
    c.len_utf8()
}

/// Test 2: len_utf8 on ASCII character
#[ensures("result >= 1 && result <= 4")]
fn test_len_utf8_ascii() -> usize {
    'A'.len_utf8()
}

/// Test 3: len_utf8 on 2-byte character (Latin extended)
#[ensures("result >= 1 && result <= 4")]
fn test_len_utf8_latin_ext() -> usize {
    'é'.len_utf8() // Latin small letter e with acute: 2 bytes
}

/// Test 4: len_utf8 on 3-byte character (CJK)
#[ensures("result >= 1 && result <= 4")]
fn test_len_utf8_cjk() -> usize {
    '中'.len_utf8() // Chinese character: 3 bytes
}

/// Test 5: len_utf8 on 4-byte character (emoji)
#[ensures("result >= 1 && result <= 4")]
fn test_len_utf8_emoji() -> usize {
    '😀'.len_utf8() // Emoji: 4 bytes
}

// =========================================================================
// char::len_utf16 - UTF-16 code unit length is in [1, 2]
// =========================================================================

/// Test 6: len_utf16 result is bounded [1, 2]
#[ensures("result >= 1 && result <= 2")]
fn test_len_utf16_bounds(c: char) -> usize {
    c.len_utf16()
}

/// Test 7: len_utf16 on BMP character (1 code unit)
#[ensures("result >= 1 && result <= 2")]
fn test_len_utf16_bmp() -> usize {
    'A'.len_utf16() // BMP character: 1 code unit
}

/// Test 8: len_utf16 on supplementary character (2 code units)
#[ensures("result >= 1 && result <= 2")]
fn test_len_utf16_supplementary() -> usize {
    '😀'.len_utf16() // Supplementary character: 2 code units
}

// =========================================================================
// Boolean char methods (documented, no specific postconditions verified)
// =========================================================================

/// Test 9: is_alphabetic method exists
fn test_is_alphabetic() -> bool {
    'a'.is_alphabetic()
}

/// Test 10: is_alphanumeric method exists
fn test_is_alphanumeric() -> bool {
    'a'.is_alphanumeric()
}

/// Test 11: is_ascii method exists
fn test_is_ascii() -> bool {
    'A'.is_ascii()
}

/// Test 12: is_ascii_digit method exists
fn test_is_ascii_digit() -> bool {
    '5'.is_ascii_digit()
}

/// Test 13: is_whitespace method exists
fn test_is_whitespace() -> bool {
    ' '.is_whitespace()
}

// =========================================================================
// Main test function
// =========================================================================

fn main() {
    // len_utf8 tests
    let _ = test_len_utf8_bounds('a');
    let _ = test_len_utf8_ascii();
    let _ = test_len_utf8_latin_ext();
    let _ = test_len_utf8_cjk();
    let _ = test_len_utf8_emoji();

    // len_utf16 tests
    let _ = test_len_utf16_bounds('a');
    let _ = test_len_utf16_bmp();
    let _ = test_len_utf16_supplementary();

    // Boolean method tests
    let _ = test_is_alphabetic();
    let _ = test_is_alphanumeric();
    let _ = test_is_ascii();
    let _ = test_is_ascii_digit();
    let _ = test_is_whitespace();

    println!("All char tests passed!");
}
