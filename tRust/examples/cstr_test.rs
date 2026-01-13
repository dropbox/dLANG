//! CStr/CString integration test (Phase 10.1)
//! Tests CStr and CString contracts for C-compatible null-terminated strings.
//!
//! CStr is a borrowed null-terminated string slice, CString is the owned version.
//! These types are documented contracts without strong postconditions since:
//! - count_bytes returns usize which is intrinsically non-negative
//! - CString::new() returns Result (success depends on input content)
//! - Most operations are runtime-dependent
//!
//! This test verifies the methods are recognized and callable.

use std::ffi::{CStr, CString};

// Test 1: CStr::count_bytes returns usize
fn test_cstr_count_bytes(s: &CStr) -> usize {
    s.count_bytes()
}

// Test 2: CStr::is_empty returns boolean
fn test_cstr_is_empty(s: &CStr) -> bool {
    s.is_empty()
}

// Test 3: CStr::to_bytes returns slice without null terminator
fn test_cstr_to_bytes(s: &CStr) -> &[u8] {
    s.to_bytes()
}

// Test 4: CStr::to_bytes_with_nul returns slice with null terminator
fn test_cstr_to_bytes_with_nul(s: &CStr) -> &[u8] {
    s.to_bytes_with_nul()
}

// Test 5: CStr::to_str returns Result (UTF-8 validity dependent)
fn test_cstr_to_str<'a>(s: &'a CStr) -> Result<&'a str, std::str::Utf8Error> {
    s.to_str()
}

// Test 6: CString::new returns Result (can fail with interior nulls)
fn test_cstring_new(bytes: Vec<u8>) -> Result<CString, std::ffi::NulError> {
    CString::new(bytes)
}

// Test 7: CString::into_bytes consumes and returns bytes
fn test_cstring_into_bytes(s: CString) -> Vec<u8> {
    s.into_bytes()
}

// Test 8: CString::into_bytes_with_nul includes null terminator
fn test_cstring_into_bytes_with_nul(s: CString) -> Vec<u8> {
    s.into_bytes_with_nul()
}

// Test 9: CString::as_bytes returns bytes reference
fn test_cstring_as_bytes(s: &CString) -> &[u8] {
    s.as_bytes()
}

// Test 10: CString::as_bytes_with_nul returns bytes with null reference
fn test_cstring_as_bytes_with_nul(s: &CString) -> &[u8] {
    s.as_bytes_with_nul()
}

// Test 11: CString::as_c_str returns CStr reference
fn test_cstring_as_c_str(s: &CString) -> &CStr {
    s.as_c_str()
}

// Test 12: CString from literal
fn test_cstring_from_literal() -> CString {
    CString::new("hello").unwrap()
}

fn main() {
    // Create CString from valid bytes
    let cstring = test_cstring_from_literal();
    println!("CString from literal: {:?}", cstring);

    // Test CStr operations via CString::as_c_str
    let cstr = test_cstring_as_c_str(&cstring);
    println!("CStr count_bytes: {}", test_cstr_count_bytes(cstr));
    println!("CStr is_empty: {}", test_cstr_is_empty(cstr));

    // Test byte access
    let bytes = test_cstr_to_bytes(cstr);
    println!("CStr to_bytes: {:?}", bytes);

    let bytes_with_nul = test_cstr_to_bytes_with_nul(cstr);
    println!("CStr to_bytes_with_nul: {:?}", bytes_with_nul);

    // Test UTF-8 conversion
    match test_cstr_to_str(cstr) {
        Ok(s) => println!("CStr to_str: {}", s),
        Err(e) => println!("CStr to_str error: {}", e),
    }

    // Test CString creation success
    let valid_bytes = vec![b'h', b'e', b'l', b'l', b'o'];
    match test_cstring_new(valid_bytes) {
        Ok(s) => println!("CString::new success: {:?}", s),
        Err(e) => println!("CString::new error: {}", e),
    }

    // Test CString creation failure (interior null)
    let invalid_bytes = vec![b'h', b'e', 0, b'l', b'o'];
    match test_cstring_new(invalid_bytes) {
        Ok(s) => println!("Unexpected success: {:?}", s),
        Err(e) => println!("Expected error (interior null): {}", e),
    }

    // Test CString byte access
    let cstring2 = CString::new("world").unwrap();
    println!("as_bytes: {:?}", test_cstring_as_bytes(&cstring2));
    println!("as_bytes_with_nul: {:?}", test_cstring_as_bytes_with_nul(&cstring2));

    // Test consuming methods
    let cstring3 = CString::new("consume").unwrap();
    let bytes_consumed = test_cstring_into_bytes(cstring3);
    println!("into_bytes: {:?}", bytes_consumed);

    let cstring4 = CString::new("consume_nul").unwrap();
    let bytes_with_nul_consumed = test_cstring_into_bytes_with_nul(cstring4);
    println!("into_bytes_with_nul: {:?}", bytes_with_nul_consumed);

    println!("All CStr/CString tests completed!");
}
