//! OsStr/OsString integration test (Phase 10.1)
//! Tests OsStr and OsString contracts for FFI string handling.
//!
//! OsStr is a borrowed platform-native string slice, OsString is the owned version.
//! These types are documented contracts without strong postconditions since:
//! - They are platform-native encoding types
//! - Length operations return usize which is intrinsically non-negative
//! - Conversion operations depend on UTF-8 validity (runtime-dependent)
//!
//! This test verifies the methods are recognized and callable.

use std::ffi::{OsStr, OsString};

// Test 1: OsStr::len returns usize
fn test_osstr_len(s: &OsStr) -> usize {
    s.len()
}

// Test 2: OsStr::is_empty returns boolean
fn test_osstr_is_empty(s: &OsStr) -> bool {
    s.is_empty()
}

// Test 3: OsStr::to_str returns Option (UTF-8 validity dependent)
fn test_osstr_to_str<'a>(s: &'a OsStr) -> Option<&'a str> {
    s.to_str()
}

// Test 4: OsStr::to_os_string creates owned copy
fn test_osstr_to_os_string(s: &OsStr) -> OsString {
    s.to_os_string()
}

// Test 5: OsString::new creates empty string
fn test_osstring_new() -> OsString {
    OsString::new()
}

// Test 6: OsString::with_capacity creates string with reserved capacity
fn test_osstring_with_capacity(capacity: usize) -> OsString {
    OsString::with_capacity(capacity)
}

// Test 7: OsString::capacity returns usize
fn test_osstring_capacity(s: &OsString) -> usize {
    s.capacity()
}

// Test 8: OsString::len returns usize
fn test_osstring_len(s: &OsString) -> usize {
    s.len()
}

// Test 9: OsString::is_empty returns boolean
fn test_osstring_is_empty(s: &OsString) -> bool {
    s.is_empty()
}

// Test 10: OsString::push mutation (documented, no postcondition)
fn test_osstring_push(s: &mut OsString, other: &OsStr) {
    s.push(other);
}

// Test 11: OsString::clear mutation (documented, no postcondition)
fn test_osstring_clear(s: &mut OsString) {
    s.clear();
}

// Test 12: OsString::as_os_str returns reference
fn test_osstring_as_os_str(s: &OsString) -> &OsStr {
    s.as_os_str()
}

// Test 13: OsString from Path integration
fn test_osstring_from_path() -> OsString {
    use std::path::Path;
    let path = Path::new("/usr/bin/test");
    path.as_os_str().to_os_string()
}

fn main() {
    // Test OsString creation
    let empty = test_osstring_new();
    println!("Empty OsString len: {}", test_osstring_len(&empty));
    println!("Empty OsString is_empty: {}", test_osstring_is_empty(&empty));

    let preallocated = test_osstring_with_capacity(100);
    println!("Preallocated capacity: {}", test_osstring_capacity(&preallocated));
    println!("Preallocated len: {}", test_osstring_len(&preallocated));

    // Test OsStr operations
    let osstr = OsStr::new("hello");
    println!("OsStr 'hello' len: {}", test_osstr_len(osstr));
    println!("OsStr 'hello' is_empty: {}", test_osstr_is_empty(osstr));

    // Test UTF-8 conversion (should succeed for valid UTF-8)
    if let Some(s) = test_osstr_to_str(osstr) {
        println!("OsStr to_str: {}", s);
    }

    // Test owned conversion
    let owned = test_osstr_to_os_string(osstr);
    println!("Owned OsString len: {}", test_osstring_len(&owned));

    // Test mutation
    let mut mutable = OsString::from("hello");
    println!("Before push: {:?}", mutable);
    test_osstring_push(&mut mutable, OsStr::new(" world"));
    println!("After push: {:?}", mutable);

    test_osstring_clear(&mut mutable);
    println!("After clear: {:?}", mutable);
    println!("After clear is_empty: {}", test_osstring_is_empty(&mutable));

    // Test as_os_str
    let owned2 = OsString::from("test");
    let borrowed = test_osstring_as_os_str(&owned2);
    println!("as_os_str: {:?}", borrowed);

    // Test Path integration
    let from_path = test_osstring_from_path();
    println!("From path: {:?}", from_path);

    println!("All OsStr/OsString tests completed!");
}
