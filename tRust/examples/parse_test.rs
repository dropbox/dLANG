//! Integration tests for parsing contracts (Phase 10.1)
//!
//! Tests parsing methods:
//! - from_str_radix precondition: radix must be in [2, 36]
//! - from_str_radix postcondition: unsigned types return non-negative values when Ok
//! - str::parse documented (returns Result, runtime-dependent)

#![allow(dead_code)]

// =========================================================================
// from_str_radix precondition: radix in [2, 36]
// =========================================================================

/// Test 1: from_str_radix with valid radix (base 10)
fn test_from_str_radix_decimal() -> Result<i32, std::num::ParseIntError> {
    i32::from_str_radix("42", 10)
}

/// Test 2: from_str_radix with valid radix (base 2)
fn test_from_str_radix_binary() -> Result<u32, std::num::ParseIntError> {
    u32::from_str_radix("1010", 2)
}

/// Test 3: from_str_radix with valid radix (base 16)
fn test_from_str_radix_hex() -> Result<u64, std::num::ParseIntError> {
    u64::from_str_radix("ff", 16)
}

/// Test 4: from_str_radix with valid radix (base 36 - maximum)
fn test_from_str_radix_base36() -> Result<u32, std::num::ParseIntError> {
    u32::from_str_radix("z", 36) // z = 35 in base 36
}

/// Test 5: from_str_radix with minimum valid radix (base 2)
fn test_from_str_radix_min_radix() -> Result<i64, std::num::ParseIntError> {
    i64::from_str_radix("11", 2) // 3 in binary
}

// =========================================================================
// Unsigned from_str_radix postcondition: value >= 0 when Ok
// =========================================================================

/// Test 6: u32::from_str_radix result is non-negative when Ok
#[requires("radix >= 2 && radix <= 36")]
fn test_u32_from_str_radix_nonneg(s: &str, radix: u32) -> Option<u32> {
    match u32::from_str_radix(s, radix) {
        Ok(v) => Some(v), // v >= 0 guaranteed by contract
        Err(_) => None,
    }
}

/// Test 7: u64::from_str_radix returns non-negative value
#[requires("radix >= 2 && radix <= 36")]
fn test_u64_from_str_radix_nonneg(s: &str, radix: u32) -> Option<u64> {
    match u64::from_str_radix(s, radix) {
        Ok(v) => Some(v),
        Err(_) => None,
    }
}

/// Test 8: u8::from_str_radix returns non-negative value
fn test_u8_from_str_radix() -> Result<u8, std::num::ParseIntError> {
    u8::from_str_radix("255", 10)
}

/// Test 9: usize::from_str_radix returns non-negative value
fn test_usize_from_str_radix() -> Result<usize, std::num::ParseIntError> {
    usize::from_str_radix("1000", 10)
}

// =========================================================================
// Signed from_str_radix (no specific postcondition)
// =========================================================================

/// Test 10: i32::from_str_radix with positive value
fn test_i32_from_str_radix_positive() -> Result<i32, std::num::ParseIntError> {
    i32::from_str_radix("42", 10)
}

/// Test 11: i32::from_str_radix with negative value
fn test_i32_from_str_radix_negative() -> Result<i32, std::num::ParseIntError> {
    i32::from_str_radix("-42", 10)
}

/// Test 12: i64::from_str_radix in hex
fn test_i64_from_str_radix_hex() -> Result<i64, std::num::ParseIntError> {
    i64::from_str_radix("7fffffff", 16) // Max i32 as i64
}

// =========================================================================
// str::parse (documented, returns Result)
// =========================================================================

/// Test 13: str::parse to i32
fn test_str_parse_i32() -> Result<i32, std::num::ParseIntError> {
    "42".parse::<i32>()
}

/// Test 14: str::parse to u32
fn test_str_parse_u32() -> Result<u32, std::num::ParseIntError> {
    "100".parse::<u32>()
}

/// Test 15: str::parse to f64 (documented)
fn test_str_parse_f64() -> Result<f64, std::num::ParseFloatError> {
    "3.14".parse::<f64>()
}

// =========================================================================
// Main test function
// =========================================================================

fn main() {
    // from_str_radix precondition tests (valid radixes)
    let _ = test_from_str_radix_decimal();
    let _ = test_from_str_radix_binary();
    let _ = test_from_str_radix_hex();
    let _ = test_from_str_radix_base36();
    let _ = test_from_str_radix_min_radix();

    // Unsigned from_str_radix tests
    let _ = test_u32_from_str_radix_nonneg("42", 10);
    let _ = test_u64_from_str_radix_nonneg("100", 10);
    let _ = test_u8_from_str_radix();
    let _ = test_usize_from_str_radix();

    // Signed from_str_radix tests
    let _ = test_i32_from_str_radix_positive();
    let _ = test_i32_from_str_radix_negative();
    let _ = test_i64_from_str_radix_hex();

    // str::parse tests
    let _ = test_str_parse_i32();
    let _ = test_str_parse_u32();
    let _ = test_str_parse_f64();

    println!("All parse tests passed!");
}
