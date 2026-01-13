// secure_buffer.rs
//
// Example Rust FFI exports with formal verification specifications.
// This demonstrates how tSwift verifies cross-language contracts.
//
// Verify: tswift-ffi-verify --swift secure_buffer_import.swift --rust secure_buffer.rs --z4 --verbose

/// Allocate a secure buffer of specified size.
///
/// The buffer size must be positive and within safe limits.
/// Returns the allocated size (or 0 on failure).
#[ffi_export]
#[ffi_requires("size > 0 && size <= 1073741824")]
#[ffi_ensures("result >= 0")]
pub fn secure_alloc(size: i64) -> i64 {
    size  // Returns allocated size
}

/// Compute hash of an input value.
///
/// The input must be non-negative.
/// Returns a hash that is always non-negative.
#[ffi_export]
#[ffi_requires("input >= 0")]
#[ffi_ensures("result >= 0")]
pub fn compute_hash(input: i64) -> i64 {
    input % 1000000007  // Simple hash
}

/// Validate buffer size for security constraints.
///
/// Size must be positive and within limits.
/// Returns 1 if valid, 0 if invalid.
#[ffi_export]
#[ffi_requires("size > 0")]
#[ffi_ensures("result == 0 || result == 1")]
pub fn validate_size(size: i64) -> i32 {
    if size <= 1073741824 { 1 } else { 0 }
}

/// Safe integer increment with bounds checking.
///
/// Value must be less than max to prevent overflow.
#[ffi_export]
#[ffi_requires("value < 9223372036854775807")]
#[ffi_ensures("result == value + 1")]
pub fn safe_increment(value: i64) -> i64 {
    value + 1
}

/// Compute the absolute difference between two values.
///
/// Both values must be non-negative.
/// Result is always non-negative.
#[ffi_export]
#[ffi_requires("a >= 0 && b >= 0")]
#[ffi_ensures("result >= 0")]
pub fn abs_diff(a: i64, b: i64) -> i64 {
    if a >= b { a - b } else { b - a }
}
