//! Example Rust core library with FFI exports.
//!
//! These functions are called from Swift via FFI.

use tswift_ffi_macros::{ffi_ensures, ffi_export, ffi_requires};

/// Compute factorial of n.
#[ffi_export]
#[ffi_requires("n >= 0 && n <= 20")]
#[ffi_ensures("result >= 1")]
#[no_mangle]
pub extern "C" fn factorial(n: i64) -> i64 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

/// Safely divide two integers.
#[ffi_export]
#[ffi_requires("divisor != 0")]
#[ffi_ensures("true")]
#[no_mangle]
pub extern "C" fn safe_divide(dividend: i64, divisor: i64) -> i64 {
    dividend / divisor
}

/// Clamp a value to a range [min, max].
#[ffi_export]
#[ffi_requires("min <= max")]
#[ffi_ensures("result >= min && result <= max")]
#[no_mangle]
pub extern "C" fn clamp(value: i64, min: i64, max: i64) -> i64 {
    if value < min {
        min
    } else if value > max {
        max
    } else {
        value
    }
}
