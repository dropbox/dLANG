// Example Rust FFI exports using Option.is_some()/is_none() patterns
// Demonstrates normalization of Rust Option presence checks to nil comparisons.

/// Requires a present value via `Option::is_some()`.
#[ffi_export]
#[ffi_requires("value.is_some()")]
#[ffi_ensures("result >= 0")]
pub fn require_some(value: Option<i32>) -> i32 {
    value.unwrap_or(0)
}

/// Requires an absent value via `Option::is_none()`.
#[ffi_export]
#[ffi_requires("value.is_none()")]
#[ffi_ensures("result == 0")]
pub fn require_none(_value: Option<i32>) -> i32 {
    0
}

