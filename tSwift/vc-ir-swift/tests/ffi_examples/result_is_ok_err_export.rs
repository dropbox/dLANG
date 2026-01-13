// Example Rust FFI exports using Result .is_ok()/.is_err() patterns in conditions
// Demonstrates normalization of dotted method calls to Swift-style field access.
//
// Note: Uses byte buffers for type compatibility; the condition patterns demonstrate normalization.

/// Require Ok-style predicate using `.is_ok()`.
#[ffi_export]
#[ffi_requires("res.is_ok()")]
#[ffi_ensures("result > 0")]
pub fn result_is_ok_requires(res: &[u8], value: i32) -> i32 {
    let _ = res;
    value + 1
}

/// Require Err-style predicate using `.is_err()`.
#[ffi_export]
#[ffi_requires("res.is_err()")]
#[ffi_ensures("result == 0")]
pub fn result_is_err_requires(res: &[u8]) -> i32 {
    let _ = res;
    0
}

/// Combine `.is_ok()` with `.unwrap().len()` (normalized to `.isSuccess` and `.value.count`).
#[ffi_export]
#[ffi_requires("res.is_ok() && res.unwrap().len() > 0")]
#[ffi_ensures("result > 0")]
pub fn result_unwrap_len_requires(res: &[u8], value: i32) -> i32 {
    let _ = res;
    value
}

/// Negated `.is_err()` should normalize to success.
#[ffi_export]
#[ffi_requires("!res.is_err()")]
#[ffi_ensures("result > 0")]
pub fn result_not_is_err_requires(res: &[u8], value: i32) -> i32 {
    let _ = res;
    value
}

