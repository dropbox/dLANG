// Example Rust FFI exports using Result .ok()/.err() patterns in conditions
// Demonstrates normalization of Rust Result checking idioms to Swift conditions
// Common patterns: res.ok().is_some() for checking success, res.err().is_some() for checking failure
// Note: Uses byte arrays for type compatibility; the condition patterns demonstrate the normalization

/// Process data only if previous operation succeeded
/// The .ok().is_some() idiom checks if a Result is Ok
/// Here prev_result represents a status struct with .ok().is_some() check
#[ffi_export]
#[ffi_requires("prev_result.ok().is_some()")]
#[ffi_ensures("result > 0")]
pub fn process_after_success(prev_result: &[u8], data: i32) -> i32 {
    // In real code prev_result would be a Result
    data + 1
}

/// Handle error case using .err().is_some()
/// The .err().is_some() idiom checks if a Result is Err
#[ffi_export]
#[ffi_requires("res.err().is_some()")]
#[ffi_ensures("result >= 0")]
pub fn handle_error(res: &[u8]) -> i32 {
    // In real code res would be a Result
    0
}

/// Check both success and failure patterns together
#[ffi_export]
#[ffi_requires("first.ok().is_some() && second.err().is_none()")]
#[ffi_ensures("result == 1")]
pub fn both_succeeded(first: &[u8], second: &[u8]) -> i32 {
    // Both results are Ok
    1
}

/// Use negated patterns: !res.ok().is_none() means success
#[ffi_export]
#[ffi_requires("!res.ok().is_none()")]
#[ffi_ensures("result > 0")]
pub fn negated_check(res: &[u8], value: i32) -> i32 {
    // res is Ok (double negation: not-is_none = is_some)
    value
}
