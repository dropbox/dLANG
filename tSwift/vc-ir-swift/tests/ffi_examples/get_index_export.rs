// Example Rust FFI exports for .get(index) patterns
// Demonstrates verification of bounds-checked access using get().is_some()

/// Get element at index - requires index in bounds
/// Uses .get(index).is_some() pattern for bounds checking
#[ffi_export]
#[ffi_requires("buffer.get(index).is_some()")]
#[ffi_ensures("result >= 0")]
pub fn get_element(buffer: &[u8], index: usize) -> i64 {
    buffer[index] as i64
}

/// Safe slice access with bounded range
/// Combines .get() pattern with additional constraints
#[ffi_export]
#[ffi_requires("data.get(start).is_some() && start < end && end <= data.len()")]
#[ffi_ensures("result >= 0")]
pub fn slice_range(data: &[u8], start: usize, end: usize) -> i64 {
    data[start..end].iter().map(|&b| b as i64).sum()
}

/// Check if index is valid (returns bool)
/// No precondition - always safe to call
#[ffi_export]
#[ffi_ensures("result == true || result == false")]
pub fn is_valid_index(buffer: &[u8], index: usize) -> bool {
    buffer.get(index).is_some()
}

/// Get element or default - safe accessor
/// Uses .get() pattern to demonstrate bounds checking
#[ffi_export]
#[ffi_requires("!buffer.get(index).is_none() || default >= 0")]
#[ffi_ensures("result >= 0")]
pub fn get_or_default(buffer: &[u8], index: usize, default: i64) -> i64 {
    buffer.get(index).map(|&b| b as i64).unwrap_or(default)
}
