// Example Rust FFI exports using .first().is_some() and .last().is_some() in conditions
// Demonstrates normalization of Rust Option patterns to count comparisons

/// Process buffer - requires non-empty buffer using .first().is_some()
#[ffi_export]
#[ffi_requires("buffer.first().is_some()")]
#[ffi_ensures("result >= 1")]
pub fn process_first(buffer: &[u8]) -> usize {
    buffer.len()
}

/// Check if buffer has last element
#[ffi_export]
#[ffi_requires("buffer.last().is_some()")]
#[ffi_ensures("result >= 1")]
pub fn process_last(buffer: &[u8]) -> usize {
    buffer.len()
}

/// Combined: non-empty via first() and bounded
#[ffi_export]
#[ffi_requires("data.first().is_some() && data.len() <= 1024")]
#[ffi_ensures("result <= data.len()")]
pub fn bounded_first(data: &[u8]) -> usize {
    data.len()
}

/// Check empty via first().is_none()
#[ffi_export]
#[ffi_ensures("(result == true && buffer.first().is_none()) || (result == false && buffer.first().is_some())")]
pub fn check_empty_via_first(buffer: &[u8]) -> bool {
    buffer.is_empty()
}
