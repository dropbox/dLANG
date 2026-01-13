// Example Rust FFI exports using .is_empty() in conditions
// Demonstrates normalization of Rust-style .is_empty() to count comparisons

/// Process buffer - requires non-empty buffer using .is_empty()
#[ffi_export]
#[ffi_requires("!buffer.is_empty()")]
#[ffi_ensures("result >= 1")]
pub fn process_buffer(buffer: &[u8]) -> usize {
    buffer.len()
}

/// Validate empty - returns true if buffer is empty
#[ffi_export]
#[ffi_ensures("(result == true && buffer.len() == 0) || (result == false && buffer.len() > 0)")]
pub fn check_empty(buffer: &[u8]) -> bool {
    buffer.is_empty()
}

/// Combined conditions - non-empty and bounded
#[ffi_export]
#[ffi_requires("!data.is_empty() && data.len() <= 1024")]
#[ffi_ensures("result <= data.len()")]
pub fn bounded_process(data: &[u8]) -> usize {
    data.len()
}
