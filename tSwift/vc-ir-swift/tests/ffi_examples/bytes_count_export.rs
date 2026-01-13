// Example Rust FFI exports using .bytes().count() in conditions
// Demonstrates normalization of Rust string byte counting to Swift .utf8.count
// Note: Uses byte arrays for type compatibility; pattern applies to any byte collection

/// Check that data has bytes using bytes().count()
/// The .bytes().count() idiom is used for byte counting in Rust strings
#[ffi_export]
#[ffi_requires("data.bytes().count() > 0")]
#[ffi_ensures("result > 0")]
pub fn byte_length(data: &[u8]) -> usize {
    data.len()
}

/// Validate byte length within bounds using bytes().count()
#[ffi_export]
#[ffi_requires("data.bytes().count() >= min_bytes && data.bytes().count() <= max_bytes && min_bytes <= max_bytes")]
#[ffi_ensures("result >= min_bytes && result <= max_bytes")]
pub fn bounded_byte_length(data: &[u8], min_bytes: usize, max_bytes: usize) -> usize {
    data.len()
}

/// Check byte capacity using bytes().count()
#[ffi_export]
#[ffi_requires("data.bytes().count() <= 1024")]
#[ffi_ensures("result == data.bytes().count()")]
pub fn buffer_capacity(data: &[u8]) -> usize {
    data.len()
}
