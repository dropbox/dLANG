// Example Rust FFI exports using .chars().count() in conditions
// Demonstrates normalization of Rust string character counting to Swift .count
// Note: Uses byte arrays for type compatibility; pattern applies to any collection

/// Check that text is not empty using chars().count()
/// The .chars().count() idiom is used for Unicode character counting in Rust
#[ffi_export]
#[ffi_requires("text.chars().count() > 0")]
#[ffi_ensures("result > 0")]
pub fn text_length(text: &[u8]) -> usize {
    text.len()
}

/// Validate text length within bounds using chars().count()
#[ffi_export]
#[ffi_requires("name.chars().count() >= min_len && name.chars().count() <= max_len && min_len <= max_len")]
#[ffi_ensures("result >= min_len && result <= max_len")]
pub fn bounded_text_length(name: &[u8], min_len: usize, max_len: usize) -> usize {
    name.len()
}

/// Check text capacity using chars().count()
#[ffi_export]
#[ffi_requires("text.chars().count() <= 256")]
#[ffi_ensures("result == text.chars().count()")]
pub fn remaining_capacity(text: &[u8]) -> usize {
    text.len()
}
