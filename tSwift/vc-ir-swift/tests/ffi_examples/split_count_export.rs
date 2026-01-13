// Example Rust FFI exports using .split(delimiter).count() in conditions
// Demonstrates normalization of Rust string splitting count to Swift conditions
// Note: Uses byte arrays for type compatibility; pattern applies to text processing

/// Check that text can be split into parts using split().count()
/// The .split(delim).count() idiom is used for counting parts in Rust strings
#[ffi_export]
#[ffi_requires("text.split(',').count() > 1")]
#[ffi_ensures("result > 0")]
pub fn csv_field_count(text: &[u8]) -> usize {
    // In real code this would count CSV fields
    text.len()
}

/// Validate split count within bounds using split().count()
#[ffi_export]
#[ffi_requires("text.split(delimiter).count() >= min_parts && text.split(delimiter).count() <= max_parts && min_parts <= max_parts")]
#[ffi_ensures("result >= min_parts && result <= max_parts")]
pub fn bounded_split_count(text: &[u8], delimiter: u8, min_parts: usize, max_parts: usize) -> usize {
    // In real code this would count split parts
    text.len()
}

/// Check line split using split().count() with newline
#[ffi_export]
#[ffi_requires("text.split('\\n').count() <= 100")]
#[ffi_ensures("result == text.split('\\n').count()")]
pub fn limited_line_split(text: &[u8]) -> usize {
    // In real code this would count lines by splitting on newline
    text.len()
}
