// Example Rust FFI exports using .lines().count() in conditions
// Demonstrates normalization of Rust string line counting to Swift .lines.count
// Note: Uses byte arrays for type compatibility; pattern applies to text processing

/// Check that text has lines using lines().count()
/// The .lines().count() idiom is used for line counting in Rust strings
#[ffi_export]
#[ffi_requires("text.lines().count() > 0")]
#[ffi_ensures("result > 0")]
pub fn line_count(text: &[u8]) -> usize {
    // In real code this would parse newlines
    text.len()
}

/// Validate line count within bounds using lines().count()
#[ffi_export]
#[ffi_requires("text.lines().count() >= min_lines && text.lines().count() <= max_lines && min_lines <= max_lines")]
#[ffi_ensures("result >= min_lines && result <= max_lines")]
pub fn bounded_line_count(text: &[u8], min_lines: usize, max_lines: usize) -> usize {
    // In real code this would count lines
    text.len()
}

/// Check line limit using lines().count()
#[ffi_export]
#[ffi_requires("text.lines().count() <= 100")]
#[ffi_ensures("result == text.lines().count()")]
pub fn limited_line_count(text: &[u8]) -> usize {
    // In real code this would count lines
    text.len()
}
