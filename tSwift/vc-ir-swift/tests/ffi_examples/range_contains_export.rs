// Example Rust FFI exports using range.contains(&index) patterns
// Demonstrates normalization of Rust range membership checks to bounds comparisons

/// Read element at index - requires index in bounds using range.contains(&index)
#[ffi_export]
#[ffi_requires("(0..buffer.len()).contains(&index)")]
#[ffi_ensures("result >= 0")]
pub fn read_at(buffer: &[u8], index: usize) -> i64 {
    buffer[index] as i64
}

/// Read element at index with caller-provided bounds
/// Uses a non-zero start range to exercise both lower/upper bound normalization
#[ffi_export]
#[ffi_requires("(start..end).contains(&index) && end <= buffer.len()")]
#[ffi_ensures("result >= 0")]
pub fn read_at_range(buffer: &[u8], start: usize, end: usize, index: usize) -> i64 {
    buffer[index] as i64
}

