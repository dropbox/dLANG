// Example Rust FFI exports using range.len() patterns
// Demonstrates normalization of Rust range length expressions to arithmetic

/// Copy a range of elements - requires range has positive length
#[ffi_export]
#[ffi_requires("start < end && (start..end).len() <= buffer.len()")]
#[ffi_ensures("result == (start..end).len() as i64")]
pub fn copy_range(buffer: &[u8], start: usize, end: usize) -> i64 {
    (end - start) as i64
}

/// Get range size - inclusive range uses (a..=b).len() which is (b - a + 1)
#[ffi_export]
#[ffi_requires("start <= end && (start..=end).len() <= buffer.len()")]
#[ffi_ensures("result >= 1")]
pub fn get_inclusive_range_size(buffer: &[u8], start: usize, end: usize) -> i64 {
    ((end - start) + 1) as i64
}

