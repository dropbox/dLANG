// Example Rust FFI exports for buffer operations
// Demonstrates verification of slice/buffer preconditions

/// Parse buffer - requires non-empty buffer
#[ffi_export]
#[ffi_requires("buffer.len() > 0")]
#[ffi_ensures("result <= buffer.len()")]
pub fn parse_buffer(buffer: &[u8]) -> usize {
    // Parse and return bytes consumed
    buffer.len()
}

/// Safe buffer compare - requires non-empty buffers
#[ffi_export]
#[ffi_requires("a.len() > 0 && b.len() > 0")]
#[ffi_ensures("result >= -1 && result <= 1")]
pub fn compare_buffers(a: &[u8], b: &[u8]) -> i32 {
    match a.cmp(b) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

/// Search for byte - requires non-empty haystack
#[ffi_export]
#[ffi_requires("haystack.len() > 0")]
#[ffi_ensures("result >= -1 && result < haystack.len() as i64")]
pub fn find_byte(haystack: &[u8], needle: u8) -> i64 {
    haystack.iter()
        .position(|&b| b == needle)
        .map(|i| i as i64)
        .unwrap_or(-1)
}

/// Validate UTF-8 - returns true if buffer is valid UTF-8
#[ffi_export]
#[ffi_ensures("result == true || result == false")]
pub fn is_valid_utf8(buffer: &[u8]) -> bool {
    std::str::from_utf8(buffer).is_ok()
}

/// Compute checksum with non-empty buffer requirement
#[ffi_export]
#[ffi_requires("data.len() > 0 && data.len() <= 65536")]
#[ffi_ensures("result >= 0")]
pub fn compute_checksum(data: &[u8]) -> u32 {
    data.iter().fold(0u32, |acc, &b| acc.wrapping_add(b as u32))
}
