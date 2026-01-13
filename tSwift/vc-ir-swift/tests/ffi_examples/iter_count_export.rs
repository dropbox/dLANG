// Example Rust FFI exports using .iter().count() in conditions
// Demonstrates normalization of Rust iterator count to Swift .count

/// Process items - requires at least one item using .iter().count()
#[ffi_export]
#[ffi_requires("items.iter().count() > 0")]
#[ffi_ensures("result >= 1")]
pub fn process_items(items: &[u8]) -> usize {
    items.len()
}

/// Count check - ensures output matches input count
#[ffi_export]
#[ffi_requires("data.iter().count() >= 1")]
#[ffi_ensures("result == data.iter().count()")]
pub fn count_items(data: &[u8]) -> usize {
    data.len()
}

/// Combined conditions - non-empty and bounded using iterator
#[ffi_export]
#[ffi_requires("buffer.iter().count() >= n && n > 0 && n <= 256")]
#[ffi_ensures("result <= buffer.iter().count()")]
pub fn bounded_iter_process(buffer: &[u8], n: usize) -> usize {
    std::cmp::min(buffer.len(), n)
}
