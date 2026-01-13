// Example Rust FFI exports using .into_iter().count() and .iter_mut().count() in conditions
// Demonstrates normalization of Rust iterator variants to Swift .count

/// Process items using into_iter().count() - owns the iterator
#[ffi_export]
#[ffi_requires("items.into_iter().count() > 0")]
#[ffi_ensures("result >= 1")]
pub fn process_into_iter(items: &[u8]) -> usize {
    items.len()
}

/// Count check using iter_mut().count() in condition (immutable param for type compat)
#[ffi_export]
#[ffi_requires("data.iter_mut().count() >= 1")]
#[ffi_ensures("result == data.iter_mut().count()")]
pub fn count_iter_mut(data: &[u8]) -> usize {
    data.len()
}

/// Combined conditions using both variants
#[ffi_export]
#[ffi_requires("buffer.into_iter().count() >= n && n > 0 && n <= 256")]
#[ffi_ensures("result <= buffer.iter_mut().count()")]
pub fn bounded_mixed_iter(buffer: &[u8], n: usize) -> usize {
    std::cmp::min(buffer.len(), n)
}
