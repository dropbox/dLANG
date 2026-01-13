// Rust FFI export with .iter().take(n).count() and .iter().skip(n).count() conditions
// These patterns should normalize to .take(n).count and .skip(n).count for FFI verification
// Uses simple integer parameters to test normalization without array type complexity

/// Process items bounded by take limit.
/// Precondition uses .iter().take(n).count() pattern - Rust idiom for bounded iteration.
/// items_len represents the collection length; limit is the take bound.
#[ffi_export]
#[ffi_requires("items.iter().take(limit).count() >= 1 && limit > 0")]
#[ffi_ensures("result >= 0")]
pub fn process_first_n(items_len: usize, limit: usize) -> i32 {
    items_len.min(limit) as i32
}

/// Skip pattern: ensure items remain after skipping offset.
/// Precondition uses .iter().skip(n).count() pattern.
#[ffi_export]
#[ffi_requires("items.iter().skip(offset).count() > 0")]
#[ffi_ensures("result >= 0")]
pub fn process_after_skip(items_len: usize, offset: usize) -> i32 {
    items_len.saturating_sub(offset) as i32
}

/// Combined take and skip: take first n, require at least min items.
#[ffi_export]
#[ffi_requires("items.iter().take(n).count() >= min && min > 0")]
#[ffi_ensures("result > 0")]
pub fn process_bounded(items_len: usize, n: usize, min: usize) -> i32 {
    1
}
