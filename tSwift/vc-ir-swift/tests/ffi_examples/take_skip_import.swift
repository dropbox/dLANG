// Swift FFI import with .take(n).count and .skip(n).count conditions
// These match the Rust .iter().take(n).count() and .iter().skip(n).count() patterns
// Uses simple integer parameters to test normalization without array type complexity

/// Process items bounded by take limit.
/// Precondition uses Swift-style .take(n).count pattern.
@_ffi_import("process_first_n")
@_ffi_requires("items.take(limit).count >= 1 && limit > 0")
@_ffi_ensures("result >= 0")
func processFirstN(_ itemsLen: UInt64, _ limit: UInt64) -> Int32

/// Skip pattern: ensure items remain after skipping offset.
/// Precondition uses Swift-style .skip(n).count pattern.
@_ffi_import("process_after_skip")
@_ffi_requires("items.skip(offset).count > 0")
@_ffi_ensures("result >= 0")
func processAfterSkip(_ itemsLen: UInt64, _ offset: UInt64) -> Int32

/// Combined take and skip: take first n, require at least min items.
@_ffi_import("process_bounded")
@_ffi_requires("items.take(n).count >= min && min > 0")
@_ffi_ensures("result > 0")
func processBounded(_ itemsLen: UInt64, _ n: UInt64, _ min: UInt64) -> Int32
