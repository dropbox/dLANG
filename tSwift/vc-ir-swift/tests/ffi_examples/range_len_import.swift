// Swift imports for range.len() FFI tests
// All should PASS verification - conditions translate correctly via normalization:
// - Rust: (start..end).len() -> Swift equivalent: (end - start)
// - Rust: (start..=end).len() -> Swift equivalent: ((end - start) + 1)

/// Import copy_range with compatible precondition using arithmetic
@_ffi_import("copy_range")
@_ffi_requires("start < end && (end - start) <= buffer.count")
@_ffi_ensures("result == (end - start)")
func copyRange(_ buffer: UnsafeBufferPointer<UInt8>, _ start: UInt, _ end: UInt) -> Int64

/// Import get_inclusive_range_size with compatible bounds
@_ffi_import("get_inclusive_range_size")
@_ffi_requires("start <= end && ((end - start) + 1) <= buffer.count")
@_ffi_ensures("result >= 1")
func getInclusiveRangeSize(_ buffer: UnsafeBufferPointer<UInt8>, _ start: UInt, _ end: UInt) -> Int64

