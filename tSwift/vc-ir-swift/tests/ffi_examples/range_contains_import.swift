// Swift imports for range.contains() FFI tests
// All should PASS verification - conditions translate correctly via normalization:
// - Rust: (0..buffer.len()).contains(&index) -> Swift equivalent: index < buffer.count
// - Rust: (start..end).contains(&index) -> Swift equivalent: index >= start && index < end

/// Import read_at with compatible precondition
@_ffi_import("read_at")
@_ffi_requires("index < buffer.count")
@_ffi_ensures("result >= 0")
func readAt(_ buffer: UnsafeBufferPointer<UInt8>, _ index: UInt) -> Int64

/// Import read_at_range with compatible bounds
@_ffi_import("read_at_range")
@_ffi_requires("index >= start && index < end && end <= buffer.count")
@_ffi_ensures("result >= 0")
func readAtRange(_ buffer: UnsafeBufferPointer<UInt8>, _ start: UInt, _ end: UInt, _ index: UInt) -> Int64

