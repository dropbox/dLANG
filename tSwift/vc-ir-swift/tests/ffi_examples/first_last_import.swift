// Swift imports for first/last FFI tests
// All should PASS verification - conditions translate correctly via normalization:
// - Rust: buffer.first().is_some() -> Swift equivalent: buffer.count > 0
// - Rust: buffer.first().is_none() -> Swift equivalent: buffer.count == 0

/// Import process_first with compatible precondition
/// Swift uses .count >= 1 which is equivalent to Rust .first().is_some()
@_ffi_import("process_first")
@_ffi_requires("buffer.count >= 1")
@_ffi_ensures("result >= 1")
func processFirst(_ buffer: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import process_last with compatible precondition
/// Swift uses .count > 0 which is equivalent to Rust .last().is_some()
@_ffi_import("process_last")
@_ffi_requires("buffer.count > 0")
@_ffi_ensures("result >= 1")
func processLast(_ buffer: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import bounded_first with compatible bounds
/// Swift uses stricter .count >= 1 && .count <= 512 (subset of 1..1024)
@_ffi_import("bounded_first")
@_ffi_requires("data.count >= 1 && data.count <= 512")
@_ffi_ensures("result <= data.count")
func boundedFirst(_ data: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import check_empty_via_first with no precondition (Rust has none)
@_ffi_import("check_empty_via_first")
func checkEmptyViaFirst(_ buffer: UnsafeBufferPointer<UInt8>) -> Bool
