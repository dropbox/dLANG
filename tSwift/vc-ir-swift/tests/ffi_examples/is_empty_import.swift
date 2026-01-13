// Swift imports for is_empty FFI tests
// All should PASS verification - conditions translate correctly

/// Import process_buffer with compatible precondition
/// Swift uses .count > 0 which should be equivalent to !buffer.is_empty()
@_ffi_import("process_buffer")
@_ffi_requires("buffer.count >= 1")
@_ffi_ensures("result >= 1")
func processBuffer(_ buffer: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import check_empty with no precondition (Rust has none)
@_ffi_import("check_empty")
func checkEmpty(_ buffer: UnsafeBufferPointer<UInt8>) -> Bool

/// Import bounded_process with compatible bounds
@_ffi_import("bounded_process")
@_ffi_requires("data.count >= 1 && data.count <= 512")
@_ffi_ensures("result <= data.count")
func boundedProcess(_ data: UnsafeBufferPointer<UInt8>) -> UInt64
