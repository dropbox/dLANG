// Swift imports for bytes().count() FFI tests
// All should PASS verification - conditions translate correctly
// Note: Uses byte buffers for type compatibility; tests .bytes().count() pattern normalization
// Swift's .utf8.count is equivalent to Rust's .bytes().count()

/// Import byte_length with compatible precondition
/// Swift uses .utf8.count >= 1 which is equivalent to .bytes().count() > 0
@_ffi_import("byte_length")
@_ffi_requires("data.utf8.count >= 1")
@_ffi_ensures("result > 0")
func byteLength(_ data: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import bounded_byte_length with compatible bounds
/// Swift uses .utf8.count which is equivalent to .bytes().count()
@_ffi_import("bounded_byte_length")
@_ffi_requires("data.utf8.count >= minBytes && data.utf8.count <= maxBytes && minBytes <= maxBytes")
@_ffi_ensures("result >= minBytes && result <= maxBytes")
func boundedByteLength(_ data: UnsafeBufferPointer<UInt8>, _ minBytes: UInt64, _ maxBytes: UInt64) -> UInt64

/// Import buffer_capacity with compatible condition
@_ffi_import("buffer_capacity")
@_ffi_requires("data.utf8.count <= 1024")
@_ffi_ensures("result == data.utf8.count")
func bufferCapacity(_ data: UnsafeBufferPointer<UInt8>) -> UInt64
