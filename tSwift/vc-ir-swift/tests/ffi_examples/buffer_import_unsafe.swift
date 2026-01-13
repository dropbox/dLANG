// UNSAFE Swift imports for buffer operations FFI
// These should FAIL verification (type mismatches)

/// UNSAFE: Wrong return type - Swift expects Int32 (32-bit), Rust provides usize (64-bit)
/// This is an intentional type mismatch to test type layout verification
@_ffi_import("parse_buffer")
@_ffi_ensures("result <= buffer.count")
func parseBufferUnsafe(_ buffer: UnsafeBufferPointer<UInt8>) -> Int32

/// UNSAFE: Wrong return type - Swift expects Int64 (signed), Rust provides u32 (unsigned)
@_ffi_import("compute_checksum")
@_ffi_requires("data.count > 0 && data.count <= 1048576")
@_ffi_ensures("result >= 0")
func computeChecksumUnsafe(_ data: UnsafeBufferPointer<UInt8>) -> Int64

/// UNSAFE: Wrong return type - Swift expects Int64 (64-bit), Rust provides i32 (32-bit)
@_ffi_import("compare_buffers")
@_ffi_ensures("result >= -1 && result <= 1")
func compareBuffersUnsafe(a: UnsafeBufferPointer<UInt8>, b: UnsafeBufferPointer<UInt8>) -> Int64
