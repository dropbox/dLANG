// Swift imports for buffer operations FFI
// All these should PASS verification (stronger or matching preconditions)

/// Import parse_buffer with stronger precondition (requires at least 4 bytes)
/// Returns UInt64 to match Rust's usize
@_ffi_import("parse_buffer")
@_ffi_requires("buffer.count >= 4")
@_ffi_ensures("result <= buffer.count")
func parseBuffer(_ buffer: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import compare_buffers with stronger precondition (requires at least 2 bytes)
@_ffi_import("compare_buffers")
@_ffi_requires("a.count >= 2 && b.count >= 2")
@_ffi_ensures("result >= -1 && result <= 1")
func compareBuffers(a: UnsafeBufferPointer<UInt8>, b: UnsafeBufferPointer<UInt8>) -> Int32

/// Import find_byte with stronger precondition (requires at least 2 bytes)
@_ffi_import("find_byte")
@_ffi_requires("haystack.count >= 2")
@_ffi_ensures("result >= -1 && result < haystack.count")
func findByte(_ haystack: UnsafeBufferPointer<UInt8>, _ needle: UInt8) -> Int64

/// Import is_valid_utf8 with no precondition (Rust has none)
@_ffi_import("is_valid_utf8")
func isValidUTF8(_ buffer: UnsafeBufferPointer<UInt8>) -> Bool

/// Import compute_checksum with stronger bounds
@_ffi_import("compute_checksum")
@_ffi_requires("data.count >= 16 && data.count <= 4096")
@_ffi_ensures("result >= 0")
func computeChecksum(_ data: UnsafeBufferPointer<UInt8>) -> UInt32
