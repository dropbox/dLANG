// Example Swift FFI imports for tswift-ffi-verify testing
// These imports should match the Rust exports

/// Import increment with a stronger precondition (x > 5 implies x > 0)
/// This should PASS verification
@_ffi_import("increment")
@_ffi_requires("x > 5")
@_ffi_ensures("result >= x")
func increment(_ x: Int32) -> Int32

/// Import safe_multiply with matching preconditions
/// This should PASS verification
@_ffi_import("safe_multiply")
@_ffi_requires("a > 0 && b > 0")
@_ffi_ensures("result > 0")
func safe_multiply(_ a: Int64, _ b: Int64) -> Int64

/// Import trusted function (skip verification)
@_ffi_import("raw_pointer_op")
@_ffi_trusted
func raw_pointer_op(_ ptr: UnsafeMutablePointer<UInt8>)

/// Import get_size with matching signature
@_ffi_import("get_size")
@_ffi_ensures("result >= 0")
func get_size(_ buffer: UnsafeBufferPointer<UInt8>) -> Int32
