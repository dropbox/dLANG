// Swift imports for chars().count() FFI tests
// All should PASS verification - conditions translate correctly
// Note: Uses byte buffers for type compatibility; tests .chars().count() pattern normalization

/// Import text_length with compatible precondition
/// Swift uses .count > 0 which is equivalent to .chars().count() > 0
@_ffi_import("text_length")
@_ffi_requires("text.count >= 1")
@_ffi_ensures("result > 0")
func textLength(_ text: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import bounded_text_length with compatible bounds
/// Swift uses .count which is equivalent to .chars().count()
@_ffi_import("bounded_text_length")
@_ffi_requires("name.count >= minLen && name.count <= maxLen && minLen <= maxLen")
@_ffi_ensures("result >= minLen && result <= maxLen")
func boundedTextLength(_ name: UnsafeBufferPointer<UInt8>, _ minLen: UInt64, _ maxLen: UInt64) -> UInt64

/// Import remaining_capacity with compatible condition
@_ffi_import("remaining_capacity")
@_ffi_requires("text.count <= 256")
@_ffi_ensures("result == text.count")
func remainingCapacity(_ text: UnsafeBufferPointer<UInt8>) -> UInt64
