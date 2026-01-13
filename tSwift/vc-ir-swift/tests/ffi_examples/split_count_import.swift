// Swift imports for split().count() FFI tests
// All should PASS verification - conditions translate correctly
// Note: Uses byte buffers for type compatibility; tests .split().count() pattern normalization
// Swift's .split().count is the normalized form of Rust's .split(delimiter).count()

/// Import csv_field_count with compatible precondition
/// Swift uses .split(',').count >= 2 which is equivalent to .split(',').count() > 1
@_ffi_import("csv_field_count")
@_ffi_requires("text.split(',').count >= 2")
@_ffi_ensures("result > 0")
func csvFieldCount(_ text: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import bounded_split_count with compatible bounds
/// Swift uses .split(delimiter).count which is equivalent to .split(delimiter).count()
@_ffi_import("bounded_split_count")
@_ffi_requires("text.split(delimiter).count >= minParts && text.split(delimiter).count <= maxParts && minParts <= maxParts")
@_ffi_ensures("result >= minParts && result <= maxParts")
func boundedSplitCount(_ text: UnsafeBufferPointer<UInt8>, _ delimiter: UInt8, _ minParts: UInt64, _ maxParts: UInt64) -> UInt64

/// Import limited_line_split with compatible condition
@_ffi_import("limited_line_split")
@_ffi_requires("text.split('\\n').count <= 100")
@_ffi_ensures("result == text.split('\\n').count")
func limitedLineSplit(_ text: UnsafeBufferPointer<UInt8>) -> UInt64
