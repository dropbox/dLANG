// Swift imports for lines().count() FFI tests
// All should PASS verification - conditions translate correctly
// Note: Uses byte buffers for type compatibility; tests .lines().count() pattern normalization
// Swift's .lines.count is the normalized form of Rust's .lines().count()

/// Import line_count with compatible precondition
/// Swift uses .lines.count >= 1 which is equivalent to .lines().count() > 0
@_ffi_import("line_count")
@_ffi_requires("text.lines.count >= 1")
@_ffi_ensures("result > 0")
func lineCount(_ text: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import bounded_line_count with compatible bounds
/// Swift uses .lines.count which is equivalent to .lines().count()
@_ffi_import("bounded_line_count")
@_ffi_requires("text.lines.count >= minLines && text.lines.count <= maxLines && minLines <= maxLines")
@_ffi_ensures("result >= minLines && result <= maxLines")
func boundedLineCount(_ text: UnsafeBufferPointer<UInt8>, _ minLines: UInt64, _ maxLines: UInt64) -> UInt64

/// Import limited_line_count with compatible condition
@_ffi_import("limited_line_count")
@_ffi_requires("text.lines.count <= 100")
@_ffi_ensures("result == text.lines.count")
func limitedLineCount(_ text: UnsafeBufferPointer<UInt8>) -> UInt64
