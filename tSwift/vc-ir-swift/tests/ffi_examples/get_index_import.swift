// Swift imports for get(index) FFI tests
// All should PASS verification - conditions translate correctly via normalization:
// - Rust: buffer.get(index).is_some() -> Swift equivalent: index < buffer.count

/// Import get_element with compatible precondition
/// Swift uses index < count which is equivalent to Rust .get(index).is_some()
@_ffi_import("get_element")
@_ffi_requires("index < buffer.count")
@_ffi_ensures("result >= 0")
func getElement(_ buffer: UnsafeBufferPointer<UInt8>, _ index: UInt) -> Int64

/// Import slice_range with compatible bounds
/// Swift uses start < end && end <= count which is compatible
@_ffi_import("slice_range")
@_ffi_requires("start < data.count && start < end && end <= data.count")
@_ffi_ensures("result >= 0")
func sliceRange(_ data: UnsafeBufferPointer<UInt8>, _ start: UInt, _ end: UInt) -> Int64

/// Import is_valid_index with no precondition
@_ffi_import("is_valid_index")
func isValidIndex(_ buffer: UnsafeBufferPointer<UInt8>, _ index: UInt) -> Bool

/// Import get_or_default with compatible precondition
/// Swift uses (index < count) || default >= 0 which is compatible
@_ffi_import("get_or_default")
@_ffi_requires("index < buffer.count || default >= 0")
@_ffi_ensures("result >= 0")
func getOrDefault(_ buffer: UnsafeBufferPointer<UInt8>, _ index: UInt, _ default: Int64) -> Int64
