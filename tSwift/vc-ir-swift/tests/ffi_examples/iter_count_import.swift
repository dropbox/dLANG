// Swift imports for iter().count() FFI tests
// All should PASS verification - conditions translate correctly

/// Import process_items with compatible precondition
/// Swift uses .count > 0 which is equivalent to .iter().count() > 0
@_ffi_import("process_items")
@_ffi_requires("items.count >= 1")
@_ffi_ensures("result >= 1")
func processItems(_ items: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import count_items with compatible condition
@_ffi_import("count_items")
@_ffi_requires("data.count >= 1")
@_ffi_ensures("result == data.count")
func countItems(_ data: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import bounded_iter_process with compatible bounds
/// n > 0 is stronger than n >= 1 (Rust uses >=), but Swift import is stronger
@_ffi_import("bounded_iter_process")
@_ffi_requires("buffer.count >= n && n >= 1 && n <= 128")
@_ffi_ensures("result <= buffer.count")
func boundedIterProcess(_ buffer: UnsafeBufferPointer<UInt8>, _ n: UInt64) -> UInt64
