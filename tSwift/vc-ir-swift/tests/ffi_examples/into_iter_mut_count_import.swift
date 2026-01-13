// Swift imports for into_iter().count() and iter_mut().count() FFI tests
// All should PASS verification - conditions translate correctly

/// Import process_into_iter with compatible precondition
/// Swift uses .count > 0 which is equivalent to .into_iter().count() > 0
@_ffi_import("process_into_iter")
@_ffi_requires("items.count >= 1")
@_ffi_ensures("result >= 1")
func processIntoIter(_ items: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import count_iter_mut with compatible condition
/// Swift uses .count >= 1 which is equivalent to .iter_mut().count() >= 1
@_ffi_import("count_iter_mut")
@_ffi_requires("data.count >= 1")
@_ffi_ensures("result == data.count")
func countIterMut(_ data: UnsafeBufferPointer<UInt8>) -> UInt64

/// Import bounded_mixed_iter with compatible bounds
/// n > 0 is stronger than n >= 1 (Rust uses >=), but Swift import is stronger
@_ffi_import("bounded_mixed_iter")
@_ffi_requires("buffer.count >= n && n >= 1 && n <= 128")
@_ffi_ensures("result <= buffer.count")
func boundedMixedIter(_ buffer: UnsafeBufferPointer<UInt8>, _ n: UInt64) -> UInt64
