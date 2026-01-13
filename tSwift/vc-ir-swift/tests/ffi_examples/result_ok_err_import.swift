// Swift imports for Result .ok()/.err() FFI tests
// All should PASS verification - conditions translate correctly
// Swift uses .isSuccess for Result success checking which matches the normalization
// Note: Uses byte buffers for type compatibility; tests .ok()/.err() pattern normalization

/// Import process_after_success with compatible precondition
/// Swift uses .isSuccess which is equivalent to .ok().is_some()
@_ffi_import("process_after_success")
@_ffi_requires("prevResult.isSuccess")
@_ffi_ensures("result > 0")
func processAfterSuccess(_ prevResult: UnsafeBufferPointer<UInt8>, _ data: Int32) -> Int32

/// Import handle_error with compatible precondition
/// Swift uses !.isSuccess which is equivalent to .err().is_some()
@_ffi_import("handle_error")
@_ffi_requires("!res.isSuccess")
@_ffi_ensures("result >= 0")
func handleError(_ res: UnsafeBufferPointer<UInt8>) -> Int32

/// Import both_succeeded with combined conditions
/// Swift uses .isSuccess for both success checks
@_ffi_import("both_succeeded")
@_ffi_requires("first.isSuccess && second.isSuccess")
@_ffi_ensures("result == 1")
func bothSucceeded(_ first: UnsafeBufferPointer<UInt8>, _ second: UnsafeBufferPointer<UInt8>) -> Int32

/// Import negated_check with equivalent Swift condition
/// !res.ok().is_none() normalizes to res.isSuccess
@_ffi_import("negated_check")
@_ffi_requires("res.isSuccess")
@_ffi_ensures("result > 0")
func negatedCheck(_ res: UnsafeBufferPointer<UInt8>, _ value: Int32) -> Int32
