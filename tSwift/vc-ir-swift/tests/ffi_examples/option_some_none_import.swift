// Swift imports for Option is_some()/is_none() FFI tests
// All should PASS verification - conditions translate correctly via normalization:
// - Rust: value.is_some() -> Swift equivalent: value != nil
// - Rust: value.is_none() -> Swift equivalent: value == nil

/// Import require_some with compatible nil-check precondition.
@_ffi_import("require_some")
@_ffi_requires("value != nil")
@_ffi_ensures("result >= 0")
func requireSome(_ value: Int32?) -> Int32

/// Import require_none with compatible nil-check precondition.
@_ffi_import("require_none")
@_ffi_requires("value == nil")
@_ffi_ensures("result == 0")
func requireNone(_ value: Int32?) -> Int32

