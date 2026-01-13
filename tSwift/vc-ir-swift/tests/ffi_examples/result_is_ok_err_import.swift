// Swift imports for Result .is_ok()/.is_err() and unwrap() normalization FFI tests
// All should PASS verification - conditions translate correctly

@_ffi_import("result_is_ok_requires")
@_ffi_requires("res.isSuccess")
@_ffi_ensures("result > 0")
func resultIsOkRequires(_ res: UnsafeBufferPointer<UInt8>, _ value: Int32) -> Int32

@_ffi_import("result_is_err_requires")
@_ffi_requires("!res.isSuccess")
@_ffi_ensures("result == 0")
func resultIsErrRequires(_ res: UnsafeBufferPointer<UInt8>) -> Int32

@_ffi_import("result_unwrap_len_requires")
@_ffi_requires("res.isSuccess && res.value.count > 0")
@_ffi_ensures("result > 0")
func resultUnwrapLenRequires(_ res: UnsafeBufferPointer<UInt8>, _ value: Int32) -> Int32

@_ffi_import("result_not_is_err_requires")
@_ffi_requires("res.isSuccess")
@_ffi_ensures("result > 0")
func resultNotIsErrRequires(_ res: UnsafeBufferPointer<UInt8>, _ value: Int32) -> Int32

