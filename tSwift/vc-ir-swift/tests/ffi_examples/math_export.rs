// Example Rust FFI exports for tswift-ffi-verify testing

/// Safe increment that requires positive input
#[ffi_export]
#[ffi_requires("x > 0")]
#[ffi_ensures("result >= x")]
pub fn increment(x: i32) -> i32 {
    x + 1
}

/// Safe multiply with positive inputs
#[ffi_export]
#[ffi_requires("a > 0 && b > 0")]
#[ffi_ensures("result > 0")]
pub fn safe_multiply(a: i64, b: i64) -> i64 {
    a * b
}

/// Trusted unsafe operation (skip verification)
#[ffi_export]
#[ffi_trusted]
pub unsafe fn raw_pointer_op(ptr: *mut u8) {
    // Unsafe pointer operations
}

/// Function with result type
#[ffi_export]
#[ffi_ensures("result >= 0")]
pub fn get_size(buffer: &[u8]) -> i32 {
    buffer.len() as i32
}
