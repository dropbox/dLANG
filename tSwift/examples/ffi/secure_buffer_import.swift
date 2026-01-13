// secure_buffer_import.swift
//
// Swift FFI imports with formal verification specifications.
// The verifier PROVES Swift's contracts are compatible with Rust's contracts.
//
// Run verification:
//   tswift-ffi-verify --swift secure_buffer_import.swift --rust secure_buffer.rs --z4 --verbose
//
// Expected output: All functions pass verification because:
// - Swift preconditions IMPLY Rust preconditions (stronger or equal)
// - Rust postconditions IMPLY Swift expectations (equal or stronger)

// MARK: - Compatible Imports (All should PASS)

/// Allocate a secure buffer.
///
/// Swift uses STRONGER precondition (size >= 16) which implies Rust's (size > 0).
/// This is safe because Swift callers are more restricted.
@_ffi_import("secure_alloc")
@_ffi_requires("size >= 16 && size <= 1073741824")  // Stronger: minimum 16 bytes
@_ffi_ensures("result >= 0")
func secureAlloc(_ size: Int64) -> Int64

/// Compute hash of input value.
///
/// Swift uses STRONGER precondition (input > 0) which implies Rust's (input >= 0).
@_ffi_import("compute_hash")
@_ffi_requires("input > 0")  // Stronger: strictly positive
@_ffi_ensures("result >= 0")
func computeHash(_ input: Int64) -> Int64

/// Validate buffer size.
///
/// Swift requires size >= 8, which implies Rust's size > 0.
@_ffi_import("validate_size")
@_ffi_requires("size >= 8")  // Stronger: minimum 8
@_ffi_ensures("result == 0 || result == 1")
func validateSize(_ size: Int64) -> Int32

/// Safe increment with overflow protection.
///
/// Swift uses an even stricter bound.
@_ffi_import("safe_increment")
@_ffi_requires("value >= 0 && value < 9223372036854775800")  // Stronger bound
@_ffi_ensures("result == value + 1")
func safeIncrement(_ value: Int64) -> Int64

/// Absolute difference between values.
///
/// Swift requires strictly positive values (implies Rust's >= 0).
@_ffi_import("abs_diff")
@_ffi_requires("a > 0 && b > 0")  // Stronger: strictly positive
@_ffi_ensures("result >= 0")
func absDiff(_ a: Int64, _ b: Int64) -> Int64

// MARK: - How Verification Works
//
// For each FFI function, tswift-ffi-verify checks:
//
// 1. PRECONDITION SAFETY:
//    Does caller's requires IMPLY callee's requires?
//    (Swift's constraints must be at least as strong as Rust's)
//
//    Example: secure_alloc
//    - Swift: size >= 16 && size <= 1073741824
//    - Rust:  size > 0 && size <= 1073741824
//    - Check: (size >= 16 && size <= 1073741824) => (size > 0 && size <= 1073741824)
//    - Result: PROVEN (16 >= 1, so size > 0 is implied)
//
// 2. POSTCONDITION VALIDITY:
//    Does callee's ensures IMPLY caller's expects?
//    (Rust's guarantees must be at least as strong as Swift expects)
//
// 3. TYPE COMPATIBILITY:
//    Do the types match across the FFI boundary?
//
// When all checks pass, the FFI boundary is formally verified safe.
