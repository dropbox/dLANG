// weak_import_fail.swift
//
// Example of INCOMPATIBLE FFI imports that FAIL verification.
// This demonstrates how tSwift catches unsafe FFI boundaries.
//
// Run verification (expect FAILURE):
//   tswift-ffi-verify --swift weak_import_fail.swift --rust secure_buffer.rs --z4 --verbose
//
// Expected: 2 FAIL, 1 OK

/// FAIL: Weak precondition does NOT imply Rust's requirement.
///
/// Swift says: size > -100 (allows negative sizes!)
/// Rust needs: size > 0 && size <= 1073741824
///
/// Counterexample: size = -50 satisfies Swift but violates Rust.
@_ffi_import("secure_alloc")
@_ffi_requires("size > -100")  // TOO WEAK!
@_ffi_ensures("result >= 0")
func unsafeAlloc(_ size: Int64) -> Int64

/// FAIL: Weak precondition allows zero which Rust rejects.
///
/// Swift says: input >= -10 (allows negative and zero!)
/// Rust needs: input >= 0
///
/// Counterexample: input = -5 satisfies Swift but violates Rust.
@_ffi_import("compute_hash")
@_ffi_requires("input >= -10")  // TOO WEAK!
@_ffi_ensures("result >= 0")
func unsafeHash(_ input: Int64) -> Int64

/// OK: This one is correct for demonstration.
@_ffi_import("validate_size")
@_ffi_requires("size >= 8")
@_ffi_ensures("result == 0 || result == 1")
func validateSizeOK(_ size: Int64) -> Int32

// MARK: - Why Weak Preconditions Are Dangerous
//
// When Swift has a WEAKER precondition than Rust:
// - Swift allows some inputs (e.g., size = -50)
// - Rust's implementation assumes those inputs can't happen
// - Calling Rust with invalid inputs = UNDEFINED BEHAVIOR
//
// The Z4 solver finds counterexamples proving the implication fails:
//   Swift_requires => Rust_requires  is FALSE
//
// This catches the bug at compile time, not runtime!
