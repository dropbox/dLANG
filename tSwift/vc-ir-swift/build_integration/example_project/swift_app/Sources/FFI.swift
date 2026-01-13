// FFI.swift - Swift declarations importing Rust functions
//
// These declarations must match the Rust FFI exports.
// tswift-ffi-verify checks that specifications are compatible.

import Foundation

/// Compute factorial of n.
/// - Parameter n: Non-negative integer (0-20)
/// - Returns: n! (factorial of n)
@_ffi_import("factorial")
@_ffi_requires("n >= 0 && n <= 20")
@_ffi_ensures("result >= 1")
func factorial(_ n: Int64) -> Int64

/// Safely divide two integers.
/// - Parameters:
///   - dividend: The number to divide
///   - divisor: The number to divide by (must not be zero)
/// - Returns: dividend / divisor
@_ffi_import("safe_divide")
@_ffi_requires("divisor != 0")
@_ffi_ensures("true")
func safeDivide(_ dividend: Int64, _ divisor: Int64) -> Int64

/// Clamp a value to a range.
/// - Parameters:
///   - value: The value to clamp
///   - min: Minimum bound
///   - max: Maximum bound (must be >= min)
/// - Returns: value clamped to [min, max]
@_ffi_import("clamp")
@_ffi_requires("min <= max")
@_ffi_ensures("result >= min && result <= max")
func clamp(_ value: Int64, min: Int64, max: Int64) -> Int64
