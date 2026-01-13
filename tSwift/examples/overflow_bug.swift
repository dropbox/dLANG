// overflow_bug.swift
//
// Demonstrates tSwift auto-VC finding a potential overflow bug.
// The function specification is correct, but the implementation
// can overflow for large inputs.
//
// Run: tswift verify examples/overflow_bug.swift --verbose

/// Doubles an integer.
///
/// The specification is correct: result equals x * 2
/// BUT: the verifier detects that x * 2 can overflow!
///
/// This is an AUTO-VC - the verifier automatically checks for
/// overflow without any annotation from the programmer.
@inline(never)
@_requires("x > 0")
@_ensures("result == x * 2")
func double(_ x: Int) -> Int {
    return x * 2  // Auto-VC: arithmetic overflow FAIL
}

/// Squares an integer.
///
/// Another example of auto-VC finding potential overflow.
@inline(never)
@_requires("x >= 0")
@_ensures("result == x * x")
func square(_ x: Int) -> Int {
    return x * x  // Auto-VC: arithmetic overflow FAIL
}

/// Adds two integers.
///
/// Even simple addition can overflow!
@inline(never)
@_ensures("result == a + b")
func add(_ a: Int, _ b: Int) -> Int {
    return a + b  // Auto-VC: arithmetic overflow FAIL
}

// Usage to prevent optimization removal
_ = double(10)
_ = square(5)
_ = add(1, 2)
