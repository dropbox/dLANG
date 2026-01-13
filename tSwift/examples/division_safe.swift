// division_safe.swift
//
// Demonstrates division by zero auto-VC detection.
//
// Run: tswift verify examples/division_safe.swift --verbose

/// Divides a by b without checking for zero.
///
/// The auto-VC detects that b could be zero.
@inline(never)
@_ensures("b != 0 ==> result == a / b")
func unsafeDivide(_ a: Int, _ b: Int) -> Int {
    return a / b  // Auto-VC: division by zero FAIL
}

/// Safe divide with explicit precondition.
///
/// The @_requires "b != 0" satisfies the auto-VC.
@inline(never)
@_requires("b != 0")
@_ensures("result == a / b")
func safeDivide(_ a: Int, _ b: Int) -> Int {
    return a / b  // Auto-VC: should pass with precondition
}

/// Modulo operation also needs non-zero divisor.
@inline(never)
@_ensures("b != 0 ==> result == a % b")
func unsafeMod(_ a: Int, _ b: Int) -> Int {
    return a % b  // Auto-VC: division by zero FAIL
}

// Usage to prevent optimization removal
_ = unsafeDivide(10, 2)
_ = safeDivide(10, 2)
_ = unsafeMod(10, 3)
