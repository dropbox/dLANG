// hello_verified.swift
//
// A simple demonstration of tSwift formal verification.
// This function has a specification that the verifier PROVES correct.
//
// Run: tswift verify examples/hello_verified.swift --verbose

/// Returns the absolute value of an integer.
///
/// The @_requires precondition bounds x to prevent overflow in negation.
/// The @_ensures postcondition is PROVEN by the verifier.
@inline(never)
@_requires("x > -9223372036854775807")
@_ensures("result >= 0")
func absoluteValue(_ x: Int) -> Int {
    if x >= 0 {
        return x
    } else {
        return -x
    }
}

/// Returns true if n is positive.
///
/// Simple boolean function - specification is always verified.
@inline(never)
@_ensures("result == (n > 0)")
func isPositive(_ n: Int) -> Bool {
    return n > 0
}

/// Returns the maximum of two integers.
///
/// The postcondition is a tautology from the implementation.
@inline(never)
@_ensures("result >= a && result >= b")
func max(_ a: Int, _ b: Int) -> Int {
    if a >= b {
        return a
    } else {
        return b
    }
}

// Usage to prevent optimization removal
// The verifier checks these functions regardless of usage,
// but calling them ensures they remain in the compiled SIL.
_ = absoluteValue(42)
_ = isPositive(10)
_ = max(5, 3)
