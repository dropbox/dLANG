// Test file demonstrating proper Hoare-logic verification semantics.
//
// These specs are designed to verify even WITHOUT function body analysis,
// because the precondition logically implies the postcondition.
//
// Run with: tswift-mock tests/verification/implication_test.swift --verify

// Tautology: result == result is always true
@_ensures("result == result")
func tautology(_ x: Int) -> Int {
    return x
}

// Logical implication: x > 0 implies x >= 0
@_requires("x > 0")
@_ensures("x >= 0")
func positiveIsNonnegative(_ x: Int) -> Int {
    return x
}

// Logical implication: x > 0 implies x > -1
@_requires("x > 0")
@_ensures("x > -1")
func positiveGreaterThanNegOne(_ x: Int) -> Int {
    return x
}

// Multiple requires conjoined: x > 0 AND y > 0 implies x > 0
// (Weakening - postcondition is weaker than precondition)
@_requires("x > 0")
@_requires("y > 0")
@_ensures("x > 0")
func weakening(x: Int, y: Int) -> Int {
    return x + y
}

// Sum of positives: x > 0 AND y > 0 implies x + y > 0
@_requires("x > 0")
@_requires("y > 0")
@_ensures("x + y > 0")
func sumPositive(x: Int, y: Int) -> Int {
    return x + y
}

// Trusted function (always verifies by skipping)
@_trusted
func trustedOp(_ x: Int) -> Int {
    return x * x
}
