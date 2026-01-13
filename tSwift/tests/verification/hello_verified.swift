// Hello, Verified Swift!
//
// This file demonstrates tSwift verification using the mock parser.
// Run with: tswift-mock tests/verification/hello_verified.swift --verify

// Simple function with precondition and postcondition
// Bounded to prevent overflow: x * 2 fits in Int64 when x <= 4611686018427387903
@_requires("x > 0 && x <= 4611686018427387903")
@_ensures("result >= x")
func double(_ x: Int) -> Int {
    return x * 2
}

// Function with multiple preconditions
// Bounded to prevent overflow: a + b fits in Int64 when both are bounded
@_requires("a >= 0 && a <= 4611686018427387903")
@_requires("b >= 0 && b <= 4611686018427387903")
@_ensures("result >= 0")
func add(a: Int, b: Int) -> Int {
    return a + b
}

// Function with boolean parameter
@_requires("flag || x > 0")
@_ensures("result > 0")
func conditionalIncrement(flag: Bool, x: Int) -> Int {
    if flag {
        return 1
    }
    return x
}

// Trusted function (skips verification)
@_trusted
func unsafePointerOp(_ ptr: UnsafePointer<Int>) -> Int {
    return ptr.pointee
}

// Function with tautology (always verifies)
@_ensures("result == result")
func identity(_ x: Int) -> Int {
    return x
}

// Function that should fail verification (for testing)
// Uncomment to test failure case:
// @_requires("x > 0")
// @_ensures("result > x")  // This is false for x=1 since 1*2=2 is not > 1 (wait, 2>1)
// func mightFail(_ x: Int) -> Int {
//     return x * 2
// }
