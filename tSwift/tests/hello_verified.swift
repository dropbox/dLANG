// Hello, Verified Swift!
// Simple test cases to verify E2E verification pipeline
//
// Run with: tswift-mock tests/hello_verified.swift --verify
//
// Expected results:
//   identity:      VERIFIED
//   increment:     VERIFIED
//   clampPositive: VERIFIED
//   safeDecrement: VERIFIED
//   shouldFail:    FAILED (counterexample: x=0)
//   trustedFunc:   VERIFIED (trusted, skipped)
//   abs:           VERIFIED (negation transformed to x+y=0)
//   max:           VERIFIED (both ensures)
//   min:           VERIFIED (both ensures)
//
// Total: 9 VERIFIED, 1 FAILED (expected)

// VERIFIED: Simple tautology
@_requires("x >= 0")
@_ensures("x >= 0")
func identity(_ x: Int) -> Int {
    return x
}

// VERIFIED: Simple arithmetic with precondition
@_requires("x > 0")
@_ensures("result > 0")
func increment(_ x: Int) -> Int {
    return x + 1
}

// VERIFIED: Clamp to non-negative (if-else)
@_ensures("result >= 0")
func clampPositive(_ x: Int) -> Int {
    if x >= 0 {
        return x
    } else {
        return 0
    }
}

// VERIFIED: Safe decrement with guard
@_ensures("result >= 0")
func safeDecrement(_ x: Int) -> Int {
    guard x > 0 else { return 0 }
    return x - 1
}

// EXPECTED FAIL: This should fail (result could be 0 when x = 0)
@_requires("x >= 0")
@_ensures("result > 0")
func shouldFail(_ x: Int) -> Int {
    return x
}

// TRUSTED: Skips verification
@_trusted
@_ensures("result == 42")
func trustedFunc(_ x: Int) -> Int {
    return 42
}

// VERIFIED: abs uses negation but our transformation handles it
// The transformation converts `result = -x` to `result + x = 0`
// and `NOT(x >= 0)` to `x + 1 <= 0`, avoiding Z4's LIA limitations
@_ensures("result >= 0")
func abs(_ x: Int) -> Int {
    if x >= 0 {
        return x
    } else {
        return -x
    }
}

// VERIFIED: max of two values
@_ensures("result >= x")
@_ensures("result >= y")
func max(_ x: Int, _ y: Int) -> Int {
    if x >= y {
        return x
    } else {
        return y
    }
}

// VERIFIED: min of two values
@_ensures("result <= x")
@_ensures("result <= y")
func min(_ x: Int, _ y: Int) -> Int {
    if x <= y {
        return x
    } else {
        return y
    }
}
