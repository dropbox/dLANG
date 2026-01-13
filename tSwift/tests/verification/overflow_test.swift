// Tests for overflow verification
// This file tests automatic overflow detection in tSwift

// Function that can overflow - no precondition to bound inputs
// Should report: POTENTIAL OVERFLOW (unbounded inputs can overflow)
@_requires("true")
@_ensures("result == x + y")
func unsafeAdd(_ x: Int, _ y: Int) -> Int {
    return x + y
}

// Function with bounded inputs - should be safe
// If x and y are both bounded, their sum cannot overflow
@_requires("x >= 0 && x <= 1000000")
@_ensures("result == x + x")
func safeDouble(_ x: Int) -> Int {
    return x + x
}

// Multiplication can overflow easily
// Should report: POTENTIAL OVERFLOW
@_requires("true")
@_ensures("result == x * y")
func unsafeMul(_ x: Int, _ y: Int) -> Int {
    return x * y
}

// Bounded multiplication should be safe
@_requires("x >= 0 && x <= 1000 && y >= 0 && y <= 1000")
@_ensures("result == x * y")
func safeMul(_ x: Int, _ y: Int) -> Int {
    return x * y
}

// Subtraction can underflow
@_requires("true")
@_ensures("result == x - y")
func unsafeSub(_ x: Int, _ y: Int) -> Int {
    return x - y
}
