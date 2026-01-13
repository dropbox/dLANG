// tests/verification/parser_integration_test.swift
// Test file for verifying parser integration into SIL verification pass

import Foundation

@_requires("x > 0")
@_requires("y >= 0 && y < 100")
@_ensures("result == x + y")
func addPositive(_ x: Int, _ y: Int) -> Int {
    return x + y
}

@_requires("n >= 0")
@_ensures("result >= 0")
func factorial(_ n: Int) -> Int {
    if n == 0 {
        return 1
    }
    return n * factorial(n - 1)
}

@_requires("divisor != 0")
@_ensures("result * divisor <= dividend && (result + 1) * divisor > dividend")
func safeDivide(dividend: Int, divisor: Int) -> Int {
    return dividend / divisor
}
