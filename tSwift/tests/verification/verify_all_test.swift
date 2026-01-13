// tests/verification/verify_all_test.swift
//
// Test file for -verify-all-functions flag.
// Contains a mix of functions with and without specs.

// Function WITH specs - should be verified normally
@_requires("x > 0")
@_ensures("result > 0")
func withSpecs(_ x: Int) -> Int {
    return x * 2
}

// Function WITHOUT specs - should be tracked by -verify-all-functions
func withoutSpecs(_ x: Int) -> Int {
    return x + 1
}

// Another function WITHOUT specs
func anotherNoSpecs(_ a: Int, _ b: Int) -> Int {
    return a - b
}

// Trusted function - always skipped
@_trusted
func trustedFunc(_ x: Int) -> Int {
    return x
}
