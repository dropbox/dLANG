// tests/verification/function_body_test.swift
//
// Test file for function body encoding in verification.
// With function semantics, these should verify correctly.
//
// Previous state (before #15):
//   @_requires("x > 0") @_ensures("result > 0")
//   func double(x) = x * 2
//   -> SMT: (x > 0) => (result > 0)
//   -> sat (counterexample found, e.g. x=1, result=0)
//   -> FAILED
//
// Current state (with function semantics):
//   -> SMT: (x > 0) AND (result = x * 2) => (result > 0)
//   -> unsat (postcondition is provable)
//   -> VERIFIED

// Simple doubling - should verify
@_requires("x > 0")
@_ensures("result > 0")
func positiveDouble(_ x: Int) -> Int {
    return x * 2
}

// Identity function - should verify
@_requires("x > 0")
@_ensures("result == x")
func identity(_ x: Int) -> Int {
    return x
}

// Addition - should verify
@_requires("x >= 0")
@_requires("y >= 0")
@_ensures("result >= x")
@_ensures("result >= y")
func add(_ x: Int, _ y: Int) -> Int {
    return x + y
}

// Subtraction - should verify
@_requires("x > y")
@_ensures("result > 0")
func subtract(_ x: Int, _ y: Int) -> Int {
    return x - y
}

// This should FAIL verification (intentionally wrong spec)
@_requires("x > 0")
@_ensures("result < 0")  // Wrong! x * 2 is positive if x > 0
func badSpec(_ x: Int) -> Int {
    return x * 2
}

// Trusted function - should be skipped
@_trusted
@_requires("x > 0")
@_ensures("result > 1000")  // Would fail without @_trusted
func trustedUnsafe(_ x: Int) -> Int {
    return x  // Obviously doesn't satisfy result > 1000
}
