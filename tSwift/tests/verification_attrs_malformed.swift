// Test file for verification attribute diagnostics
// This tests that malformed specs produce actionable diagnostics

// Test 1: Missing argument
@_requires
func missingArg(x: Int) -> Int {
    return x
}

// Test 2: Wrong argument type (not a string)
@_requires(42)
func wrongArgType(x: Int) -> Int {
    return x
}

// Test 3: String interpolation (should be rejected)
@_requires("x > \(y)")
func interpolatedString(x: Int, y: Int) -> Int {
    return x
}

// Test 4: Empty string
@_requires("")
func emptyCondition(x: Int) -> Int {
    return x
}

// Test 5: Missing closing paren
@_requires("x > 0"
func missingCloseParen(x: Int) -> Int {
    return x
}

// Test 6: Applied to wrong decl type (import)
@_requires("true")
import Foundation
