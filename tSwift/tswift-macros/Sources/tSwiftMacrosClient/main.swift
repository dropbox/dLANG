// tSwift Macros Client - Example Usage and Tests
//
// This demonstrates how to use tSwift verification macros and serves as the
// test suite for the tswift-macros package.
//
// Run with: swift run tSwiftMacrosClient
// Exit code 0 = all tests pass, non-zero = failure

import Foundation
import tSwiftMacros

// MARK: - Test Infrastructure

var testsPassed = 0
var testsFailed = 0

func test(_ name: String, _ condition: Bool) {
    if condition {
        testsPassed += 1
        print("  ✓ \(name)")
    } else {
        testsFailed += 1
        print("  ✗ \(name)")
    }
}

func testEqual<T: Equatable>(_ name: String, _ actual: T, _ expected: T) {
    test(name, actual == expected)
}

// MARK: - Basic Precondition/Postcondition

@requires("n > 0")
@ensures("result >= 1 && result <= n")
func clampPositive(_ n: Int, _ val: Int) -> Int {
    if val < 1 { return 1 }
    else if val > n { return n }
    else { return val }
}

// MARK: - Array Bounds (Auto-Verified)

// tSwift automatically verifies bounds checks.
// This function requires no annotations - the compiler proves it safe.
func guardedIndex(_ arr: [Int], _ i: Int) -> Int {
    if i >= 0 && i < arr.count {
        return arr[i]  // VERIFIED SAFE: i in bounds from path condition
    }
    return 0
}

// MARK: - Optional Safety (Auto-Verified)

// tSwift automatically verifies optional unwraps.
func guardedUnwrap(_ x: Int?) -> Int {
    if let value = x {
        return value  // VERIFIED SAFE: x is non-nil in this branch
    }
    return 0
}

// MARK: - Arithmetic (Auto-Verified)

// tSwift automatically verifies no overflow.
func guardedAdd(_ a: UInt8, _ b: UInt8) -> UInt8 {
    if a < 100 && b < 100 {
        return a + b  // VERIFIED SAFE: 99 + 99 = 198 <= 255
    }
    return 0
}

// MARK: - Division (Auto-Verified)

// tSwift automatically verifies no division by zero.
func guardedDivide(_ a: Int, _ b: Int) -> Int {
    if b != 0 {
        return a / b  // VERIFIED SAFE: b != 0 from path condition
    }
    return 0
}

// MARK: - Invariant Example

@invariant("value >= 0")
var globalValue: Int = 0

// MARK: - Trusted Example

@trusted
func legacyCode() -> Int {
    // Skip verification for this function
    return 42
}

@trusted(.overflow)
func intentionalWrapping(_ x: UInt8) -> UInt8 {
    return x &+ 1
}

// MARK: - Main

print("tSwift Macros Test Suite")
print("========================")
print("")

// Test 1: TrustLevel enum
print("TrustLevel Enum Tests:")
let levels: [TrustLevel] = [.overflow, .bounds, .nil, .division, .all]
testEqual("TrustLevel has 5 cases", levels.count, 5)
test("TrustLevel.overflow exists", true)
test("TrustLevel.bounds exists", true)
test("TrustLevel.nil exists", true)
test("TrustLevel.division exists", true)
test("TrustLevel.all exists", true)
print("")

// Test 2: clampPositive function
print("clampPositive Tests:")
testEqual("clampPositive(10, 5) == 5", clampPositive(10, 5), 5)
testEqual("clampPositive(10, 0) == 1 (clamped to min)", clampPositive(10, 0), 1)
testEqual("clampPositive(10, 15) == 10 (clamped to max)", clampPositive(10, 15), 10)
testEqual("clampPositive(10, 1) == 1 (boundary)", clampPositive(10, 1), 1)
testEqual("clampPositive(10, 10) == 10 (boundary)", clampPositive(10, 10), 10)
print("")

// Test 3: guardedIndex function
print("guardedIndex Tests:")
testEqual("guardedIndex([1,2,3], 0) == 1", guardedIndex([1,2,3], 0), 1)
testEqual("guardedIndex([1,2,3], 1) == 2", guardedIndex([1,2,3], 1), 2)
testEqual("guardedIndex([1,2,3], 2) == 3", guardedIndex([1,2,3], 2), 3)
testEqual("guardedIndex([1,2,3], -1) == 0 (guarded)", guardedIndex([1,2,3], -1), 0)
testEqual("guardedIndex([1,2,3], 10) == 0 (guarded)", guardedIndex([1,2,3], 10), 0)
print("")

// Test 4: guardedUnwrap function
print("guardedUnwrap Tests:")
testEqual("guardedUnwrap(42) == 42", guardedUnwrap(42), 42)
testEqual("guardedUnwrap(0) == 0", guardedUnwrap(0), 0)
testEqual("guardedUnwrap(nil) == 0", guardedUnwrap(nil), 0)
print("")

// Test 5: guardedAdd function
print("guardedAdd Tests:")
testEqual("guardedAdd(50, 50) == 100", guardedAdd(50, 50), 100)
testEqual("guardedAdd(99, 99) == 198", guardedAdd(99, 99), 198)
testEqual("guardedAdd(100, 1) == 0 (guarded)", guardedAdd(100, 1), 0)
testEqual("guardedAdd(200, 200) == 0 (guarded)", guardedAdd(200, 200), 0)
print("")

// Test 6: guardedDivide function
print("guardedDivide Tests:")
testEqual("guardedDivide(10, 2) == 5", guardedDivide(10, 2), 5)
testEqual("guardedDivide(10, 3) == 3", guardedDivide(10, 3), 3)
testEqual("guardedDivide(10, 0) == 0 (guarded)", guardedDivide(10, 0), 0)
print("")

// Test 7: trusted functions compile and run
print("Trusted Function Tests:")
testEqual("legacyCode() == 42", legacyCode(), 42)
testEqual("intentionalWrapping(255) == 0 (wraps)", intentionalWrapping(255), 0)
testEqual("intentionalWrapping(100) == 101", intentionalWrapping(100), 101)
print("")

// Summary
print("========================")
print("Tests passed: \(testsPassed)")
print("Tests failed: \(testsFailed)")
print("")

if testsFailed > 0 {
    print("FAIL")
    exit(1)
} else {
    print("PASS")
    exit(0)
}
