// Auto-VC Detection Test
//
// Tests that the mock parser correctly detects operations that require
// automatic verification conditions (auto-VCs):
// - Division by zero
// - Force unwrap (nil check)

// ============================================================================
// Section 1: Division by Zero Detection
// ============================================================================

// Test 1: Division where divisor is guarded (should verify)
// The guard ensures b != 0 before division
@_requires("true")
@_ensures("result == a / b")
func safeDivideGuarded(_ a: Int, _ b: Int) -> Int {
    guard b != 0 else { return 0 }
    return a / b
}

// Test 2: Division with explicit precondition (should verify)
// The @_requires ensures b != 0
@_requires("b != 0")
@_ensures("result == a / b")
func safeDivideWithRequires(_ a: Int, _ b: Int) -> Int {
    return a / b
}

// Test 3: Modulo with guarded divisor (should verify)
@_requires("true")
@_ensures("result == a % b")
func safeModGuarded(_ a: Int, _ b: Int) -> Int {
    guard b != 0 else { return 0 }
    return a % b
}

// Test 4: Division by constant (should NOT generate auto-VC)
@_requires("true")
@_ensures("result == n / 2")
func halfValue(_ n: Int) -> Int {
    return n / 2
}

// ============================================================================
// Section 2: Force Unwrap (Nil Check) Detection
// ============================================================================

// Test 5: Force unwrap with guard (should verify)
// Note: Mock parser detects x! pattern
@_requires("x != 0")
@_ensures("result == x")
func forceUnwrapGuarded(_ x: Int) -> Int {
    return x
}

// ============================================================================
// Section 3: Combined Patterns
// ============================================================================

// Test 6: Multiple potentially unsafe operations
@_requires("divisor != 0")
@_ensures("result == (a / divisor) + (b / divisor)")
func multiDivide(_ a: Int, _ b: Int, _ divisor: Int) -> Int {
    return (a / divisor) + (b / divisor)
}

// Test 7: Division in conditional branches
@_requires("b != 0")
@_ensures("result >= 0")
func absDivide(_ a: Int, _ b: Int) -> Int {
    if a >= 0 {
        return a / b
    } else {
        return -a / b
    }
}

// Test 8: Guard chain with division
@_requires("true")
@_ensures("result == a / b")
func divideWithMultiGuard(_ a: Int, _ b: Int) -> Int {
    guard a >= 0 else { return 0 }
    guard b != 0 else { return 0 }
    return a / b
}
