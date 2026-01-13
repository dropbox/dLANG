// tests/verification/control_flow_test.swift
//
// Test file for control flow (if/else) in function body verification.
// With path-sensitive analysis, these should verify correctly using Ite constraints.
//
// For functions with if/else:
//   if cond { return then_expr } else { return else_expr }
// The body constraint becomes:
//   result == ite(cond, then_expr, else_expr)
//
// Verification formula:
//   (requires AND result == ite(cond, then, else)) => ensures

// ============================================================================
// Absolute value - classic if/else pattern
// ============================================================================

// Should verify: if x >= 0 then result = x >= 0; if x < 0 then result = -x > 0
@_requires("true")
@_ensures("result >= 0")
func abs(_ x: Int) -> Int {
    if x >= 0 {
        return x
    } else {
        return -x
    }
}

// ============================================================================
// Max function - returns larger of two values
// ============================================================================

// Should verify: result is always >= both inputs
@_requires("true")
@_ensures("result >= x")
@_ensures("result >= y")
func max(_ x: Int, _ y: Int) -> Int {
    if x > y {
        return x
    } else {
        return y
    }
}

// Should verify: result is always equal to one of the inputs
@_requires("true")
@_ensures("result == x || result == y")
func maxEquality(_ x: Int, _ y: Int) -> Int {
    if x > y {
        return x
    } else {
        return y
    }
}

// ============================================================================
// Min function - returns smaller of two values
// ============================================================================

@_requires("true")
@_ensures("result <= x")
@_ensures("result <= y")
func min(_ x: Int, _ y: Int) -> Int {
    if x < y {
        return x
    } else {
        return y
    }
}

// ============================================================================
// Sign function - returns 1 for positive, -1 for negative/zero
// ============================================================================

@_requires("true")
@_ensures("result == 1 || result == -1")
func sign(_ x: Int) -> Int {
    if x > 0 {
        return 1
    } else {
        return -1
    }
}

// ============================================================================
// Clamp function - bounds value between min and max
// ============================================================================

// Now supported! Else-if chains translate to nested Ite expressions.
@_requires("minVal <= maxVal")
@_ensures("result >= minVal")
@_ensures("result <= maxVal")
func clamp(_ x: Int, minVal: Int, maxVal: Int) -> Int {
    if x < minVal {
        return minVal
    } else if x > maxVal {
        return maxVal
    } else {
        return x
    }
}

// ============================================================================
// Nested if/else
// ============================================================================

@_requires("true")
@_ensures("result >= 1 && result <= 3")
func nestedIf(_ x: Int, _ y: Int) -> Int {
    if x > 0 {
        if y > 0 {
            return 1
        } else {
            return 2
        }
    } else {
        return 3
    }
}

// ============================================================================
// Single-line if/else syntax
// ============================================================================

@_requires("true")
@_ensures("result >= 0")
func absSingleLine(_ x: Int) -> Int {
    if x >= 0 { return x } else { return -x }
}

// ============================================================================
// Intentionally wrong specs - should FAIL
// ============================================================================

// Should FAIL: abs can return positive values when x >= 0
@_requires("true")
@_ensures("result < 0")  // Wrong! abs returns non-negative
func badAbsSpec(_ x: Int) -> Int {
    if x >= 0 {
        return x
    } else {
        return -x
    }
}

// ============================================================================
// Trusted function with control flow
// ============================================================================

@_trusted
@_requires("true")
@_ensures("result > 1000")  // Would fail without @_trusted
func trustedMax(_ x: Int, _ y: Int) -> Int {
    if x > y {
        return x
    } else {
        return y
    }
}
