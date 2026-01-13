// else_if_test.swift - Tests for else-if chain verification
//
// Tests if/else-if/else chain translation to nested ite expressions.
// if c1 { return e1 } else if c2 { return e2 } else { return e3 }
// -> ite(c1, e1, ite(c2, e2, e3))

// ============================================================================
// BASIC ELSE-IF TESTS
// ============================================================================

// Clamp function - bounds a value between min and max
// This is the canonical example of needing else-if chains
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

// Classification function - categorizes integers
@_requires("true")
@_ensures("result == -1 || result == 0 || result == 1")
func sign3Way(_ x: Int) -> Int {
    if x < 0 {
        return -1
    } else if x == 0 {
        return 0
    } else {
        return 1
    }
}

// Grade classification - maps score to letter grade index
@_requires("score >= 0")
@_ensures("result >= 0")
@_ensures("result <= 4")
func gradeIndex(_ score: Int) -> Int {
    if score >= 90 {
        return 4
    } else if score >= 80 {
        return 3
    } else if score >= 70 {
        return 2
    } else if score >= 60 {
        return 1
    } else {
        return 0
    }
}

// ============================================================================
// ELSE-IF WITH COMPUTED RESULTS
// ============================================================================

// Tiered multiplier - different rates for different ranges
@_requires("x >= 0")
@_ensures("result >= 0")
func tieredMultiplier(_ x: Int) -> Int {
    if x < 10 {
        return x * 1
    } else if x < 100 {
        return x * 2
    } else {
        return x * 3
    }
}

// ============================================================================
// INTENTIONAL FAILURE TESTS
// ============================================================================

// This should FAIL - clamp doesn't always return x
// When x < minVal, it returns minVal, not x
@_requires("minVal <= maxVal")
@_ensures("result == x")
func badClampSpec(_ x: Int, minVal: Int, maxVal: Int) -> Int {
    if x < minVal {
        return minVal
    } else if x > maxVal {
        return maxVal
    } else {
        return x
    }
}

// ============================================================================
// TRUSTED FUNCTION (skips verification)
// ============================================================================

@_trusted
@_requires("true")
@_ensures("result == 42")
func trustedElseIf(_ x: Int) -> Int {
    if x < 0 {
        return -1
    } else if x == 0 {
        return 0
    } else {
        return 1
    }
}
