// switch_test.swift - Tests for switch statement verification
//
// Tests switch statement translation to nested ite expressions.
// switch x { case 0: return e0; case 1: return e1; default: return ed }
// -> ite(x == 0, e0, ite(x == 1, e1, ed))

// ============================================================================
// BASIC SWITCH TESTS
// ============================================================================

// Simple switch with default - should verify
@_requires("true")
@_ensures("result == 0 || result == 1 || result == -1")
func signClass(_ x: Int) -> Int {
    switch x {
    case 0: return 0
    case 1: return 1
    default: return -1
    }
}

// Switch with identity cases - should verify
@_requires("x == 0 || x == 1")
@_ensures("result == x")
func boolIdentity(_ x: Int) -> Int {
    switch x {
    case 0: return 0
    case 1: return 1
    default: return 0
    }
}

// Switch returning constants - should verify
@_requires("true")
@_ensures("result >= 0")
func dayOfWeek(_ x: Int) -> Int {
    switch x {
    case 0: return 1
    case 1: return 2
    case 2: return 3
    default: return 0
    }
}

// ============================================================================
// SWITCH WITH ARITHMETIC
// ============================================================================

// Switch with computed return values - should verify
@_requires("x >= 0")
@_ensures("result >= 0")
func doubleOrTriple(_ x: Int) -> Int {
    switch x {
    case 0: return 0
    case 1: return x * 2
    default: return x * 3
    }
}

// Multi-line switch - should verify
@_requires("true")
@_ensures("x == 0 || result > 0")
func multilineSwitch(_ x: Int) -> Int {
    switch x {
    case 0:
        return 0
    case 1:
        return 10
    default:
        return 100
    }
}

// ============================================================================
// SWITCH WITH NEGATIVE PATTERNS
// ============================================================================

// Switch with negative case - should verify
@_requires("true")
@_ensures("result == 0 || result == 1 || result == 2")
func signToIndex(_ x: Int) -> Int {
    switch x {
    case -1: return 0
    case 0: return 1
    default: return 2
    }
}

// ============================================================================
// SWITCH WITH RANGE PATTERNS
// ============================================================================

// Switch with half-open ranges - should verify
@_requires("x >= 0 && x < 20")
@_ensures("result == 0 || result == 1")
func rangeBucketHalfOpen(_ x: Int) -> Int {
    switch x {
    case 0..<10: return 0
    case 10..<20: return 1
    default: return 0
    }
}

// Switch with closed range - should verify
@_requires("true")
@_ensures("result == 0 || result == 1")
func rangeBucketClosed(_ x: Int) -> Int {
    switch x {
    case -2...2: return 0
    default: return 1
    }
}

// ============================================================================
// COMMA-SEPARATED PATTERNS
// ============================================================================

// Switch with comma-separated patterns - should verify
@_requires("true")
@_ensures("result == 0 || result == 1")
func isSmall(_ x: Int) -> Int {
    switch x {
    case 0, 1, 2: return 1
    default: return 0
    }
}

// Comma-separated with multiple groups - should verify
@_requires("true")
@_ensures("result >= 0 && result <= 2")
func classifyDigit(_ x: Int) -> Int {
    switch x {
    case 0, 1: return 0
    case 2, 3, 4: return 1
    default: return 2
    }
}

// ============================================================================
// WILDCARD PATTERNS
// ============================================================================

// Switch with wildcard default - should verify
@_requires("true")
@_ensures("result == 0 || result == 1 || result == 2")
func wildcardDefault(_ x: Int) -> Int {
    switch x {
    case 0: return 0
    case 1: return 1
    case _: return 2
    }
}

// ============================================================================
// BINDING PATTERNS
// ============================================================================

// Switch with let binding (always matches like default) - should verify
@_requires("true")
@_ensures("result == 0 || result == 1 || result == 2")
func bindingDefault(_ x: Int) -> Int {
    switch x {
    case 0: return 0
    case 1: return 1
    case let n: return 2
    }
}

// ============================================================================
// INTENTIONAL FAILURE TESTS
// ============================================================================

// This should FAIL - wrong ensures clause
// switch x { case 0: return 0; default: return 1 }
// But ensures claims result >= 1 (false when x == 0)
@_requires("true")
@_ensures("result >= 1")
func badSwitchSpec(_ x: Int) -> Int {
    switch x {
    case 0: return 0
    default: return 1
    }
}

// ============================================================================
// TRUSTED FUNCTION (skips verification)
// ============================================================================

@_trusted
@_requires("true")
@_ensures("result == 42")
func trustedSwitch(_ x: Int) -> Int {
    switch x {
    case 0: return 0
    default: return 1
    }
}
