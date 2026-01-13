// switch_auto_vc_test.swift
// Test switch case path conditions with auto-VC detection
// Auto-VCs inside switch cases should inherit the case pattern condition

// =============================================================================
// SECTION 1: Division in case branch (should verify with case condition)
// =============================================================================

// Division inside case x != 0 should verify (path condition makes x != 0)
@_requires("true")
@_ensures("result == a / x")
func divideInCaseBranch(a: Int, x: Int) -> Int {
    switch x {
    case 1, 2, 3, 4, 5:
        return a / x  // auto-VC path condition: x == 1 || x == 2 || ... -> x != 0 -> VERIFIED
    default:
        return 0
    }
}

// Division inside case with explicit non-zero pattern
@_requires("true")
@_ensures("result >= 0")
func divideInCasePositive(a: Int, b: Int) -> Int {
    switch b {
    case 1:
        return a / b  // auto-VC path condition: b == 1 -> b != 0 -> VERIFIED
    case 2:
        return a / b  // auto-VC path condition: b == 2 -> b != 0 -> VERIFIED
    default:
        return 0
    }
}

// =============================================================================
// SECTION 2: Division in default branch (should verify with negated cases)
// =============================================================================

// Division in default with @_requires for b != 0
// Since default is !(b == 0), division should verify
@_requires("b >= 0")
@_ensures("result >= 0")
func divideInDefault(a: Int, b: Int) -> Int {
    switch b {
    case 0:
        return 0  // b == 0 case handled
    default:
        return a / b  // auto-VC path condition: !(b == 0) -> b != 0 -> VERIFIED
    }
}

// =============================================================================
// SECTION 3: Switch with range patterns
// =============================================================================

// Division inside range case (1..<100)
// Path condition: b >= 1 && b < 100, which implies b != 0
@_requires("true")
@_ensures("result >= 0")
func divideInRangeCase(a: Int, b: Int) -> Int {
    switch b {
    case 1..<100:
        return a / b  // auto-VC path condition: b >= 1 && b < 100 -> VERIFIED
    default:
        return 0
    }
}

// =============================================================================
// SECTION 4: Guard + switch combined
// =============================================================================

// Guard plus switch should combine path conditions
@_requires("true")
@_ensures("result > 0")
func divideWithGuardAndSwitch(a: Int, b: Int) -> Int {
    guard a > 0 else { return 0 }
    switch b {
    case 1:
        return a / b  // auto-VC path condition: a > 0 AND b == 1 -> VERIFIED
    case 2:
        return a / b  // auto-VC path condition: a > 0 AND b == 2 -> VERIFIED
    default:
        return 0
    }
}

// =============================================================================
// SECTION 5: Nested switch
// =============================================================================

// Nested switch should have combined path conditions from both levels
@_requires("true")
@_ensures("result >= 0")
func divideInNestedSwitch(a: Int, b: Int, c: Int) -> Int {
    switch b {
    case 1:
        switch c {
        case 2:
            return a / b  // auto-VC path condition: b == 1 AND c == 2 -> b != 0 -> VERIFIED
        default:
            return 0
        }
    default:
        return 0
    }
}

// =============================================================================
// SECTION 6: Division after switch closes (no path condition)
// =============================================================================

// Division outside switch should NOT have path condition (needs @_requires)
@_requires("b != 0")
@_ensures("result == a / b")
func divideAfterSwitchCloses(a: Int, b: Int) -> Int {
    switch a {
    case 0:
        return 0
    default:
        let _ = a + 1
    }
    return a / b  // auto-VC has no path condition from switch; needs @_requires
}

// =============================================================================
// SECTION 7: Switch with comma patterns (OR conditions)
// =============================================================================

// Division with comma-separated case pattern
// Path condition should be x == 1 || x == 2 || x == 3
@_requires("true")
@_ensures("result >= 0")
func divideWithCommaPattern(a: Int, x: Int) -> Int {
    switch x {
    case 1, 2, 3:
        return a / x  // auto-VC path condition: x == 1 || x == 2 || x == 3 -> VERIFIED
    default:
        return 0
    }
}

// =============================================================================
// SECTION 8: Division without protection (expected to fail)
// =============================================================================

// This should FAIL - division has no path condition protection for b != 0
@_requires("true")
@_ensures("result == a / b")
func divideUnprotectedSwitch(a: Int, b: Int) -> Int {
    switch b {
    case -1:
        return -a  // b == -1 case
    default:
        return a / b  // auto-VC path condition: !(b == -1) does NOT imply b != 0 -> FAILS
    }
}
