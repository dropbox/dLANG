// if_else_auto_vc_test.swift
// Test if/else path conditions with auto-VC detection
// Auto-VCs inside if/else branches should inherit the branch condition

// =============================================================================
// SECTION 1: Division in if branch (should verify with if condition)
// =============================================================================

// Division inside if b != 0 should verify (path condition makes b != 0)
@_requires("true")
@_ensures("result == a / b")
func divideInIfBranch(a: Int, b: Int) -> Int {
    if b != 0 {
        return a / b  // auto-VC path condition: b != 0 -> VERIFIED
    }
    return 0
}

// Division inside if b > 0 should verify (b > 0 implies b != 0)
@_requires("true")
@_ensures("result >= 0")
func divideInIfBranchPositive(a: Int, b: Int) -> Int {
    if b > 0 {
        return a / b  // auto-VC path condition: b > 0 -> VERIFIED
    }
    return 0
}

// =============================================================================
// SECTION 2: Division in else branch (should verify with negated condition)
// =============================================================================

// Division in else branch where if checks b == 0
// else branch has path condition !(b == 0), i.e., b != 0
@_requires("true")
@_ensures("result == a / b")
func divideInElseBranch(a: Int, b: Int) -> Int {
    if b == 0 {
        return 0
    } else {
        return a / b  // auto-VC path condition: !(b == 0) -> VERIFIED
    }
}

// =============================================================================
// SECTION 3: Division in else-if branch
// =============================================================================

// Division in else-if branch with explicit non-zero check
@_requires("true")
@_ensures("result >= 0")
func divideInElseIfBranch(a: Int, b: Int) -> Int {
    if a < 0 {
        return -1
    } else if b != 0 {
        return a / b  // auto-VC path condition: b != 0 -> VERIFIED
    } else {
        return 0
    }
}

// =============================================================================
// SECTION 4: Nested if statements
// =============================================================================

// Division inside nested if should have combined path conditions
@_requires("true")
@_ensures("result >= 0")
func divideInNestedIf(a: Int, b: Int) -> Int {
    if a >= 0 {
        if b > 0 {
            return a / b  // auto-VC path condition: a >= 0 AND b > 0 -> VERIFIED
        }
    }
    return 0
}

// =============================================================================
// SECTION 5: Guard + if combined
// =============================================================================

// Guard plus if should combine path conditions
@_requires("true")
@_ensures("result > 0")
func divideWithGuardAndIf(a: Int, b: Int) -> Int {
    guard a > 0 else { return 0 }
    if b > 0 {
        return a / b  // auto-VC path condition: a > 0 AND b > 0 -> VERIFIED
    }
    return 0
}

// =============================================================================
// SECTION 6: Division after if closes (no path condition)
// =============================================================================

// Division outside if should NOT have path condition (fails without @_requires)
// This demonstrates that path conditions are properly scoped
@_requires("b != 0")
@_ensures("result == a / b")
func divideAfterIfCloses(a: Int, b: Int) -> Int {
    if a > 0 {
        let _ = a + 1
    }
    return a / b  // auto-VC has no path condition; needs @_requires
}

// =============================================================================
// SECTION 7: Multiple divisions in different branches
// =============================================================================

// Both divisions should verify with their respective path conditions
@_requires("true")
@_ensures("result >= 0")
func multipleDivisionsInBranches(a: Int, b: Int, c: Int) -> Int {
    if b != 0 {
        return a / b  // auto-VC path condition: b != 0 -> VERIFIED
    } else if c != 0 {
        return a / c  // auto-VC path condition: c != 0 -> VERIFIED
    }
    return 0
}

// =============================================================================
// SECTION 8: Division without protection (expected to fail)
// =============================================================================

// This should FAIL - division has no path condition protection
// We include it to verify that unprotected divisions still generate failing auto-VCs
@_requires("true")
@_ensures("result == a / b")
func divideUnprotected(a: Int, b: Int) -> Int {
    return a / b  // auto-VC has no path condition -> FAILS
}
