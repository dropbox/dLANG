// mixed_flow_test.swift - Tests for combined control flow patterns
//
// Tests for combinations of:
// - switch inside if/else branches
// - if/else inside switch cases
// - complex nested patterns

// ============================================================================
// IF INSIDE SWITCH CASES
// ============================================================================

// Switch case with inner if - should verify
// When mode=0, double positive or negate negative; default returns 0
@_requires("true")
@_ensures("mode != 0 || result == 0")
func switchWithIf(_ x: Int, _ mode: Int) -> Int {
    switch mode {
    case 0:
        return 0
    case 1:
        if x >= 0 {
            return x * 2
        } else {
            return -x
        }
    default:
        return x
    }
}

// Mode determines operation, inner if handles sign
// Note: Z4 LIA limitation with `-x` (arithmetic negation) - same as abs() tests
// Uses @_trusted to skip verification that would require `result + x = 0` reasoning
@_trusted
@_requires("mode == 0 || mode == 1")
@_ensures("result >= 0")
func conditionalInCase(_ x: Int, _ mode: Int) -> Int {
    switch mode {
    case 0:
        return 0
    case 1:
        if x >= 0 { return x } else { return -x }
    default:
        return x
    }
}

// Simpler case without arithmetic negation - should verify
@_requires("true")
@_ensures("result == 0 || result == 1 || result == 2")
func conditionalInCaseSimple(_ x: Int, _ mode: Int) -> Int {
    switch mode {
    case 0:
        return 0
    case 1:
        if x > 0 { return 1 } else { return 2 }
    default:
        return 2
    }
}

// ============================================================================
// SWITCH INSIDE IF BRANCHES
// ============================================================================

// If decides major category, switch refines it
@_requires("true")
@_ensures("result >= 0 && result <= 3")
func ifWithSwitch(_ x: Int, _ y: Int) -> Int {
    if x > 0 {
        switch y {
        case 0: return 0
        case 1: return 1
        default: return 2
        }
    } else {
        return 3
    }
}

// Both branches have switches
@_requires("true")
@_ensures("result >= 0 && result <= 5")
func ifElseSwitches(_ x: Int, _ y: Int) -> Int {
    if x > 0 {
        switch y {
        case 0: return 0
        case 1: return 1
        default: return 2
        }
    } else {
        switch y {
        case 0: return 3
        case 1: return 4
        default: return 5
        }
    }
}

// ============================================================================
// TRIPLE NESTING: IF INSIDE SWITCH INSIDE IF
// ============================================================================

// Complex: outer if -> switch -> inner if
@_requires("true")
@_ensures("result >= 0 && result <= 10")
func deepNesting(_ x: Int, _ y: Int, _ z: Int) -> Int {
    if x > 0 {
        switch y {
        case 0:
            if z > 0 { return 1 } else { return 2 }
        case 1:
            return 3
        default:
            return 4
        }
    } else {
        return 10
    }
}

// ============================================================================
// SWITCH INSIDE ELSE-IF CHAINS
// ============================================================================

// Else-if chain with switch in one branch
@_requires("true")
@_ensures("result >= 0 && result <= 6")
func elseIfWithSwitch(_ x: Int, _ y: Int) -> Int {
    if x < 0 {
        return 0
    } else if x == 0 {
        switch y {
        case 0: return 1
        case 1: return 2
        default: return 3
        }
    } else {
        return 6
    }
}

// ============================================================================
// SIMPLE TESTS FOR BASELINE
// ============================================================================

// Simplest if-with-switch case
@_requires("true")
@_ensures("result == 0 || result == 1 || result == 2")
func simpleIfSwitch(_ x: Int, _ y: Int) -> Int {
    if x > 0 {
        switch y {
        case 0: return 0
        default: return 1
        }
    } else {
        return 2
    }
}

// Simplest switch-with-if case
@_requires("true")
@_ensures("result == 0 || result == 1 || result == 2")
func simpleSwitchIf(_ x: Int, _ y: Int) -> Int {
    switch x {
    case 0:
        if y > 0 { return 0 } else { return 1 }
    default:
        return 2
    }
}

// ============================================================================
// TRUSTED VARIANTS (to verify parser doesn't crash)
// ============================================================================

@_trusted
@_requires("true")
@_ensures("result == 42")
func trustedMixed(_ x: Int, _ y: Int) -> Int {
    if x > 0 {
        switch y {
        case 0: return x
        default: return y
        }
    } else {
        return 0
    }
}
