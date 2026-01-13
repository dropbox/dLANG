// tests/verification/guard_test.swift
//
// Test file for guard statement support in function body verification.
// Guard statements are a common Swift pattern for early exits:
//
//   guard condition else { return earlyExitValue }
//   return normalValue
//
// This translates to: result == ite(condition, normalValue, earlyExitValue)
// The guard condition is TRUE for the main (non-early-exit) path.
//
// Verification formula:
//   (requires AND result == ite(cond, normal, early)) => ensures

// ============================================================================
// Clamp positive - return 0 for negative values
// ============================================================================

// Should verify: if x >= 0, result = x; if x < 0, result = 0
// Either way, result >= 0
@_requires("true")
@_ensures("result >= 0")
func clampPositive(_ x: Int) -> Int {
    guard x >= 0 else { return 0 }
    return x
}

// ============================================================================
// Safe division - return 0 for division by zero
// ============================================================================

// Should verify: result is 0 when y is 0
@_requires("true")
@_ensures("y != 0 || result == 0")
func safeDivByZero(_ x: Int, _ y: Int) -> Int {
    guard y != 0 else { return 0 }
    return x / y
}

// ============================================================================
// Clamp to range - ensures result is within bounds
// ============================================================================

// Should verify: result >= 0 (negative inputs clamped to 0)
@_requires("true")
@_ensures("result >= 0")
func clampNonNegative(_ x: Int) -> Int {
    guard x > 0 else { return 0 }
    return x
}

// ============================================================================
// Identity with positive guard
// ============================================================================

// For positive x, returns x unchanged
// For non-positive x, returns 1
@_requires("true")
@_ensures("result >= 1")
func atLeastOne(_ x: Int) -> Int {
    guard x >= 1 else { return 1 }
    return x
}

// ============================================================================
// Safe decrement - don't go below zero
// ============================================================================

// Should verify: result >= 0 always
@_requires("true")
@_ensures("result >= 0")
func safeDecrement(_ x: Int) -> Int {
    guard x > 0 else { return 0 }
    return x - 1
}

// ============================================================================
// Multi-line guard syntax
// ============================================================================

@_requires("true")
@_ensures("result >= 0")
func clampPositiveMultiLine(_ x: Int) -> Int {
    guard x >= 0 else {
        return 0
    }
    return x
}

// ============================================================================
// Guard with computation
// ============================================================================

// Double x if positive, return 0 otherwise
@_requires("true")
@_ensures("result >= 0")
func doubleIfPositive(_ x: Int) -> Int {
    guard x > 0 else { return 0 }
    return x * 2
}

// ============================================================================
// Intentionally wrong spec - should FAIL
// ============================================================================

// Should FAIL: when x < 0, we return 0, not something negative
@_requires("true")
@_ensures("result < 0")  // Wrong! We return 0 when x < 0
func badClampSpec(_ x: Int) -> Int {
    guard x >= 0 else { return 0 }
    return x
}

// ============================================================================
// Trusted function with guard
// ============================================================================

@_trusted
@_requires("true")
@_ensures("result > 1000")  // Would fail without @_trusted
func trustedClamp(_ x: Int) -> Int {
    guard x >= 0 else { return 0 }
    return x
}

// ============================================================================
// Multiple guards (guard chain)
// ============================================================================

// Should verify: both guards must pass for non-zero result
// guard x >= 0: if false, return 0; if true, check y
// guard y >= 0: if false, return 0; if true, return x + y
// Result: always >= 0
@_requires("true")
@_ensures("result >= 0")
func multiGuardSum(_ x: Int, _ y: Int) -> Int {
    guard x >= 0 else { return 0 }
    guard y >= 0 else { return 0 }
    return x + y
}

// Should verify: three guards in sequence
@_requires("true")
@_ensures("result >= 0")
func tripleGuard(_ x: Int, _ y: Int, _ z: Int) -> Int {
    guard x >= 0 else { return 0 }
    guard y >= 0 else { return 0 }
    guard z >= 0 else { return 0 }
    return x + y + z
}

// Should verify: guards with different early exit values
@_requires("true")
@_ensures("result >= -1")
func guardsWithDifferentReturns(_ x: Int, _ y: Int) -> Int {
    guard x >= 0 else { return -1 }
    guard y >= 0 else { return 0 }
    return x + y
}

// ============================================================================
// Switch inside guard patterns
// ============================================================================

// Should verify: guard filters negatives, switch classifies the rest
// When x < 0, return -1 (guard fails)
// When x >= 0: case 0 -> 0, case 1 -> 1, default -> 10
// Result: always >= -1
@_requires("true")
@_ensures("result >= -1")
func guardThenSwitch(_ x: Int) -> Int {
    guard x >= 0 else { return -1 }
    switch x {
    case 0: return 0
    case 1: return 1
    default: return 10
    }
}

// Should verify: guard ensures divisor valid, switch selects operation
// If y == 0, return 0 (guard fails)
// If y != 0: op==0 -> x+y, op==1 -> x-y, default -> x*y
// Result: always defined (no division by zero risk in any branch)
@_requires("true")
@_ensures("y == 0 || result == result")  // Tautology to check it parses
func guardSwitchSafeOp(_ x: Int, _ y: Int, _ op: Int) -> Int {
    guard y != 0 else { return 0 }
    switch op {
    case 0: return x + y
    case 1: return x - y
    default: return x * y
    }
}

// Should verify: multiple guards before switch
// x < 0 -> return -1
// y < 0 -> return -2
// switch classifies positive x: 0->0, 1->y, 2->x+y, default->100
// Result: always >= -2
@_requires("true")
@_ensures("result >= -2")
func multiGuardThenSwitch(_ x: Int, _ y: Int) -> Int {
    guard x >= 0 else { return -1 }
    guard y >= 0 else { return -2 }
    switch x {
    case 0: return 0
    case 1: return y
    case 2: return x + y
    default: return 100
    }
}

// Should verify: guard + switch with range patterns
// When x < 0 -> return -1
// When x >= 0:
//   case 0..<10 -> x (0-9)
//   case 10..<100 -> x (10-99)
//   default -> 100
// Result: always >= -1
@_requires("true")
@_ensures("result >= -1")
func guardSwitchRange(_ x: Int) -> Int {
    guard x >= 0 else { return -1 }
    switch x {
    case 0..<10: return x
    case 10..<100: return x
    default: return 100
    }
}
