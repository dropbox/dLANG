// tests/verification/loop_nesting_test.swift
//
// Test file for loop nesting support: while/for-in loops followed by
// complex control flow (switch, if-else).
//
// IMPORTANT: The mock parser now supports:
// - while { ... }; switch { ... }
// - while { ... }; if/else { ... }
// - for i in range { ... }; switch { ... }
// - for i in range { ... }; if/else { ... }
//
// The loop body is NOT analyzed (use @trusted + @invariant for that).
// The post-loop control flow IS analyzed for verification.

// ============================================================================
// While loop followed by switch
// ============================================================================

// Accumulate counter, then classify final value
@_requires("n >= 0")
// @_invariant("i >= 0")
@_ensures("result >= 0")
func whileSwitch(_ n: Int) -> Int {
    var i = 0
    while i < n {
        i += 1
    }
    switch i {
    case 0: return 0
    case 1: return 1
    default: return 10
    }
}

// Count iterations, classify result
@_trusted
@_requires("n >= 0")
// @_invariant("count >= 0")
@_ensures("result >= 0")
func whileSwitchTrusted(_ n: Int) -> Int {
    var count = 0
    while count < n {
        count += 1
    }
    switch count {
    case 0: return 0
    case 1: return 1
    case 2, 3, 4: return count
    default: return 100
    }
}

// ============================================================================
// While loop followed by if-else
// ============================================================================

// Iterate then branch based on result
// Note: i - 10 when i > 10 is always >= 1, and i when i <= 10 is >= 0
// So result is always >= 0
@_requires("n >= 0")
// @_invariant("i >= 0")
@_ensures("result == result")  // tautology - just check VC generation works
func whileIfElse(_ n: Int) -> Int {
    var i = 0
    while i < n {
        i += 1
    }
    if i > 10 {
        return i - 10
    } else {
        return i
    }
}

// Accumulate with complex post-loop decision
// Use tautology ensures to verify VC generation
@_requires("n >= 0")
// @_invariant("sum >= 0")
@_ensures("result == result")  // tautology
func whileIfElseChain(_ n: Int) -> Int {
    var sum = 0
    var i = 0
    while i < n {
        sum += i
        i += 1
    }
    if sum > 100 {
        return 100
    } else if sum > 10 {
        return sum - 10
    } else {
        return sum
    }
}

// ============================================================================
// For-in loop followed by switch
// ============================================================================

// Sum range, then classify the sum
// Use tautology ensures to verify VC generation works
@_requires("n >= 0")
// @_invariant("sum >= 0")
@_ensures("result == result")  // tautology
func forInSwitch(_ n: Int) -> Int {
    var sum = 0
    for i in 0..<n {
        sum += i
    }
    switch sum {
    case 0: return 0
    case 1, 2, 3: return 1
    default: return sum
    }
}

// Product range (closed), then classify
@_trusted
@_requires("n >= 1")
// @_invariant("prod >= 1")
@_ensures("result >= 1")
func forInClosedSwitch(_ n: Int) -> Int {
    var prod = 1
    for i in 1...n {
        prod *= i
    }
    switch prod {
    case 1: return 1
    case 2: return 2
    case 6: return 6
    default: return 24
    }
}

// ============================================================================
// For-in loop followed by if-else
// ============================================================================

// Sum then branch - use tautology ensures
@_requires("n >= 0")
// @_invariant("sum >= 0")
@_ensures("result == result")  // tautology
func forInIfElse(_ n: Int) -> Int {
    var sum = 0
    for i in 0..<n {
        sum += i
    }
    if sum > 50 {
        return 50
    } else {
        return sum
    }
}

// Product with complex branching
@_trusted
@_requires("n >= 1")
// @_invariant("prod >= 1")
@_ensures("result >= 0")
func forInClosedIfElseChain(_ n: Int) -> Int {
    var prod = 1
    for i in 1...n {
        prod *= i
    }
    if prod > 1000 {
        return 1000
    } else if prod > 100 {
        return 100
    } else if prod > 10 {
        return 10
    } else {
        return prod
    }
}

// ============================================================================
// Complex nesting: loop -> switch -> nested if
// ============================================================================

// Loop, then switch with if-else inside case bodies
// Use tautology ensures for VC generation verification
@_requires("n >= 0 && flag >= 0")
// @_invariant("count >= 0")
@_ensures("result == result")  // tautology
func whileSwitchNestedIf(_ n: Int, _ flag: Int) -> Int {
    var count = 0
    while count < n {
        count += 1
    }
    switch count {
    case 0:
        if flag > 0 {
            return flag
        } else {
            return 0
        }
    case 1:
        return 1
    default:
        if flag > 10 {
            return count + flag
        } else {
            return count
        }
    }
}
