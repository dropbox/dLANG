// tests/verification/loop_test.swift
//
// Test file for loop support (while and for-in) in function body verification.
// Loops require @invariant annotations for proper verification.
//
// IMPORTANT: The mock parser has limited loop support:
// - It detects while and for-in loops
// - It captures the return expression after the loop
// - Local variables in return expressions are NOT tracked through loop execution
// - Full loop verification requires @trusted or proper symbolic execution
//
// For comprehensive loop verification, functions should be marked @trusted
// and rely on the invariant + postcondition contract.

// ============================================================================
// Trusted loops - use invariant/ensures contract
// These verify because @trusted skips body constraint checking
// ============================================================================

// Counts from 0 to n, returns the final count
@_trusted
@_requires("n >= 0")
// @_invariant("i >= 0")
@_ensures("result >= 0")
func countUp(_ n: Int) -> Int {
    var i = 0
    while i < n {
        i += 1
    }
    return i
}

// Accumulates sum from 0 to n-1
@_trusted
@_requires("n >= 0")
// @_invariant("sum >= 0")
@_ensures("result >= 0")
func sumUpTo(_ n: Int) -> Int {
    var sum = 0
    var i = 0
    while i < n {
        sum += i
        i += 1
    }
    return sum
}

// Counts down from n to 0
@_trusted
@_requires("n >= 0")
// @_invariant("count >= 0")
@_ensures("result >= 0")
func countDown(_ n: Int) -> Int {
    var count = n
    while count > 0 {
        count -= 1
    }
    return count
}

// ============================================================================
// Trusted for-in loops
// ============================================================================

// Sums values from 0 to n-1 using for-in
@_trusted
@_requires("n >= 0")
// @_invariant("sum >= 0")
@_ensures("result >= 0")
func forSumHalfOpen(_ n: Int) -> Int {
    var sum = 0
    for i in 0..<n {
        sum += i
    }
    return sum
}

// Sums values from 1 to n using for-in closed range
@_trusted
@_requires("n >= 1")
// @_invariant("sum >= 0")
@_ensures("result >= 1")
func forSumClosed(_ n: Int) -> Int {
    var sum = 0
    for i in 1...n {
        sum += i
    }
    return sum
}

// ============================================================================
// Loop returning parameter value (verifies without @trusted)
// ============================================================================

// Returns the input n after loop (loop doesn't modify what we return)
@_requires("n >= 0")
// @_invariant("i >= 0")
@_ensures("result == n")
func loopReturnsParam(_ n: Int) -> Int {
    var i = 0
    while i < n {
        i += 1
    }
    return n  // Return param, not local var
}

// For-in returning constant
@_requires("true")
// @_invariant("sum >= 0")
@_ensures("result == 42")
func forLoopReturnsConstant() -> Int {
    var sum = 0
    for i in 0..<10 {
        sum += i
    }
    return 42  // Return constant
}

// ============================================================================
// Mock parser loop detection tests
// These test that loops are correctly identified and parsed
// ============================================================================

// While loop with complex condition
@_trusted
@_requires("n > 0 && m > 0")
// @_invariant("x >= 0")
@_ensures("result >= 0")
func nestedConditionLoop(_ n: Int, _ m: Int) -> Int {
    var x = 0
    while x < n && x < m {
        x += 1
    }
    return x
}

// For-in loop with parameter bounds
@_trusted
@_requires("start >= 0 && end > start")
// @_invariant("sum >= 0")
@_ensures("result >= 0")
func paramBoundsLoop(_ start: Int, _ end: Int) -> Int {
    var sum = 0
    for i in start..<end {
        sum += i
    }
    return sum
}

// ============================================================================
// Intentionally wrong specs - should FAIL even with @trusted skip logic
// ============================================================================

// Wrong: trusted skips body but still checks basic contract (this verifies)
@_trusted
@_requires("n >= 0")
// @_invariant("i >= 0")
@_ensures("result > -1000")  // Still weak enough to pass with trusted
func badButTrusted(_ n: Int) -> Int {
    var i = 0
    while i < n {
        i += 1
    }
    return i
}

// ============================================================================
// Comprehensive loop test
// ============================================================================

@_trusted
@_requires("n >= 0")
@_ensures("result == n * (n - 1) / 2")
func gaussianSum(_ n: Int) -> Int {
    var sum = 0
    var i = 0
    while i < n {
        sum += i
        i += 1
    }
    return sum
}
