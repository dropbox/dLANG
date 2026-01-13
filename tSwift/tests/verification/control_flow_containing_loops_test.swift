// Test: Control flow containing loops + nested loops
// This file tests patterns where control flow structures contain loops inside them.
// These patterns are the inverse of loop_nesting_test.swift (which tests loops followed by control flow).
//
// Patterns tested:
// - if { while/for { ... } } - if branch containing loop
// - switch { case: while/for { ... } } - switch case containing loop
// - guard + if { while { ... } } - guard then if-with-loop
// - while { for { ... } } - nested loops
// - if { for { ... }; switch { ... } } - loop followed by control flow in branch
//
// All tests use @_trusted since loop bodies are not analyzed (verification relies on @invariant).

// ============================================================
// SECTION 1: If branches containing loops
// ============================================================

// Test 1.1: if branch containing while loop
// @requires(n >= 0)
// @ensures(result >= 0)
// @invariant(sum >= 0)
@_trusted
func ifContainingWhile(n: Int) -> Int {
    if n > 10 {
        var sum = 0
        var i = 0
        while i < n {
            sum = sum + 1
            i = i + 1
        }
        return sum
    } else {
        return 0
    }
}

// Test 1.2: if branch containing for-in loop
// @requires(n >= 0)
// @ensures(result >= 0)
// @invariant(total >= 0)
@_trusted
func ifContainingForIn(n: Int) -> Int {
    if n > 5 {
        var total = 0
        for i in 0..<n {
            total = total + i
        }
        return total
    } else {
        return 1
    }
}

// Test 1.3: both if and else branches containing loops
// @requires(n >= 0)
// @ensures(result >= 0)
// @invariant(count >= 0)
// @invariant(sum >= 0)
@_trusted
func bothBranchesWithLoops(n: Int, flag: Int) -> Int {
    if flag > 0 {
        var count = 0
        while count < n {
            count = count + 1
        }
        return count
    } else {
        var sum = 0
        for i in 0...n {
            sum = sum + 1
        }
        return sum
    }
}

// Test 1.4: if-else-if with different loops in each branch
// @requires(n >= 0)
// @ensures(result >= 0)
// @invariant(a >= 0)
// @invariant(b >= 0)
@_trusted
func elseIfWithLoops(n: Int, mode: Int) -> Int {
    if mode == 0 {
        var a = 0
        while a < n {
            a = a + 1
        }
        return a
    } else if mode == 1 {
        var b = 0
        for i in 0..<n {
            b = b + i
        }
        return b
    } else {
        return n
    }
}

// ============================================================
// SECTION 2: Switch cases containing loops
// ============================================================

// Test 2.1: switch case with for-in loop
// @requires(n >= 0)
// @ensures(result >= 0)
// @invariant(total >= 0)
@_trusted
func switchCaseWithLoop(n: Int, op: Int) -> Int {
    switch op {
    case 0:
        return 0
    case 1:
        var total = 0
        for i in 0..<n {
            total = total + 1
        }
        return total
    default:
        return n
    }
}

// Test 2.2: multiple switch cases with loops
// @requires(n >= 0)
// @ensures(result >= 0)
// @invariant(sum >= 0)
// @invariant(prod >= 1)
@_trusted
func switchMultipleCasesWithLoops(n: Int, op: Int) -> Int {
    switch op {
    case 0:
        var sum = 0
        for i in 0..<n {
            sum = sum + i
        }
        return sum
    case 1:
        var prod = 1
        var j = 0
        while j < n {
            prod = prod * 2
            j = j + 1
        }
        return prod
    default:
        return 0
    }
}

// ============================================================
// SECTION 3: Nested loops
// ============================================================

// Test 3.1: while containing for-in
// @requires(n >= 0)
// @ensures(result >= 0)
// @invariant(outer >= 0)
@_trusted
func whileContainingForIn(n: Int) -> Int {
    var outer = 0
    while outer < n {
        for i in 0..<5 {
            outer = outer + 1
        }
    }
    return outer
}

// Test 3.2: for-in containing while
// @requires(n >= 0)
// @ensures(result >= 0)
// @invariant(total >= 0)
@_trusted
func forInContainingWhile(n: Int) -> Int {
    var total = 0
    for i in 0..<n {
        var j = 0
        while j < 3 {
            total = total + 1
            j = j + 1
        }
    }
    return total
}

// Test 3.3: double for-in loop
// @requires(rows >= 0)
// @requires(cols >= 0)
// @ensures(result >= 0)
// @invariant(count >= 0)
@_trusted
func doubleForIn(rows: Int, cols: Int) -> Int {
    var count = 0
    for i in 0..<rows {
        for j in 0..<cols {
            count = count + 1
        }
    }
    return count
}

// ============================================================
// SECTION 4: Loop followed by control flow in branches
// ============================================================

// Test 4.1: if-branch with loop followed by switch
// @requires(n >= 0)
// @ensures(result >= 0)
// @invariant(sum >= 0)
@_trusted
func ifBranchLoopThenSwitch(n: Int, mode: Int) -> Int {
    if mode > 0 {
        var sum = 0
        for i in 0..<n {
            sum = sum + 1
        }
        switch sum {
        case 0:
            return 0
        case 1:
            return 1
        default:
            return sum
        }
    } else {
        return 0
    }
}

// Test 4.2: if-branch with loop followed by if-else
// @requires(n >= 0)
// @ensures(result >= 0)
// @invariant(count >= 0)
@_trusted
func ifBranchLoopThenIfElse(n: Int, flag: Int) -> Int {
    if flag > 0 {
        var count = 0
        while count < n {
            count = count + 1
        }
        if count > 10 {
            return 10
        } else {
            return count
        }
    } else {
        return 0
    }
}

// ============================================================
// SECTION 5: Guard + control flow with loops
// ============================================================

// Test 5.1: guard followed by if-branch with loop
// @requires(n >= 0)
// @ensures(result >= -1)
// @invariant(sum >= 0)
@_trusted
func guardThenIfWithLoop(n: Int, flag: Int) -> Int {
    guard n >= 0 else { return -1 }
    if flag > 0 {
        var sum = 0
        while sum < n {
            sum = sum + 1
        }
        return sum
    } else {
        return 0
    }
}

// Test 5.2: multiple guards then loop
// @requires(n >= 0)
// @ensures(result >= -2)
// @invariant(total >= 0)
@_trusted
func multiGuardThenLoop(n: Int, flag: Int) -> Int {
    guard n >= 0 else { return -1 }
    guard flag > 0 else { return -2 }
    var total = 0
    for i in 0..<n {
        total = total + 1
    }
    return total
}

// ============================================================
// SECTION 6: Deeply nested patterns
// ============================================================

// Test 6.1: if { for { switch } }
// @requires(n >= 1)
// @ensures(result >= 0)
// @invariant(result_val >= 0)
@_trusted
func ifForSwitch(n: Int, mode: Int) -> Int {
    if mode > 0 {
        var result_val = 0
        for i in 0..<n {
            switch i {
            case 0:
                result_val = result_val + 1
            case 1:
                result_val = result_val + 2
            default:
                result_val = result_val + i
            }
        }
        return result_val
    } else {
        return 0
    }
}

// Test 6.2: guard + switch + loop in case
// @requires(n >= 0)
// @ensures(result >= -1)
// @invariant(acc >= 0)
@_trusted
func guardSwitchLoop(n: Int, op: Int) -> Int {
    guard n >= 0 else { return -1 }
    switch op {
    case 0:
        return 0
    case 1:
        var acc = 0
        for i in 0..<n {
            acc = acc + i
        }
        return acc
    default:
        return n
    }
}
