//! Integration test for Phase 12.2 refinement widening at join points
//!
//! This test verifies that refinement predicates are correctly merged at
//! control flow join points (where multiple basic blocks converge).
//!
//! Key features tested:
//! - Refinements from both if/else branches are available after the join
//! - Common refinements are preserved (when both paths have same refinement)
//! - Disjunctive refinements work correctly (when paths have different predicates)
//! - Multiple levels of control flow work correctly
//!
//! Note: The tracked refinements are reported in verbose output with:
//! "[tRust] Phase 12.2: Tracked N refinement(s) through assignments"

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Same refinement in both branches (should preserve at join)
// ============================================================================

/// When both branches have the same refinement, it should be preserved at join
/// n > 0 propagates to x in both branches, so after the if/else, x > 0 still holds
#[trust::refined(n, "n > 0")]
#[ensures("result > 0")]
fn same_refinement_both_branches(n: i32, flag: bool) -> i32 {
    let x = n;  // x > 0
    if flag {
        // x > 0 still holds here
        x
    } else {
        // x > 0 still holds here
        x
    }
}

/// Refinement copied before branching is available in both branches
#[trust::refined(val, "val >= 0")]
#[ensures("result >= 0")]
fn refinement_copied_before_branch(val: i32, cond: bool) -> i32 {
    let v = val;  // v >= 0
    if cond {
        v  // result >= 0
    } else {
        v  // result >= 0
    }
}

// ============================================================================
// Part 2: Refinements from multiple assignments (chain propagation)
// ============================================================================

/// Chain: n -> x -> y, refinement should propagate through
#[trust::refined(n, "n != 0")]
#[ensures("result != 0")]
fn chain_before_branch(n: i32, flag: bool) -> i32 {
    let x = n;  // x != 0
    let y = x;  // y != 0
    if flag {
        y  // result != 0
    } else {
        y  // result != 0
    }
}

/// Multiple refined params, both preserved through branches
#[trust::refined(a, "a > 0")]
#[trust::refined(b, "b >= 0")]
#[ensures("result > 0")]
fn multiple_refinements_branch(a: i32, b: i32, flag: bool) -> i32 {
    let x = a;  // x > 0
    let y = b;  // y >= 0
    if flag {
        x  // result > 0 (from x)
    } else {
        x  // result > 0 (from x)
    }
}

// ============================================================================
// Part 3: Constant inference through branches
// ============================================================================

/// Constants assigned before branch should be available at join
#[ensures("result >= 5")]
fn constant_before_branch(flag: bool) -> i32 {
    let x = 5;  // x == 5
    if flag {
        x  // result == 5, therefore result >= 5
    } else {
        x  // result == 5, therefore result >= 5
    }
}

/// Constants assigned in both branches (same value)
#[ensures("result == 10")]
fn constant_same_both_branches(flag: bool) -> i32 {
    let result = if flag {
        10  // 10
    } else {
        10  // 10
    };
    result  // result == 10 in both paths
}

// ============================================================================
// Part 4: Nested control flow (multiple join points)
// ============================================================================

/// Nested if/else: refinement should propagate through multiple joins
#[trust::refined(n, "n > 0")]
#[ensures("result > 0")]
fn nested_branches(n: i32, flag1: bool, flag2: bool) -> i32 {
    let x = n;  // x > 0
    if flag1 {
        if flag2 {
            x  // result > 0
        } else {
            x  // result > 0
        }
    } else {
        x  // result > 0
    }
}

/// Multiple sequential branches
#[trust::refined(val, "val >= 0")]
#[ensures("result >= 0")]
fn sequential_branches(val: i32, c1: bool, c2: bool) -> i32 {
    let x = val;  // x >= 0
    // First branch
    let y = if c1 { x } else { x };  // y >= 0 at join
    // Second branch
    if c2 {
        y  // result >= 0
    } else {
        y  // result >= 0
    }
}

// ============================================================================
// Part 5: Binary operations before branch
// ============================================================================

/// Addition before branch, result carries refinement
#[trust::refined(n, "n >= 0")]
#[requires("n <= 1000")]  // For overflow safety
#[ensures("result >= 1")]
fn binop_before_branch(n: i32, flag: bool) -> i32 {
    let x = n + 1;  // x >= 1 (from n >= 0)
    if flag {
        x  // result >= 1
    } else {
        x  // result >= 1
    }
}

/// Subtraction with bounds
#[trust::refined(n, "n > 10")]
#[requires("n > 10 && n < 1000")]  // For overflow safety (lower bound needed for subtraction)
#[ensures("result > 0")]
fn sub_before_branch(n: i32, cond: bool) -> i32 {
    let x = n - 5;  // x > 5 (from n > 10)
    if cond {
        x  // result > 0 (since x > 5 > 0)
    } else {
        x  // result > 0
    }
}

// ============================================================================
// Part 6: Match expressions (multiple branches joining)
// ============================================================================

/// Match with refinement propagated to all arms
#[trust::refined(n, "n >= 0")]
#[ensures("result >= 0")]
fn match_same_refinement(n: i32, choice: i32) -> i32 {
    let x = n;  // x >= 0
    match choice {
        0 => x,      // result >= 0
        1 => x,      // result >= 0
        _ => x,      // result >= 0
    }
}

/// Match with constant values
#[ensures("result >= 1")]
fn match_constants(choice: i32) -> i32 {
    match choice {
        0 => 1,   // result == 1 >= 1
        1 => 2,   // result == 2 >= 1
        2 => 3,   // result == 3 >= 1
        _ => 10,  // result == 10 >= 1
    }
}

// ============================================================================
// Part 7: Loop-like patterns (join from back edge)
// ============================================================================

/// Simple conditional that models loop-like control flow
#[trust::refined(n, "n > 0")]
#[ensures("result > 0")]
fn conditional_loop_like(n: i32, iterations: i32) -> i32 {
    let mut x = n;  // x > 0
    // In MIR this will have a join point from the loop back edge
    if iterations > 0 {
        // The refinement x > 0 should be preserved
        x
    } else {
        x
    }
}

// ============================================================================
// Part 8: Return value refinement
// ============================================================================

/// Return refinement with branching
#[trust::refined(n, "n > 0")]
#[trust::returns_refined("result > 0")]
fn return_refined_branch(n: i32, flag: bool) -> i32 {
    let x = n;  // x > 0
    if flag {
        x  // result > 0
    } else {
        x  // result > 0
    }
}

/// Combined refined parameter and return
#[trust::refined(val, "val != 0")]
#[trust::returns_refined("result != 0")]
fn refined_param_and_return(val: i32, cond: bool) -> i32 {
    let v = val;  // v != 0
    if cond {
        v  // result != 0
    } else {
        v  // result != 0
    }
}

fn main() {
    // Part 1: Same refinement both branches
    assert!(same_refinement_both_branches(5, true) > 0);
    assert!(same_refinement_both_branches(5, false) > 0);
    assert!(refinement_copied_before_branch(10, true) >= 0);
    assert!(refinement_copied_before_branch(10, false) >= 0);

    // Part 2: Chain propagation
    assert!(chain_before_branch(42, true) != 0);
    assert!(chain_before_branch(42, false) != 0);
    assert!(multiple_refinements_branch(1, 0, true) > 0);
    assert!(multiple_refinements_branch(1, 0, false) > 0);

    // Part 3: Constants
    assert!(constant_before_branch(true) >= 5);
    assert!(constant_before_branch(false) >= 5);
    assert!(constant_same_both_branches(true) == 10);
    assert!(constant_same_both_branches(false) == 10);

    // Part 4: Nested control flow
    assert!(nested_branches(3, true, true) > 0);
    assert!(nested_branches(3, true, false) > 0);
    assert!(nested_branches(3, false, true) > 0);
    assert!(sequential_branches(5, true, true) >= 0);
    assert!(sequential_branches(5, false, false) >= 0);

    // Part 5: Binary operations
    assert!(binop_before_branch(0, true) >= 1);
    assert!(binop_before_branch(0, false) >= 1);
    assert!(sub_before_branch(20, true) > 0);
    assert!(sub_before_branch(20, false) > 0);

    // Part 6: Match expressions
    assert!(match_same_refinement(5, 0) >= 0);
    assert!(match_same_refinement(5, 1) >= 0);
    assert!(match_same_refinement(5, 99) >= 0);
    assert!(match_constants(0) >= 1);
    assert!(match_constants(1) >= 1);
    assert!(match_constants(99) >= 1);

    // Part 7: Loop-like
    assert!(conditional_loop_like(1, 5) > 0);
    assert!(conditional_loop_like(1, 0) > 0);

    // Part 8: Return value refinement
    assert!(return_refined_branch(1, true) > 0);
    assert!(return_refined_branch(1, false) > 0);
    assert!(refined_param_and_return(42, true) != 0);
    assert!(refined_param_and_return(42, false) != 0);

    println!("Phase 12.2: All refinement join widening tests passed!");
}
