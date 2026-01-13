//! Integration test for Phase 12.2 refinement tracking through assignments
//!
//! This test verifies that refinement predicates are correctly propagated
//! through simple copy/move assignments from refined parameters to local variables.
//!
//! Key features tested:
//! - Refinement predicates propagate through `let x = n` assignments
//! - Multiple assignments chain correctly (n -> x -> y)
//! - Propagated refinements enable call-site verification
//!
//! Note: The tracked refinements are reported in verbose output with:
//! "[tRust] Phase 12.2: Tracked N refinement(s) through assignments"

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Basic refinement propagation through assignment
// ============================================================================

/// Simple refinement propagation: refined param -> local variable
/// The refinement "n > 0" should propagate to local variable x
#[trust::refined(n, "n > 0")]
#[ensures("result > 0")]
fn propagate_to_local(n: i32) -> i32 {
    let x = n;  // x gets refinement "x > 0" (from n)
    x           // result > 0 because x > 0 because n > 0
}

/// Chain propagation: n -> x -> y
/// Refinements should propagate through multiple assignments
#[trust::refined(n, "n >= 10")]
#[ensures("result >= 10")]
fn chain_propagation(n: i32) -> i32 {
    let x = n;  // x gets refinement "x >= 10"
    let y = x;  // y gets refinement "y >= 10"
    y           // result >= 10
}

// ============================================================================
// Part 2: Multiple refined parameters
// ============================================================================

/// Multiple refined params with separate propagation
#[trust::refined(a, "a > 0")]
#[trust::refined(b, "b > 0")]
#[ensures("result > 0")]
fn multiple_params(a: i32, b: i32) -> i32 {
    let x = a;  // x gets refinement "x > 0"
    let y = b;  // y gets refinement "y > 0"
    if x > y { x } else { y }  // result > 0
}

/// Cross assignment between refined params
#[trust::refined(lo, "lo >= 0")]
#[trust::refined(hi, "hi >= lo")]
#[ensures("result >= 0")]
fn cross_assignment(lo: i32, hi: i32) -> i32 {
    let lower = lo;  // lower gets refinement "lower >= 0"
    let upper = hi;  // upper gets refinement "upper >= lo"
    lower  // result >= 0 because lower >= 0
}

// ============================================================================
// Part 3: Refinement with computation (basic inference future work)
// ============================================================================

/// Propagation with simple return
/// This shows the base case works - variable carries refinement to return
#[trust::refined(n, "n >= 0")]
#[ensures("result >= 0")]
fn return_via_local(n: i32) -> i32 {
    let r = n;  // r gets refinement "r >= 0"
    r           // result >= 0
}

/// Nested locals (multiple copy chains)
#[trust::refined(n, "n > 5")]
#[ensures("result > 5")]
fn nested_locals(n: i32) -> i32 {
    let a = n;  // a > 5
    let b = a;  // b > 5
    let c = b;  // c > 5
    c           // result > 5
}

// ============================================================================
// Part 4: Refinement tracking with control flow
// ============================================================================

/// Refinement in both branches (simple case)
/// The refinement should be available in both branches
#[trust::refined(n, "n >= 0")]
#[ensures("result >= 0")]
fn refinement_in_branches(n: i32, flag: bool) -> i32 {
    let x = n;  // x >= 0
    if flag {
        x  // result >= 0 from x
    } else {
        x  // result >= 0 from x
    }
}

/// Conditional use of refined local
#[trust::refined(val, "val != 0")]
#[ensures("result != 0")]
fn conditional_refined(val: i32, use_direct: bool) -> i32 {
    let v = val;  // v != 0
    if use_direct {
        val  // result != 0
    } else {
        v    // result != 0
    }
}

// ============================================================================
// Part 5: Unsigned integers and other types
// ============================================================================

/// Unsigned refinement propagation
#[trust::refined(idx, "idx < 100")]
#[requires("idx < 100")]  // Explicit for automatic bounds checker
#[ensures("result < 100")]
fn unsigned_propagation(idx: usize) -> usize {
    let i = idx;  // i < 100
    i             // result < 100
}

/// Boolean result with refined input
#[trust::refined(n, "n > 0")]
#[trust::returns_refined("result == true")]
fn always_positive(n: i32) -> bool {
    let x = n;  // x > 0
    x > 0       // always true since x > 0
}

fn main() {
    // Part 1: Basic propagation
    assert!(propagate_to_local(5) > 0);
    assert!(chain_propagation(15) >= 10);

    // Part 2: Multiple params
    assert!(multiple_params(3, 7) > 0);
    assert!(cross_assignment(0, 10) >= 0);

    // Part 3: Return via local
    assert!(return_via_local(42) >= 0);
    assert!(nested_locals(10) > 5);

    // Part 4: Control flow
    assert!(refinement_in_branches(5, true) >= 0);
    assert!(refinement_in_branches(5, false) >= 0);
    assert!(conditional_refined(42, true) != 0);
    assert!(conditional_refined(42, false) != 0);

    // Part 5: Unsigned and boolean
    assert!(unsigned_propagation(50) < 100);
    assert!(always_positive(1));

    println!("Phase 12.2: All refinement tracking tests passed!");
}
