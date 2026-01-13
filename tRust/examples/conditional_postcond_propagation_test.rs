//! Conditional Postcondition Propagation Test
//!
//! Tests that postconditions from called functions are correctly propagated
//! through various control flow structures in the caller. This validates
//! that the modular verification approach handles postcondition facts when
//! they flow through if-else, match, and other branching constructs.
//!
//! Expected outcomes:
//! All functions should VERIFY - postconditions should chain correctly
//! through different control flow patterns.

#![allow(unused)]

// ============================================================================
// Helper functions with postconditions
// ============================================================================

/// Returns 0 or 1 based on boolean input
#[ensures("result < 2")]
fn idx_from_bool(b: bool) -> usize {
    if b { 0 } else { 1 }
}

/// Returns a value guaranteed to be less than n (when n > 0)
#[requires("n > 0")]
#[ensures("result >= 0")]
#[ensures("result < n")]
fn bounded_value(n: i32) -> i32 {
    n - 1
}

/// Returns value clamped to [0, limit]
#[requires("limit >= 0")]
#[ensures("result >= 0")]
#[ensures("result <= limit")]
fn clamp_positive(val: i32, limit: i32) -> i32 {
    if val < 0 { 0 }
    else if val > limit { limit }
    else { val }
}

// ============================================================================
// Test: Postcondition through if-else branches
// ============================================================================

/// Postcondition should flow through both branches of if-else
#[ensures("result < 2")]
fn postcond_through_if_else(flag: bool, branch: bool) -> usize {
    if branch {
        idx_from_bool(flag)  // postcondition: result < 2
    } else {
        idx_from_bool(!flag)  // postcondition: result < 2
    }
}

/// Postcondition with constant in one branch
#[ensures("result < 3")]
fn postcond_mixed_branches(flag: bool, use_call: bool) -> usize {
    if use_call {
        idx_from_bool(flag)  // postcondition: result < 2, which implies result < 3
    } else {
        2  // constant < 3
    }
}

// ============================================================================
// Test: Postcondition through match expressions
// ============================================================================

#[derive(Copy, Clone)]
enum Choice {
    UseFirst,
    UseSecond,
    UseBoth,
}

/// Postcondition through match with multiple callee invocations
#[ensures("result < 2")]
fn postcond_through_match(a: bool, b: bool, choice: Choice) -> usize {
    match choice {
        Choice::UseFirst => idx_from_bool(a),
        Choice::UseSecond => idx_from_bool(b),
        Choice::UseBoth => idx_from_bool(a && b),
    }
}

/// Postcondition with mixed match arms (calls and constants)
#[ensures("result < 4")]
fn postcond_mixed_match_arms(flag: bool, choice: Choice) -> usize {
    match choice {
        Choice::UseFirst => idx_from_bool(flag),  // < 2
        Choice::UseSecond => 2,  // constant
        Choice::UseBoth => 3,  // constant
    }
}

// ============================================================================
// Test: Multiple postconditions combining
// ============================================================================

/// Both postconditions from bounded_value should propagate
#[requires("n > 0")]
#[ensures("result >= 0")]
#[ensures("result < n")]
fn relay_bounded(n: i32) -> i32 {
    bounded_value(n)
}

/// Chain of two bounded calls
#[requires("n > 1")]
#[ensures("result >= 0")]
#[ensures("result < n - 1")]
fn chained_bounded(n: i32) -> i32 {
    let intermediate = bounded_value(n);  // 0 <= intermediate < n
    if intermediate > 0 {
        bounded_value(intermediate)  // 0 <= result < intermediate < n
    } else {
        0  // edge case: intermediate == 0, so result == 0 < n-1 (since n > 1)
    }
}

// ============================================================================
// Test: Postcondition through nested conditionals
// ============================================================================

/// Deeply nested if-else with postcondition at leaves
#[ensures("result < 2")]
fn deep_nested_postcond(a: bool, b: bool, c: bool) -> usize {
    if a {
        if b {
            idx_from_bool(c)
        } else {
            0
        }
    } else {
        if c {
            1
        } else {
            idx_from_bool(b)
        }
    }
}

// ============================================================================
// Test: Postcondition in loop body (single iteration reasoning)
// ============================================================================

/// Postcondition should hold for value computed in each iteration
#[ensures("result < 2")]
fn postcond_in_loop(flags: [bool; 4]) -> usize {
    let mut last = 0;
    for flag in flags {
        last = idx_from_bool(flag);  // postcondition: last < 2
    }
    last  // last < 2 from final call
}

// ============================================================================
// Test: Combining multiple callee postconditions
// ============================================================================

/// Choose between two bounded values based on condition
/// Both x and y come from clamp_positive with the same limit
#[requires("limit >= 0")]
#[ensures("result >= 0")]
#[ensures("result <= limit")]
fn pick_clamped(a: i32, b: i32, limit: i32, pick_first: bool) -> i32 {
    let x = clamp_positive(a, limit);  // 0 <= x <= limit
    let y = clamp_positive(b, limit);  // 0 <= y <= limit
    if pick_first { x } else { y }  // either way, result in [0, limit]
}

/// Min of two bounded values - tighter postcondition
#[requires("limit >= 0")]
#[ensures("result >= 0")]
#[ensures("result <= limit")]
fn min_clamped(a: i32, b: i32, limit: i32) -> i32 {
    let x = clamp_positive(a, limit);  // 0 <= x <= limit
    let y = clamp_positive(b, limit);  // 0 <= y <= limit
    if x < y { x } else { y }  // min is also in [0, limit]
}

fn main() {
    // Test if-else propagation
    let _ = postcond_through_if_else(true, false);
    let _ = postcond_mixed_branches(true, true);

    // Test match propagation
    let _ = postcond_through_match(true, false, Choice::UseFirst);
    let _ = postcond_mixed_match_arms(true, Choice::UseBoth);

    // Test multiple postconditions
    let _ = relay_bounded(10);
    let _ = chained_bounded(10);

    // Test nested conditionals
    let _ = deep_nested_postcond(true, false, true);

    // Test loop body
    let _ = postcond_in_loop([true, false, true, false]);

    // Test combining postconditions
    let _ = pick_clamped(5, 10, 20, true);
    let _ = min_clamped(5, 10, 20);

    println!("All conditional postcondition propagation tests passed!");
}
