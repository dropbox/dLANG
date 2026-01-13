//! Integration test for ghost variables (Phase 11.4)
//!
//! Ghost variables allow tracking logical state across mutations.
//! They exist only for verification and have no runtime effect.
//!
//! Syntax:
//!   #[ghost(name = expr)]  -- declares ghost variable `name` bound to `expr` at entry
//!
//! Convenience patterns (expand to old() expressions):
//!   ghost_len(x)           -- expands to old(x.len())
//!   ghost_is_some(x)       -- expands to old(x.is_some())
//!   ghost_contains(x, v)   -- expands to old(x.contains(&v))

#![feature(register_tool)]
#![register_tool(trust)]

// ============================================================================
// Part 1: Ghost variable binding syntax
// ============================================================================

/// Test basic ghost variable declaration
/// The ghost variable `initial_len` captures vec.len() at function entry
#[trust::requires(vec.len() < 100)]
#[trust::ghost(initial_len = vec.len())]
#[trust::ensures(vec.len() == initial_len + 1)]
fn push_with_ghost(vec: &mut Vec<i32>, item: i32) {
    vec.push(item);
}

/// Test multiple ghost variables
#[trust::requires(a.len() > 0 && b.len() > 0)]
#[trust::ghost(a_len = a.len())]
#[trust::ghost(b_len = b.len())]
#[trust::ensures(a.len() == a_len - 1)]
#[trust::ensures(b.len() == b_len + 1)]
fn transfer_last(a: &mut Vec<i32>, b: &mut Vec<i32>) {
    if let Some(item) = a.pop() {
        b.push(item);
    }
}

/// Test ghost with Option tracking
#[trust::ghost(was_some = opt.is_some())]
#[trust::ensures(was_some ==> opt.is_none())]
fn take_option(opt: &mut Option<i32>) -> Option<i32> {
    opt.take()
}

// ============================================================================
// Part 2: Convenience ghost functions (syntactic sugar)
// ============================================================================

/// ghost_len(x) expands to old(x.len())
#[trust::requires(vec.len() < 100)]
#[trust::ensures(vec.len() == ghost_len(vec) + 1)]
fn push_with_ghost_len(vec: &mut Vec<i32>, item: i32) {
    vec.push(item);
}

/// ghost_is_some(x) expands to old(x.is_some())
#[trust::ensures(ghost_is_some(opt) ==> result.is_some())]
fn take_with_ghost_is_some(opt: &mut Option<i32>) -> Option<i32> {
    opt.take()
}

// ============================================================================
// Part 3: Test ghost variables across non-trivial mutations
// ============================================================================

/// Swap and verify both sides changed
#[trust::requires(a.is_some() && b.is_some())]
#[trust::ghost(old_a = a.is_some())]
#[trust::ghost(old_b = b.is_some())]
#[trust::ensures(a.is_some() && b.is_some())]  // Both still Some after swap
fn swap_options(a: &mut Option<i32>, b: &mut Option<i32>) {
    std::mem::swap(a, b);
}

/// Track multiple state changes in sequence
#[trust::requires(vec.len() >= 2)]
#[trust::ghost(len_at_start = vec.len())]
#[trust::ensures(vec.len() == len_at_start)]  // Same length after rotation
fn rotate_first_two(vec: &mut Vec<i32>) {
    if vec.len() >= 2 {
        vec.swap(0, 1);
    }
}

fn main() {
    // Test push_with_ghost
    let mut v = vec![1, 2, 3];
    push_with_ghost(&mut v, 4);
    assert_eq!(v.len(), 4);

    // Test transfer_last
    let mut a = vec![1, 2, 3];
    let mut b = vec![10];
    transfer_last(&mut a, &mut b);
    assert_eq!(a.len(), 2);
    assert_eq!(b.len(), 2);

    // Test take_option
    let mut opt = Some(42);
    let taken = take_option(&mut opt);
    assert_eq!(taken, Some(42));
    assert!(opt.is_none());

    // Test ghost_len convenience
    let mut v2 = vec![1];
    push_with_ghost_len(&mut v2, 2);
    assert_eq!(v2.len(), 2);

    // Test ghost_is_some convenience
    let mut opt2 = Some(100);
    let taken2 = take_with_ghost_is_some(&mut opt2);
    assert_eq!(taken2, Some(100));

    // Test swap_options
    let mut opt_a = Some(1);
    let mut opt_b = Some(2);
    swap_options(&mut opt_a, &mut opt_b);
    assert_eq!(opt_a, Some(2));
    assert_eq!(opt_b, Some(1));

    // Test rotate_first_two
    let mut v3 = vec![1, 2, 3];
    rotate_first_two(&mut v3);
    assert_eq!(v3, vec![2, 1, 3]);

    println!("All ghost variable tests passed!");
}
