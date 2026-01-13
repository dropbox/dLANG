// Test VecDeque builtin contracts and mutation tracking (Phase 10.1)
//
// Tests that VecDeque operations properly update tracked lengths:
// - new/with_capacity: length = 0
// - push_front/push_back: length increases by 1
// - pop_front/pop_back: length decreases by 1 (if non-empty)
// - clear: length = 0
// - truncate: length = min(current, new_len)
// - resize: length = new_len
// - append: self length += other length, other length = 0
//
// VecDeque is a double-ended queue supporting O(1) operations at both ends.

#![allow(unused)]

use std::collections::VecDeque;

// =============================================================================
// VecDeque::new() tests - length is 0
// =============================================================================

// After new, length is 0
// VERIFIED
#[ensures("result.len() == 0")]
fn vecdeque_new_len_zero() -> VecDeque<i32> {
    VecDeque::new()
}

// After new, is_empty is true
// VERIFIED
#[ensures("result.is_empty()")]
fn vecdeque_new_is_empty() -> VecDeque<i32> {
    VecDeque::new()
}

// =============================================================================
// VecDeque::with_capacity() tests - length is 0
// =============================================================================

// After with_capacity, length is 0
// VERIFIED
#[ensures("result.len() == 0")]
fn vecdeque_with_capacity_len_zero() -> VecDeque<i32> {
    VecDeque::with_capacity(10)
}

// After with_capacity, is_empty is true
// VERIFIED
#[ensures("result.is_empty()")]
fn vecdeque_with_capacity_is_empty() -> VecDeque<i32> {
    VecDeque::with_capacity(10)
}

// =============================================================================
// VecDeque::push_back() tests - length increases by 1
// =============================================================================

// After push_back on empty, length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vecdeque_push_back_one() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(10);
    vd
}

// After push_back, not empty
// VERIFIED
#[ensures("!result.is_empty()")]
fn vecdeque_push_back_not_empty() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(42);
    vd
}

// After two push_back, length is 2
// VERIFIED
#[ensures("result.len() == 2")]
fn vecdeque_push_back_two() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.push_back(2);
    vd
}

// After three push_back, length is 3
// VERIFIED
#[ensures("result.len() == 3")]
fn vecdeque_push_back_three() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.push_back(2);
    vd.push_back(3);
    vd
}

// =============================================================================
// VecDeque::push_front() tests - length increases by 1
// =============================================================================

// After push_front on empty, length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vecdeque_push_front_one() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_front(10);
    vd
}

// After push_front, not empty
// VERIFIED
#[ensures("!result.is_empty()")]
fn vecdeque_push_front_not_empty() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_front(42);
    vd
}

// After two push_front, length is 2
// VERIFIED
#[ensures("result.len() == 2")]
fn vecdeque_push_front_two() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_front(1);
    vd.push_front(2);
    vd
}

// =============================================================================
// Mixed push_front and push_back tests
// =============================================================================

// After push_front and push_back, length is 2
// VERIFIED
#[ensures("result.len() == 2")]
fn vecdeque_push_front_and_back() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_front(1);
    vd.push_back(2);
    vd
}

// After alternating pushes, length is 4
// VERIFIED
#[ensures("result.len() == 4")]
fn vecdeque_alternating_pushes() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_front(1);
    vd.push_back(2);
    vd.push_front(3);
    vd.push_back(4);
    vd
}

// =============================================================================
// VecDeque::clear() tests - length becomes 0
// =============================================================================

// After clear, length is 0
// VERIFIED
#[ensures("result.len() == 0")]
fn vecdeque_clear_len_zero() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.push_back(2);
    vd.push_front(3);
    vd.clear();
    vd
}

// After clear, is_empty is true
// VERIFIED
#[ensures("result.is_empty()")]
fn vecdeque_clear_is_empty() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.clear();
    vd
}

// =============================================================================
// VecDeque::pop_back() tests - length decreases by 1 if non-empty
// =============================================================================

// After push then pop_back, length is 0
// VERIFIED
#[ensures("result.len() == 0")]
fn vecdeque_pop_back_to_empty() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(10);
    vd.pop_back();
    vd
}

// After two pushes then one pop_back, length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vecdeque_pop_back_one() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.push_back(2);
    vd.pop_back();
    vd
}

// =============================================================================
// VecDeque::pop_front() tests - length decreases by 1 if non-empty
// =============================================================================

// After push then pop_front, length is 0
// VERIFIED
#[ensures("result.len() == 0")]
fn vecdeque_pop_front_to_empty() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(10);
    vd.pop_front();
    vd
}

// After two pushes then one pop_front, length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vecdeque_pop_front_one() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_front(1);
    vd.push_front(2);
    vd.pop_front();
    vd
}

// =============================================================================
// Combined push and pop tests
// =============================================================================

// Push 3, pop 2, length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vecdeque_push_pop_combined() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.push_back(2);
    vd.push_back(3);
    vd.pop_front();
    vd.pop_back();
    vd
}

// Push front and back, pop front and back
// VERIFIED
#[ensures("result.len() == 2")]
fn vecdeque_mixed_operations() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_front(1);  // len = 1
    vd.push_back(2);   // len = 2
    vd.push_front(3);  // len = 3
    vd.pop_back();     // len = 2
    vd
}

// =============================================================================
// Clear then push tests
// =============================================================================

// Clear then push: length is 1
// VERIFIED
#[ensures("result.len() == 1")]
fn vecdeque_clear_then_push() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.push_back(2);
    vd.clear();
    vd.push_back(3);
    vd
}

// Clear then push_front: not empty
// VERIFIED
#[ensures("!result.is_empty()")]
fn vecdeque_clear_then_push_front() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.clear();
    vd.push_front(2);
    vd
}

fn main() {
    // new() tests
    assert_eq!(vecdeque_new_len_zero().len(), 0);
    assert!(vecdeque_new_is_empty().is_empty());

    // with_capacity() tests
    assert_eq!(vecdeque_with_capacity_len_zero().len(), 0);
    assert!(vecdeque_with_capacity_is_empty().is_empty());

    // push_back() tests
    assert_eq!(vecdeque_push_back_one().len(), 1);
    assert!(!vecdeque_push_back_not_empty().is_empty());
    assert_eq!(vecdeque_push_back_two().len(), 2);
    assert_eq!(vecdeque_push_back_three().len(), 3);

    // push_front() tests
    assert_eq!(vecdeque_push_front_one().len(), 1);
    assert!(!vecdeque_push_front_not_empty().is_empty());
    assert_eq!(vecdeque_push_front_two().len(), 2);

    // Mixed push tests
    assert_eq!(vecdeque_push_front_and_back().len(), 2);
    assert_eq!(vecdeque_alternating_pushes().len(), 4);

    // clear() tests
    assert_eq!(vecdeque_clear_len_zero().len(), 0);
    assert!(vecdeque_clear_is_empty().is_empty());

    // pop_back() tests
    assert_eq!(vecdeque_pop_back_to_empty().len(), 0);
    assert_eq!(vecdeque_pop_back_one().len(), 1);

    // pop_front() tests
    assert_eq!(vecdeque_pop_front_to_empty().len(), 0);
    assert_eq!(vecdeque_pop_front_one().len(), 1);

    // Combined tests
    assert_eq!(vecdeque_push_pop_combined().len(), 1);
    assert_eq!(vecdeque_mixed_operations().len(), 2);

    // Clear then push tests
    assert_eq!(vecdeque_clear_then_push().len(), 1);
    assert!(!vecdeque_clear_then_push_front().is_empty());

    println!("All VecDeque tests passed at runtime!");
}
