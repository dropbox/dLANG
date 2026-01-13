// Test LinkedList builtin contracts and mutation tracking (Phase 10.1)
//
// LinkedList<T> is modeled via `(len list)`:
// - new: len == 0
// - len/is_empty: consistent with `(len list)`
// - push_front/push_back/pop_front/pop_back/clear/append: update tracked length
// - pop_*/front/back: Option is_some iff len > 0 (before pop)

#![allow(unused)]

use std::collections::LinkedList;

// =============================================================================
// LinkedList::new() tests - length is 0
// =============================================================================

#[ensures("result.len() == 0")]
fn linkedlist_new_len_zero() -> LinkedList<i32> {
    LinkedList::new()
}

#[ensures("result.is_empty()")]
fn linkedlist_new_is_empty() -> LinkedList<i32> {
    LinkedList::new()
}

// =============================================================================
// LinkedList push tests - length increases by 1
// =============================================================================

#[ensures("result.len() == 1")]
fn linkedlist_push_front_one() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_front(10);
    l
}

#[ensures("result.len() == 1")]
fn linkedlist_push_back_one() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(10);
    l
}

#[ensures("result.len() == 2")]
fn linkedlist_push_front_and_back_two() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_front(1);
    l.push_back(2);
    l
}

// =============================================================================
// LinkedList pop tests - length decreases by 1 if non-empty
// =============================================================================

#[ensures("result.len() == 0")]
fn linkedlist_pop_front_to_empty() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(10);
    l.pop_front();
    l
}

#[ensures("result.len() == 1")]
fn linkedlist_pop_back_one_remaining() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.pop_back();
    l
}

// =============================================================================
// LinkedList clear/append tests
// =============================================================================

#[ensures("result.len() == 0")]
fn linkedlist_clear_len_zero() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.clear();
    l
}

// NOTE: append() generates internal loops that require invariants.
// Since we can't add invariants to library code, this function is not verified.
fn linkedlist_append_len_sum() -> LinkedList<i32> {
    let mut a = LinkedList::new();
    a.push_back(1);

    let mut b = LinkedList::new();
    b.push_back(2);
    b.push_back(3);

    a.append(&mut b);
    a
}

// =============================================================================
// LinkedList pop/front/back Option tests
// =============================================================================

#[ensures("result.is_some()")]
fn linkedlist_pop_front_some_after_push() -> Option<i32> {
    let mut l = LinkedList::new();
    l.push_back(10);
    l.pop_front()
}

#[ensures("result.is_none()")]
fn linkedlist_pop_back_none_on_empty() -> Option<i32> {
    let mut l: LinkedList<i32> = LinkedList::new();
    l.pop_back()
}

#[ensures("result")]
fn linkedlist_front_some_after_push() -> bool {
    let mut l: LinkedList<i32> = LinkedList::new();
    l.push_back(10);
    l.front().is_some()
}

#[ensures("result")]
fn linkedlist_back_none_on_empty() -> bool {
    let l: LinkedList<i32> = LinkedList::new();
    let b = l.back();
    b.is_none()
}

fn main() {
    let l = linkedlist_append_len_sum();
    println!("LinkedList len after append: {}", l.len());
    println!("LinkedList pop_front_some_after_push: {:?}", linkedlist_pop_front_some_after_push());
    println!("LinkedList pop_back_none_on_empty: {:?}", linkedlist_pop_back_none_on_empty());
    println!("LinkedList front_some_after_push: {}", linkedlist_front_some_after_push());
    println!("LinkedList back_none_on_empty: {}", linkedlist_back_none_on_empty());
}
