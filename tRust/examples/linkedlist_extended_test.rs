// Test LinkedList extended mutation tracking (Phase 10.1)
//
// LinkedList::split_off(at) splits the list at index `at`:
// - self's length becomes `at` (keeps [0, at))
// - returned list has length (old_len - at) (contains [at, end))

#![allow(unused)]

use std::collections::LinkedList;

// =============================================================================
// LinkedList::split_off() tests - self's length becomes `at`
// =============================================================================

// split_off at 0: self becomes empty, result has all elements
#[ensures("result.len() == 0")]
fn linkedlist_split_off_at_zero() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.push_back(3);

    let _tail = l.split_off(0);
    l
}

// split_off at 1: self has 1 element
#[ensures("result.len() == 1")]
fn linkedlist_split_off_at_one() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.push_back(3);

    let _tail = l.split_off(1);
    l
}

// split_off at 2: self has 2 elements
#[ensures("result.len() == 2")]
fn linkedlist_split_off_at_two() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.push_back(3);

    let _tail = l.split_off(2);
    l
}

// split_off at len: self keeps all, result is empty
#[ensures("result.len() == 3")]
fn linkedlist_split_off_at_len() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.push_back(3);

    let _tail = l.split_off(3);
    l
}

// =============================================================================
// split_off returned list tests
// =============================================================================

// The returned list has len >= 0 (conservative postcondition)
#[ensures("result.len() >= 0")]
fn linkedlist_split_off_result_nonneg() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.push_back(3);

    l.split_off(1)
}

// =============================================================================
// split_off combined with other operations
// =============================================================================

// split_off then push to self
#[ensures("result.len() == 2")]
fn linkedlist_split_off_then_push() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.push_back(3);

    let _tail = l.split_off(1);
    l.push_back(100);
    l
}

// split_off then append
#[ensures("result.len() == 3")]
fn linkedlist_split_off_then_append() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.push_back(3);

    let _tail = l.split_off(1);
    // l now has len = 1

    let mut other = LinkedList::new();
    other.push_back(10);
    other.push_back(20);

    l.append(&mut other);
    // l now has len = 1 + 2 = 3
    l
}

// split_off then clear
#[ensures("result.len() == 0")]
fn linkedlist_split_off_then_clear() -> LinkedList<i32> {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);
    l.push_back(3);

    let _tail = l.split_off(2);
    l.clear();
    l
}

// =============================================================================
// split_off with front/back Option tests
// =============================================================================

// After split_off at 0, self is empty, so front() is None
#[ensures("result")]
fn linkedlist_split_off_zero_front_none() -> bool {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);

    let _tail = l.split_off(0);
    l.front().is_none()
}

// After split_off at 1, self has 1 element, so front() is Some
#[ensures("result")]
fn linkedlist_split_off_one_front_some() -> bool {
    let mut l = LinkedList::new();
    l.push_back(1);
    l.push_back(2);

    let _tail = l.split_off(1);
    l.front().is_some()
}

fn main() {
    let l = linkedlist_split_off_at_one();
    println!("LinkedList after split_off(1): {}", l.len());

    let l2 = linkedlist_split_off_then_push();
    println!("LinkedList after split_off + push: {}", l2.len());

    let l3 = linkedlist_split_off_then_append();
    println!("LinkedList after split_off + append: {}", l3.len());

    println!("split_off(0) front none: {}", linkedlist_split_off_zero_front_none());
    println!("split_off(1) front some: {}", linkedlist_split_off_one_front_some());
}
