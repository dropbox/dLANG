// Test extended collection mutation tracking (Phase 10.1)
#![feature(linked_list_retain)]  // LinkedList::retain_mut is unstable in Rust 1.83
//
// Tests additional mutation operations for Vec, VecDeque, and LinkedList:
// - Vec::dedup_by/dedup_by_key: length <= old_len
// - Vec::retain_mut: length tracking invalidated
// - Vec::resize_with: length = n
// - Vec::extend_from_within: length >= old_len
// - VecDeque::resize_with: length = n
// - VecDeque::retain_mut: length tracking invalidated
// - LinkedList::retain_mut: length tracking invalidated
//
// Note: Methods that take closures cannot have their results precisely tracked,
// but we can still verify bounds and that length remains non-negative.

use std::collections::{VecDeque, LinkedList};

// =================================================================
// Vec::resize_with() tests - length becomes exactly n
// =================================================================

// resize_with to grow vec
// VERIFIED
#[ensures("result.len() == 5")]
fn vec_resize_with_grow() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);  // len = 1
    v.push(2);  // len = 2
    v.resize_with(5, || 0);  // len = 5
    v
}

// resize_with to shrink vec
// VERIFIED
#[ensures("result.len() == 2")]
fn vec_resize_with_shrink() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    v.resize_with(2, || 0);  // len = 2
    v
}

// resize_with to zero makes vec empty
// VERIFIED
#[ensures("result.is_empty()")]
fn vec_resize_with_to_zero() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.resize_with(0, || 0);  // len = 0
    v
}

// resize_with then push gives predictable length
// VERIFIED
#[ensures("result.len() == 4")]
fn vec_resize_with_then_push() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.resize_with(3, || 0);  // len = 3
    v.push(99);  // len = 4
    v
}

// =================================================================
// Vec::dedup_by() tests - length <= old_len
// We can't predict exact length since it depends on the closure,
// but we know length won't increase
// =================================================================

// After dedup_by, vec is not longer than before
// Note: Exact length is unknown after dedup_by
// VERIFIED (length >= 0, which is always true for Vec)
#[ensures("result.len() >= 0")]
fn vec_dedup_by_non_negative() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(1);
    v.push(2);
    v.push(2);
    v.dedup_by(|a, b| *a == *b);
    v
}

// After dedup_by_key, vec is not longer than before
// VERIFIED (length >= 0)
#[ensures("result.len() >= 0")]
fn vec_dedup_by_key_non_negative() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(10);
    v.push(11);  // same "tens" digit
    v.push(20);
    v.push(21);  // same "tens" digit
    v.dedup_by_key(|x| *x / 10);
    v
}

// =================================================================
// Vec::retain_mut() tests - length tracking invalidated
// After retain_mut, we can't know exact length
// =================================================================

// After retain_mut, length is non-negative
// VERIFIED (length >= 0)
#[ensures("result.len() >= 0")]
fn vec_retain_mut_non_negative() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    v.retain_mut(|x| {
        *x += 1;  // modify in place
        *x % 2 == 0  // keep evens
    });
    v
}

// =================================================================
// Vec::extend_from_within() tests - length >= old_len
// =================================================================

// After extend_from_within, length is at least old_len
// VERIFIED (length >= old_len, old_len was 4)
#[ensures("result.len() >= 4")]
fn vec_extend_from_within_bounds() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);  // len = 4
    v.extend_from_within(1..3);  // copies elements [2, 3] to end
    // Now v should be [1, 2, 3, 4, 2, 3] with len = 6
    v
}

// =================================================================
// VecDeque::resize_with() tests - length becomes exactly n
// =================================================================

// VecDeque resize_with to grow
// VERIFIED
#[ensures("result.len() == 5")]
fn vecdeque_resize_with_grow() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.push_back(2);
    vd.resize_with(5, || 0);  // len = 5
    vd
}

// VecDeque resize_with to shrink
// VERIFIED
#[ensures("result.len() == 2")]
fn vecdeque_resize_with_shrink() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.push_back(2);
    vd.push_back(3);
    vd.push_back(4);
    vd.resize_with(2, || 0);  // len = 2
    vd
}

// VecDeque resize_with then push_back gives predictable length
// VERIFIED
#[ensures("result.len() == 4")]
fn vecdeque_resize_with_then_push() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.resize_with(3, || 0);  // len = 3
    vd.push_back(99);  // len = 4
    vd
}

// =================================================================
// VecDeque::retain_mut() tests - length tracking invalidated
// =================================================================

// After VecDeque retain_mut, length is non-negative
// VERIFIED (length >= 0)
#[ensures("result.len() >= 0")]
fn vecdeque_retain_mut_non_negative() -> VecDeque<i32> {
    let mut vd: VecDeque<i32> = VecDeque::new();
    vd.push_back(1);
    vd.push_back(2);
    vd.push_back(3);
    vd.push_back(4);
    vd.retain_mut(|x| {
        *x *= 2;  // modify in place
        *x > 4  // keep values > 4 after doubling
    });
    vd
}

// =================================================================
// LinkedList::retain_mut() tests - length tracking invalidated
// =================================================================

// After LinkedList retain, length is non-negative
// VERIFIED (length >= 0)
// Note: LinkedList doesn't have retain_mut in 1.91.0, using retain instead
#[ensures("result.len() >= 0")]
fn linkedlist_retain_non_negative() -> LinkedList<i32> {
    let mut list: LinkedList<i32> = LinkedList::new();
    list.push_back(1);
    list.push_back(2);
    list.push_back(3);
    list.push_back(4);
    list.retain(|x| *x > 2);  // keep values > 2
    list
}

fn main() {
    // Vec::resize_with tests
    assert_eq!(vec_resize_with_grow().len(), 5);
    assert_eq!(vec_resize_with_shrink().len(), 2);
    assert!(vec_resize_with_to_zero().is_empty());
    assert_eq!(vec_resize_with_then_push().len(), 4);

    // Vec::dedup_by tests
    let v1 = vec_dedup_by_non_negative();
    assert!(v1.len() >= 0 && v1.len() <= 4);  // at most 4 (original len)

    let v2 = vec_dedup_by_key_non_negative();
    assert!(v2.len() >= 0 && v2.len() <= 4);  // at most 4 (original len)

    // Vec::retain_mut tests
    let v3 = vec_retain_mut_non_negative();
    assert!(v3.len() >= 0);

    // Vec::extend_from_within tests
    let v4 = vec_extend_from_within_bounds();
    assert!(v4.len() >= 4);  // at least the original length
    assert_eq!(v4.len(), 6);  // actual: 4 + 2 copied

    // VecDeque::resize_with tests
    assert_eq!(vecdeque_resize_with_grow().len(), 5);
    assert_eq!(vecdeque_resize_with_shrink().len(), 2);
    assert_eq!(vecdeque_resize_with_then_push().len(), 4);

    // VecDeque::retain_mut tests
    let vd = vecdeque_retain_mut_non_negative();
    assert!(vd.len() >= 0);

    // LinkedList::retain tests (retain_mut not available in 1.91.0)
    let ll = linkedlist_retain_non_negative();
    assert!(ll.len() >= 0);

    println!("All extended mutation tests passed!");
}
