// Test BinaryHeap builtin contracts and mutation tracking (Phase 10.1)
//
// BinaryHeap<T> is modeled via `(len heap)`:
// - new/with_capacity: len == 0
// - len/is_empty: consistent with `(len heap)`
// - push/pop/clear: update tracked length
// - pop/peek: Option is_some iff len > 0 (before pop)

#![allow(unused)]

use std::collections::BinaryHeap;

// =============================================================================
// BinaryHeap::new()/with_capacity() tests - length is 0
// =============================================================================

#[ensures("result.len() == 0")]
fn binaryheap_new_len_zero() -> BinaryHeap<i32> {
    BinaryHeap::new()
}

#[ensures("result.is_empty()")]
fn binaryheap_new_is_empty() -> BinaryHeap<i32> {
    BinaryHeap::new()
}

#[ensures("result.len() == 0")]
fn binaryheap_with_capacity_len_zero() -> BinaryHeap<i32> {
    BinaryHeap::with_capacity(10)
}

// =============================================================================
// BinaryHeap::len()/capacity() tests
// =============================================================================

#[ensures("result >= 0")]
fn binaryheap_len_nonneg(h: BinaryHeap<i32>) -> usize {
    h.len()
}

#[ensures("result >= h.len()")]
fn binaryheap_capacity_ge_len(h: BinaryHeap<i32>) -> usize {
    h.capacity()
}

// =============================================================================
// BinaryHeap mutation tests - push/pop/clear update length
// =============================================================================

#[ensures("result.len() == 1")]
fn binaryheap_push_one() -> BinaryHeap<i32> {
    let mut h = BinaryHeap::new();
    h.push(10);
    h
}

#[ensures("result.len() == 2")]
fn binaryheap_push_two() -> BinaryHeap<i32> {
    let mut h = BinaryHeap::new();
    h.push(1);
    h.push(2);
    h
}

#[ensures("result.len() == 0")]
fn binaryheap_pop_to_empty() -> BinaryHeap<i32> {
    let mut h = BinaryHeap::new();
    h.push(10);
    h.pop();
    h
}

#[ensures("result.len() == 0")]
fn binaryheap_clear_len_zero() -> BinaryHeap<i32> {
    let mut h = BinaryHeap::new();
    h.push(1);
    h.push(2);
    h.clear();
    h
}

// =============================================================================
// BinaryHeap pop/peek Option tests
// =============================================================================

#[ensures("result.is_some()")]
fn binaryheap_pop_some_after_push() -> Option<i32> {
    let mut h = BinaryHeap::new();
    h.push(10);
    h.pop()
}

#[ensures("result.is_none()")]
fn binaryheap_pop_none_on_empty() -> Option<i32> {
    let mut h: BinaryHeap<i32> = BinaryHeap::new();
    h.pop()
}

#[ensures("result")]
fn binaryheap_peek_some_after_push() -> bool {
    let mut h: BinaryHeap<i32> = BinaryHeap::new();
    h.push(10);
    let p = h.peek();
    p.is_some()
}

#[ensures("result")]
fn binaryheap_peek_none_on_empty() -> bool {
    let h: BinaryHeap<i32> = BinaryHeap::new();
    let p = h.peek();
    p.is_none()
}

fn main() {
    let h = binaryheap_push_two();
    println!("BinaryHeap len after pushes: {}", h.len());
    println!("BinaryHeap pop_some_after_push: {:?}", binaryheap_pop_some_after_push());
    println!("BinaryHeap pop_none_on_empty: {:?}", binaryheap_pop_none_on_empty());
    println!("BinaryHeap peek_some_after_push: {}", binaryheap_peek_some_after_push());
    println!("BinaryHeap peek_none_on_empty: {}", binaryheap_peek_none_on_empty());
}
