// Test BinaryHeap::retain mutation tracking (Phase 10.1)
//
// BinaryHeap::retain(&mut self, f): filters elements by predicate
// - Length may decrease (we can't predict by how much)
// - Length tracking is invalidated (closure filter)
// - After retain, we can only assert len >= 0

#![allow(unused)]

use std::collections::BinaryHeap;

// =============================================================================
// BinaryHeap::retain() basic tests - length tracking invalidation
// =============================================================================

// After retain, length is non-negative (conservative bound)
#[ensures("result >= 0")]
fn binaryheap_retain_nonnegative_len() -> usize {
    let mut heap = BinaryHeap::from([1, 2, 3, 4, 5]);
    heap.retain(|&x| x > 2);
    heap.len()
}

// Retain that keeps all elements
#[ensures("result >= 0")]
fn binaryheap_retain_all() -> usize {
    let mut heap = BinaryHeap::from([1, 2, 3]);
    heap.retain(|_| true);
    heap.len()
}

// Retain that removes all elements
#[ensures("result >= 0")]
fn binaryheap_retain_none() -> usize {
    let mut heap = BinaryHeap::from([1, 2, 3]);
    heap.retain(|_| false);
    heap.len()
}

// Retain on empty heap
#[ensures("result >= 0")]
fn binaryheap_retain_empty() -> usize {
    let mut heap: BinaryHeap<i32> = BinaryHeap::new();
    heap.retain(|_| true);
    heap.len()
}

// =============================================================================
// BinaryHeap::retain() combined with other operations
// =============================================================================

// Retain then push restores tracking
#[ensures("result >= 1")]
fn binaryheap_retain_then_push() -> usize {
    let mut heap = BinaryHeap::from([1, 2, 3, 4, 5]);
    heap.retain(|&x| x % 2 == 0);
    // After retain, length is invalidated, but push adds 1
    heap.push(100);
    heap.len()
}

// Push then retain invalidates tracking
#[ensures("result >= 0")]
fn binaryheap_push_then_retain() -> usize {
    let mut heap = BinaryHeap::new();
    heap.push(1);
    heap.push(2);
    heap.push(3);
    heap.retain(|&x| x > 1);
    heap.len()
}

// Retain then pop
#[ensures("result >= 0")]
fn binaryheap_retain_then_pop() -> usize {
    let mut heap = BinaryHeap::from([1, 2, 3, 4, 5]);
    heap.retain(|&x| x > 2);
    heap.pop();
    heap.len()
}

// Retain then clear
#[ensures("result == 0")]
fn binaryheap_retain_then_clear() -> usize {
    let mut heap = BinaryHeap::from([1, 2, 3, 4, 5]);
    heap.retain(|&x| x > 2);
    heap.clear();
    heap.len()
}

// Multiple retains
#[ensures("result >= 0")]
fn binaryheap_multiple_retains() -> usize {
    let mut heap = BinaryHeap::from([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    heap.retain(|&x| x > 3);
    heap.retain(|&x| x < 8);
    heap.len()
}

// Retain then append
#[ensures("result >= 2")]
fn binaryheap_retain_then_append() -> usize {
    let mut h1 = BinaryHeap::from([1, 2, 3, 4, 5]);
    h1.retain(|&x| x > 2);

    let mut h2 = BinaryHeap::new();
    h2.push(10);
    h2.push(20);

    h1.append(&mut h2);
    // After retain, h1's length is unknown
    // After append, h1's length is (unknown + 2)
    // We can only say it's >= h2's original length
    h1.len()
}

// =============================================================================
// Heap operations preserve validity
// =============================================================================

// After retain, peek may return Some or None
#[ensures("result == true || result == false")]
fn binaryheap_retain_then_peek() -> bool {
    let mut heap = BinaryHeap::from([1, 2, 3, 4, 5]);
    heap.retain(|&x| x > 10); // removes all
    heap.peek().is_some()
}

// Empty check after retain
#[ensures("result == true || result == false")]
fn binaryheap_retain_is_empty_check() -> bool {
    let mut heap = BinaryHeap::from([1, 2, 3]);
    heap.retain(|&x| x > 5);
    heap.is_empty()
}

fn main() {
    println!("BinaryHeap retain tests");

    println!("retain keep some: {}", binaryheap_retain_nonnegative_len());
    println!("retain all: {}", binaryheap_retain_all());
    println!("retain none: {}", binaryheap_retain_none());
    println!("retain empty: {}", binaryheap_retain_empty());
    println!("retain then push: {}", binaryheap_retain_then_push());
    println!("push then retain: {}", binaryheap_push_then_retain());
    println!("retain then pop: {}", binaryheap_retain_then_pop());
    println!("retain then clear: {}", binaryheap_retain_then_clear());
    println!("multiple retains: {}", binaryheap_multiple_retains());
    println!("retain then append: {}", binaryheap_retain_then_append());
    println!("retain then peek: {}", binaryheap_retain_then_peek());
    println!("retain is_empty: {}", binaryheap_retain_is_empty_check());
}
