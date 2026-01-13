// Test BinaryHeap extended mutation tracking (Phase 10.1)
//
// BinaryHeap::append moves all elements from another heap:
// - self's length increases by other's length
// - other becomes empty (len == 0)

#![allow(unused)]

use std::collections::BinaryHeap;

// =============================================================================
// BinaryHeap::append() tests - length tracking
// =============================================================================

// Test that appending two heaps combines their lengths
#[ensures("result.len() == 3")]
fn binaryheap_append_sum_lengths() -> BinaryHeap<i32> {
    let mut h1 = BinaryHeap::new();
    h1.push(1);

    let mut h2 = BinaryHeap::new();
    h2.push(2);
    h2.push(3);

    h1.append(&mut h2);
    h1
}

// Test that appending to empty heap gives other's length
#[ensures("result.len() == 2")]
fn binaryheap_append_to_empty() -> BinaryHeap<i32> {
    let mut h1: BinaryHeap<i32> = BinaryHeap::new();

    let mut h2 = BinaryHeap::new();
    h2.push(10);
    h2.push(20);

    h1.append(&mut h2);
    h1
}

// Test that appending empty heap doesn't change length
#[ensures("result.len() == 2")]
fn binaryheap_append_empty() -> BinaryHeap<i32> {
    let mut h1 = BinaryHeap::new();
    h1.push(1);
    h1.push(2);

    let mut h2: BinaryHeap<i32> = BinaryHeap::new();

    h1.append(&mut h2);
    h1
}

// Test that source heap becomes empty after append
// Note: We return the source heap to verify it's empty
#[ensures("result.len() == 0")]
fn binaryheap_append_source_empty() -> BinaryHeap<i32> {
    let mut h1 = BinaryHeap::new();
    h1.push(1);

    let mut h2 = BinaryHeap::new();
    h2.push(2);
    h2.push(3);

    h1.append(&mut h2);
    // h2 should now be empty
    h2
}

// =============================================================================
// Append combined with other operations
// =============================================================================

// Append then push
#[ensures("result.len() == 4")]
fn binaryheap_append_then_push() -> BinaryHeap<i32> {
    let mut h1 = BinaryHeap::new();
    h1.push(1);

    let mut h2 = BinaryHeap::new();
    h2.push(2);
    h2.push(3);

    h1.append(&mut h2);
    h1.push(4);
    h1
}

// Append then pop
#[ensures("result.len() == 2")]
fn binaryheap_append_then_pop() -> BinaryHeap<i32> {
    let mut h1 = BinaryHeap::new();
    h1.push(1);

    let mut h2 = BinaryHeap::new();
    h2.push(2);
    h2.push(3);

    h1.append(&mut h2);
    h1.pop();
    h1
}

// Multiple appends
#[ensures("result.len() == 6")]
fn binaryheap_multiple_appends() -> BinaryHeap<i32> {
    let mut h1 = BinaryHeap::new();
    h1.push(1);

    let mut h2 = BinaryHeap::new();
    h2.push(2);
    h2.push(3);

    let mut h3 = BinaryHeap::new();
    h3.push(4);
    h3.push(5);
    h3.push(6);

    h1.append(&mut h2);
    h1.append(&mut h3);
    h1
}

// Append after clear
#[ensures("result.len() == 2")]
fn binaryheap_clear_then_append() -> BinaryHeap<i32> {
    let mut h1 = BinaryHeap::new();
    h1.push(1);
    h1.push(2);
    h1.clear();

    let mut h2 = BinaryHeap::new();
    h2.push(3);
    h2.push(4);

    h1.append(&mut h2);
    h1
}

// =============================================================================
// Append with peek/pop
// =============================================================================

// After append, peek should return Some (combined heap non-empty)
#[ensures("result")]
fn binaryheap_append_then_peek_some() -> bool {
    let mut h1: BinaryHeap<i32> = BinaryHeap::new();

    let mut h2 = BinaryHeap::new();
    h2.push(10);

    h1.append(&mut h2);
    h1.peek().is_some()
}

// After appending two empty heaps, peek returns None
#[ensures("result")]
fn binaryheap_append_empty_then_peek_none() -> bool {
    let mut h1: BinaryHeap<i32> = BinaryHeap::new();
    let mut h2: BinaryHeap<i32> = BinaryHeap::new();

    h1.append(&mut h2);
    h1.peek().is_none()
}

fn main() {
    let h = binaryheap_append_sum_lengths();
    println!("BinaryHeap after append (sum): {}", h.len());

    let h2 = binaryheap_append_then_push();
    println!("BinaryHeap after append+push: {}", h2.len());

    let h3 = binaryheap_multiple_appends();
    println!("BinaryHeap after multiple appends: {}", h3.len());

    println!("Append then peek some: {}", binaryheap_append_then_peek_some());
    println!("Append empty then peek none: {}", binaryheap_append_empty_then_peek_none());
}
