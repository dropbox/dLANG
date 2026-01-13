// Test extended Vec<T> method modeling (Phase 10.1)
//
// Tests Vec methods that are directly on Vec<T> (not via slice deref):
// - Vec::pop: is_some iff len > 0
// - Vec::capacity: result >= len(self)
//
// Note: Methods like get, first, last, contains are actually on slices,
// and the deref from Vec to slice creates a new temporary that complicates
// verification when the Vec comes from a function parameter.

// Vec::capacity() is non-negative
// VERIFIED
#[ensures("c >= 0")]
fn vec_capacity_nonnegative() -> usize {
    let v: Vec<i32> = Vec::new();
    let c = v.capacity();
    c
}

// Vec::pop() returns None when called on empty vec from Vec::new()
// VERIFIED
#[ensures("result.is_none()")]
fn vec_pop_new_empty() -> Option<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.pop()
}

// Vec::pop() returns Some when len > 0 (precondition)
// VERIFIED
#[requires("v.len() > 0")]
#[ensures("result.is_some()")]
fn vec_pop_nonempty(v: &mut Vec<i32>) -> Option<i32> {
    v.pop()
}

// Vec::pop() returns None when len == 0 (precondition)
// VERIFIED
#[requires("v.len() == 0")]
#[ensures("result.is_none()")]
fn vec_pop_empty(v: &mut Vec<i32>) -> Option<i32> {
    v.pop()
}

fn main() {
    // Test capacity
    assert!(vec_capacity_nonnegative() >= 0);

    // Test pop on empty
    assert!(vec_pop_new_empty().is_none());

    // Test pop on nonempty - use Vec::with_capacity + push to avoid vec! macro overflow warnings
    let mut nonempty: Vec<i32> = Vec::with_capacity(3);
    nonempty.push(1);
    nonempty.push(2);
    nonempty.push(3);
    assert!(vec_pop_nonempty(&mut nonempty).is_some());

    // Test pop on empty parameter
    let mut empty_mut: Vec<i32> = Vec::new();
    assert!(vec_pop_empty(&mut empty_mut).is_none());
}
