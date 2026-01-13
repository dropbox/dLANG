//! Verified Stack - Real-World Verification Test
//!
//! A simple stack implementation with formal specifications.
//! This tests the verification infrastructure on real code patterns.

/// A simple fixed-capacity stack of integers
struct Stack {
    /// The underlying data storage
    data: [i32; 100],
    /// Current number of elements
    len: usize,
    /// Maximum capacity
    capacity: usize,
}

/// Create a new empty stack with given capacity
/// Note: We use a fixed array size of 100 for simplicity
// #[ensures(result.len == 0)]
// #[ensures(cap <= 100 && result.capacity == cap || cap > 100 && result.capacity == 100)]
fn new_stack(cap: usize) -> Stack {
    Stack {
        data: [0; 100],
        len: 0,
        capacity: if cap > 100 { 100 } else { cap },
    }
}

/// Check if the stack is empty
// #[pure]
// #[ensures(result == (self_len == 0))]
fn is_empty(self_len: usize) -> bool {
    self_len == 0
}

/// Check if the stack is full
// #[pure]
// #[ensures(result == (self_len >= self_capacity))]
fn is_full(self_len: usize, self_capacity: usize) -> bool {
    self_len >= self_capacity
}

/// Get the current length of the stack
// #[pure]
// #[ensures(result == self_len)]
fn len(self_len: usize) -> usize {
    self_len
}

/// Push an element onto the stack (returns new length)
/// Precondition: stack is not full
// #[requires(self_len < self_capacity)]
// #[ensures(result == self_len + 1)]
fn push(self_len: usize, self_capacity: usize, _x: i32) -> usize {
    if self_len < self_capacity {
        self_len + 1
    } else {
        self_len // Should not happen due to precondition
    }
}

/// Pop an element from the stack (returns new length)
/// Precondition: stack is not empty
// #[requires(self_len > 0)]
// #[ensures(result == self_len - 1)]
fn pop(self_len: usize) -> usize {
    if self_len > 0 {
        self_len - 1
    } else {
        0 // Should not happen due to precondition
    }
}

/// Get remaining capacity
// #[pure]
// #[ensures(self_capacity > self_len && result == self_capacity - self_len || self_capacity <= self_len && result == 0)]
fn remaining_capacity(self_len: usize, self_capacity: usize) -> usize {
    if self_capacity > self_len {
        self_capacity - self_len
    } else {
        0
    }
}

/// Simplified increment for testing modular verification
// #[ensures(result == x + 1)]
fn increment(x: i32) -> i32 {
    x + 1
}

/// Function that uses increment - tests modular verification
// #[ensures(result == x + 2)]
fn increment_twice(x: i32) -> i32 {
    let first = increment(x);
    increment(first)
}

/// Simple absolute value - tests conditionals
// #[pure]
// #[ensures(result >= 0)]
// #[ensures(x >= 0 && result == x || x < 0 && result == -x)]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

/// Safe subtraction - returns 0 if would underflow
// #[pure]
// #[ensures(a >= b && result == a - b || a < b && result == 0)]
fn safe_sub(a: usize, b: usize) -> usize {
    if a >= b { a - b } else { 0 }
}

/// Count down from n to 0 - tests loop with invariant
// #[requires(n >= 0)]
// #[ensures(result == 0)]
// #[invariant(i >= 0)]
fn count_down(n: i32) -> i32 {
    let mut i = n;
    while i > 0 {
        i = i - 1;
    }
    i
}

fn main() {
    // Test stack operations
    let stack = new_stack(10);
    println!("New stack - len: {}, capacity: {}", stack.len, stack.capacity);

    // Test pure functions
    println!("is_empty(0): {}", is_empty(0));
    println!("is_empty(5): {}", is_empty(5));
    println!("is_full(5, 10): {}", is_full(5, 10));
    println!("is_full(10, 10): {}", is_full(10, 10));

    // Test push/pop
    let new_len = push(5, 10, 42);
    println!("push(5, 10, 42) = {}", new_len);

    let new_len = pop(6);
    println!("pop(6) = {}", new_len);

    // Test remaining capacity
    println!("remaining_capacity(3, 10) = {}", remaining_capacity(3, 10));

    // Test modular verification
    println!("increment_twice(5) = {}", increment_twice(5));

    // Test abs
    println!("abs(-5) = {}", abs(-5));
    println!("abs(5) = {}", abs(5));

    // Test safe_sub
    println!("safe_sub(10, 3) = {}", safe_sub(10, 3));
    println!("safe_sub(3, 10) = {}", safe_sub(3, 10));

    // Test count_down
    println!("count_down(5) = {}", count_down(5));
}
