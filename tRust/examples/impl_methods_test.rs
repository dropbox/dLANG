//! Example: Specs on methods inside impl blocks
//!
//! This demonstrates verification of methods with #[requires] and #[ensures]
//! attributes. The tRust compiler parses these at compile time.
//!
//! Expected outcomes:
//! Counter::new: @expect: VERIFIED
//! Counter::increment: @expect: VERIFIED
//! Counter::add_positive: @expect: VERIFIED
//! Counter::clamp_to_zero: @expect: VERIFIED

#![allow(dead_code)]

struct Counter {
    value: i32,
}

impl Counter {
    /// Create a new counter with the given initial value
    #[requires("initial >= 0")]
    #[ensures("result == initial")]
    fn new(initial: i32) -> i32 {
        initial
    }

    /// Increment a value (with overflow protection)
    #[requires("n >= 0 && n < 2147483647")]
    #[ensures("result == n + 1")]
    fn increment(&self, n: i32) -> i32 {
        n + 1
    }

    /// Add two positive numbers (with overflow protection)
    #[requires("x > 0 && y > 0 && x < 1073741823 && y < 1073741823")]
    #[ensures("result == x + y")]
    fn add_positive(&self, x: i32, y: i32) -> i32 {
        x + y
    }

    /// Clamp a value to a minimum of zero
    #[requires("n >= -100")]
    #[ensures("result >= 0")]
    fn clamp_to_zero(&self, n: i32) -> i32 {
        if n < 0 { 0 } else { n }
    }
}

fn main() {
    let counter = Counter { value: 0 };
    let _ = Counter::new(5);
    let _ = counter.increment(10);
    let _ = counter.add_positive(3, 4);
    let _ = counter.clamp_to_zero(-5);
}
