//! Test trait method spec violation detection (Phase 2.5.1)
//!
//! This test verifies that impl methods that violate trait contracts are DISPROVEN.
//!
//! Expected outcomes:
//! <BuggyPoint as Absolute>::abs_value: @expect: DISPROVEN

#![allow(unused)]

/// Trait with specifications - all implementations must satisfy these contracts
trait Absolute {
    /// Absolute value must return a non-negative result
    #[ensures("result >= 0")]
    fn abs_value(&self) -> i32;
}

/// A buggy point implementation
struct BuggyPoint {
    x: i32,
}

/// SHOULD FAIL: This implementation INCORRECTLY returns negative values
impl Absolute for BuggyPoint {
    fn abs_value(&self) -> i32 {
        // BUG: Returns the value directly without taking absolute value
        // This violates the trait contract: result >= 0
        self.x
    }
}

fn main() {
    let bp = BuggyPoint { x: -5 };
    println!("BuggyPoint abs: {}", bp.abs_value()); // Returns -5, violating contract!
}
