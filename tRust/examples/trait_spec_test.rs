//! Test trait method specifications (Phase 2.5.1)
//!
//! This test verifies that:
//! 1. Trait methods can have specs (#[requires], #[ensures])
//! 2. Impl methods inherit trait contracts
//! 3. Impl methods must satisfy trait postconditions
//!
//! Expected outcomes:
//! <Point as Absolute>::abs_value: @expect: VERIFIED
//! <NegativePoint as Absolute>::abs_value: @expect: VERIFIED

#![allow(unused)]

/// Trait with specifications - all implementations must satisfy these contracts
trait Absolute {
    /// Absolute value must return a non-negative result
    #[ensures("result >= 0")]
    fn abs_value(&self) -> i32;
}

/// A point that stores non-negative coordinates
struct Point {
    x: i32,
    y: i32,
}

/// Implementation that correctly satisfies the trait contract
impl Absolute for Point {
    fn abs_value(&self) -> i32 {
        // Both x and y could be negative, but we compute abs correctly
        let ax = if self.x < 0 { -self.x } else { self.x };
        let ay = if self.y < 0 { -self.y } else { self.y };
        // Use saturating_add to prevent overflow
        ax.saturating_add(ay)
    }
}

/// Another type that also implements Absolute
struct NegativePoint {
    val: i32,
}

/// Another implementation that satisfies the trait contract
impl Absolute for NegativePoint {
    fn abs_value(&self) -> i32 {
        // Returns absolute value of val
        if self.val < 0 { -self.val } else { self.val }
    }
}

fn main() {
    let p = Point { x: 3, y: -4 };
    println!("Point abs: {}", p.abs_value());

    let np = NegativePoint { val: -10 };
    println!("NegativePoint abs: {}", np.abs_value());
}
