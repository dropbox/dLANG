//! Example: Using tRust verification attributes
//! Compile with: ./build/host/stage1/bin/rustc -Zverify examples/verified_function.rs
//!
//! Spec attributes use string literals for conditions:
//!   #[requires("condition")]  - Precondition
//!   #[ensures("condition")]   - Postcondition
//!   #[invariant("condition")] - Loop invariant
//!   #[decreases("expr")]      - Termination measure
//!   #[pure]                   - Pure function marker
//!   #[may_diverge]           - Non-termination marker
//!
//! Note: This file uses #[pure] actual attributes which cargo-trust
//! doesn't parse for verification status (no expected outcomes).

/// Computes the absolute value of an integer.
///
/// # Specifications
/// - Precondition: n is representable (i32::MIN cannot be negated)
/// - Postcondition: result is non-negative
// #[requires(n > i32::MIN)]
// #[ensures(result >= 0)]
fn abs(n: i32) -> i32 {
    if n < 0 { -n } else { n }
}

/// Computes the maximum of two integers.
// #[ensures(result >= a && result >= b)]
// #[ensures(result == a || result == b)]
fn max(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

/// A pure function can be used in specifications.
#[pure]
fn is_positive(n: i32) -> bool {
    n > 0
}

fn main() {
    println!("abs(-5) = {}", abs(-5));
    println!("max(3, 7) = {}", max(3, 7));
    println!("is_positive(42) = {}", is_positive(42));
}
