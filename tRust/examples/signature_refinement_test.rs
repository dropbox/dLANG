//! Signature-based Refinement Types Test
//!
//! This file tests inferring refinement type annotations directly from Rust
//! function signatures (e.g., `fn f(x: Positive) -> Positive`), without using
//! `// #[param_type(...)]` or `// #[return_type(...)]` annotations.
//!
//! Expected outcomes:
//! double_positive: @expect: VERIFIED
//! identity_non_negative: @expect: VERIFIED
//! identity_percentage: @expect: VERIFIED
//!
//! NOTE: Use saturating arithmetic to prevent overflow while testing signature refinements.

// Refinement type definitions (parsed by cargo-trust)
// type Positive = i32 where self > 0;
// type NonNegative = i32 where self >= 0;
// type Percentage = i32 where self >= 0 && self <= 100;

// Real Rust type aliases so the file compiles
type Positive = i32;
type NonNegative = i32;
type Percentage = i32;

fn double_positive(n: Positive) -> Positive {
    n.saturating_mul(2)
}

fn identity_non_negative(x: NonNegative) -> NonNegative {
    x
}

fn identity_percentage(x: Percentage) -> Percentage {
    x
}

fn main() {
    let a = double_positive(5);
    let b = identity_non_negative(10);
    let c = identity_percentage(50);
    println!("Results: a={}, b={}, c={}", a, b, c);
}
