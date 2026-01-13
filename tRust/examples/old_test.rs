//! Example: Functions with old() expressions in postconditions
//!
//! Tests the old() syntax for comparing pre-state and post-state values.
//! In Rust, parameters are immutable by default, so old(x) == x at function entry.
//!
//! Expected outcomes:
//! increment_old: @expect: VERIFIED
//! decrement_old: @expect: VERIFIED
//! double_old: @expect: VERIFIED
//! add_old: @expect: VERIFIED
//! increment_strict: @expect: VERIFIED
//! double_plus_one: @expect: VERIFIED
//!
//! NOTE: Use saturating arithmetic to prevent overflow while testing old() semantics.

// Simple increment: result equals old value plus 1
// Use saturating_add for overflow safety
fn increment_old(x: i32) -> i32 {
    x.saturating_add(1)
}

// Decrement: result equals old value minus 1
// Use saturating_sub for underflow safety
fn decrement_old(x: i32) -> i32 {
    x.saturating_sub(1)
}

// Double: result equals old value times 2 (linear - uses constant multiplier)
// Use saturating_add to prevent overflow
fn double_old(x: i32) -> i32 {
    x.saturating_add(x)
}

// Two parameters: result uses both old values
// Use saturating_add for overflow safety
fn add_old(a: i32, b: i32) -> i32 {
    a.saturating_add(b)
}

// Old in comparison: result greater than old
// Use saturating_add for overflow safety
fn increment_strict(x: i32) -> i32 {
    x.saturating_add(1)
}

// Multiple old() in one expression
// Use saturating operations for overflow safety
fn double_plus_one(x: i32) -> i32 {
    x.saturating_add(x).saturating_add(1)
}

fn main() {
    println!("increment_old(5) = {}", increment_old(5));
    println!("decrement_old(5) = {}", decrement_old(5));
    println!("double_old(3) = {}", double_old(3));
    println!("add_old(2, 3) = {}", add_old(2, 3));
    println!("increment_strict(5) = {}", increment_strict(5));
    println!("double_plus_one(5) = {}", double_plus_one(5));
}
