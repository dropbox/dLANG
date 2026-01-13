//! Effect system test - Phase 5.2
//!
//! Tests the effect tracking system with `#[effect_set(...)]` attribute.
//! Effects are more granular than purity:
//! - IO: file/network/console operations
//! - Alloc: heap allocation
//! - Panic: may panic/abort
//! - Diverge: may not terminate
//! - Unsafe: unsafe operations
//! - GlobalState: global state mutation
//!
//! Rules:
//! - A function with effects E1 can call functions with effects E2 only if E2 ⊆ E1
//! - Pure functions (effects = {}) can only call other pure functions
//! - Functions without declared effects are assumed to have all effects
//!
//! Expected outcomes (all functions should verify):
//! - pure_compute: demonstrates pure computation with #[pure]
//! - pure_add: demonstrates pure arithmetic with #[effect_set()]
//! - pure_calling_pure: demonstrates effect composition
//! - alloc_calling_pure: demonstrates effect superset
//! - io_alloc_calling_io: demonstrates complex effect composition

// ============================================
// Pure functions (no effects)
// ============================================

/// A pure function - no side effects at all
#[pure]
fn pure_compute(x: i32) -> i32 {
    x.saturating_mul(2)
}

/// Another pure function - empty effects list is equivalent to pure
#[effect_set()]
fn pure_add(a: i32, b: i32) -> i32 {
    a.saturating_add(b)
}

/// Pure function: absolute value
#[pure]
fn pure_abs(x: i32) -> i32 {
    if x < 0 { x.saturating_neg() } else { x }
}

// ============================================
// Functions with specific effects
// ============================================

/// A function with Alloc effect
#[effect_set(Alloc)]
fn may_allocate(x: i32) -> i32 {
    // Conceptually allocates - in reality just computes
    x.saturating_add(1)
}

/// A function with IO effect
#[effect_set(IO)]
fn may_do_io(x: i32) -> i32 {
    // Conceptually does IO - in reality just computes
    x.saturating_sub(1)
}

// ============================================
// Valid effect compositions
// ============================================

/// Pure function calling pure function - valid
/// Empty effects ⊆ Empty effects
#[pure]
fn pure_calling_pure(x: i32) -> i32 {
    pure_compute(x)
}

/// Chained pure functions - valid
#[effect_set()]
fn pure_chain(x: i32) -> i32 {
    let a = pure_compute(x);
    let b = pure_add(a, x);
    pure_abs(b)
}

/// Function with Alloc effect calling pure function - valid
/// Empty effects ⊆ {Alloc}
#[effect_set(Alloc)]
fn alloc_calling_pure(x: i32) -> i32 {
    let result = pure_compute(x);
    may_allocate(result)
}

/// Function with IO+Alloc effects calling IO and Alloc functions - valid
/// {IO} ⊆ {IO, Alloc} and {Alloc} ⊆ {IO, Alloc}
#[effect_set(IO, Alloc)]
fn io_alloc_calling_io(x: i32) -> i32 {
    let a = may_do_io(x);
    may_allocate(a)
}

// ============================================
// Main function
// ============================================

fn main() {
    // Test pure functions
    let x = pure_compute(21);
    println!("pure_compute(21) = {}", x);

    let y = pure_add(10, 20);
    println!("pure_add(10, 20) = {}", y);

    let z = pure_abs(-5);
    println!("pure_abs(-5) = {}", z);

    // Test pure composition
    let a = pure_calling_pure(5);
    println!("pure_calling_pure(5) = {}", a);

    let b = pure_chain(3);
    println!("pure_chain(3) = {}", b);

    // Test effect compositions
    let c = alloc_calling_pure(7);
    println!("alloc_calling_pure(7) = {}", c);

    let d = io_alloc_calling_io(10);
    println!("io_alloc_calling_io(10) = {}", d);
}
