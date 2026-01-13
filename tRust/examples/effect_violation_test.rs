//! Effect violation test - Phase 5.2
//!
//! Tests that the effect system correctly DETECTS violations when:
//! - A pure function calls a function with effects
//! - A function with limited effects calls a function with additional effects
//!
//! Expected: This test should produce effect violation errors.
//! The test PASSES if the compiler correctly reports the violations.
//!
//! Effect rules:
//! - A function with effects E1 can call functions with effects E2 only if E2 ⊆ E1
//! - Pure functions (effects = {}) can only call other pure functions

// ============================================
// Functions with declared effects
// ============================================

/// A pure function - no side effects
#[pure]
fn pure_compute(x: i32) -> i32 {
    x.saturating_mul(2)
}

/// Another pure function
#[effect_set()]
fn pure_add(a: i32, b: i32) -> i32 {
    a.saturating_add(b)
}

/// A function with IO effect
#[effect_set(IO)]
fn io_function(x: i32) -> i32 {
    // Conceptually does IO
    x.saturating_add(1)
}

/// A function with Alloc effect
#[effect_set(Alloc)]
fn alloc_function(x: i32) -> i32 {
    // Conceptually allocates
    x.saturating_mul(2)
}

/// A function with IO and Alloc effects
#[effect_set(IO, Alloc)]
fn io_alloc_function(x: i32) -> i32 {
    x.saturating_sub(1)
}

// ============================================
// VALID compositions (should not produce errors)
// ============================================

/// Pure calling pure - VALID
#[pure]
fn valid_pure_chain(x: i32) -> i32 {
    let a = pure_compute(x);
    pure_add(a, 1)
}

/// IO calling pure - VALID (pure ⊆ IO)
#[effect_set(IO)]
fn valid_io_calling_pure(x: i32) -> i32 {
    pure_compute(x)
}

/// IO,Alloc calling IO - VALID (IO ⊆ {IO, Alloc})
#[effect_set(IO, Alloc)]
fn valid_io_alloc_calling_io(x: i32) -> i32 {
    io_function(x)
}

// ============================================
// INVALID compositions (should produce errors)
// ============================================

/// VIOLATION: Pure calling IO function
/// Expected error: pure function cannot call io_function which has IO effect
#[pure]
fn invalid_pure_calling_io(x: i32) -> i32 {
    io_function(x)  // ERROR: IO not allowed in pure function
}

/// VIOLATION: Pure calling Alloc function
/// Expected error: pure function cannot call alloc_function which has Alloc effect
#[effect_set()]  // Empty = pure
fn invalid_pure_calling_alloc(x: i32) -> i32 {
    alloc_function(x)  // ERROR: Alloc not allowed in pure function
}

/// VIOLATION: IO calling Alloc function (IO doesn't include Alloc)
/// Expected error: IO function cannot call alloc_function which has Alloc effect
#[effect_set(IO)]
fn invalid_io_calling_alloc(x: i32) -> i32 {
    alloc_function(x)  // ERROR: Alloc not in caller's effect set
}

/// VIOLATION: Alloc calling IO function (Alloc doesn't include IO)
/// Expected error: Alloc function cannot call io_function which has IO effect
#[effect_set(Alloc)]
fn invalid_alloc_calling_io(x: i32) -> i32 {
    io_function(x)  // ERROR: IO not in caller's effect set
}

/// VIOLATION: IO calling IO,Alloc function (missing Alloc)
/// Expected error: IO function cannot call io_alloc_function which has {IO, Alloc}
#[effect_set(IO)]
fn invalid_io_calling_io_alloc(x: i32) -> i32 {
    io_alloc_function(x)  // ERROR: Alloc not in caller's effect set
}

// ============================================
// Main function (no effects declared - can call anything)
// ============================================

fn main() {
    // Valid calls
    let a = valid_pure_chain(5);
    println!("valid_pure_chain(5) = {}", a);

    let b = valid_io_calling_pure(10);
    println!("valid_io_calling_pure(10) = {}", b);

    let c = valid_io_alloc_calling_io(15);
    println!("valid_io_alloc_calling_io(15) = {}", c);

    // Invalid calls - these should have been flagged during verification
    let d = invalid_pure_calling_io(20);
    println!("invalid_pure_calling_io(20) = {}", d);

    let e = invalid_pure_calling_alloc(25);
    println!("invalid_pure_calling_alloc(25) = {}", e);

    let f = invalid_io_calling_alloc(30);
    println!("invalid_io_calling_alloc(30) = {}", f);

    let g = invalid_alloc_calling_io(35);
    println!("invalid_alloc_calling_io(35) = {}", g);

    let h = invalid_io_calling_io_alloc(40);
    println!("invalid_io_calling_io_alloc(40) = {}", h);
}
