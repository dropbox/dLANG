//! Unsafe Effect Detection Test - Phase N1.4
//!
//! Tests that unsafe fn declarations automatically get the Unsafe effect
//! using HIR/MIR metadata instead of name-based heuristics.
//!
//! Expected: Effect violation errors when pure/safe functions call unsafe fn
//!
//! N1.4 Acceptance Criteria:
//! - unsafe fn automatically gets Unsafe effect (not from name, from HIR/MIR)
//! - Functions calling unsafe fn must have Unsafe in their effect set
//! - Functions with #[effect_set(Unsafe)] can call unsafe fn

// ============================================
// Unsafe functions (should auto-get Unsafe effect)
// ============================================

/// An unsafe function that dereferences raw pointer
/// This should automatically have Unsafe effect (detected via HIR/MIR, not name)
pub unsafe fn deref_raw(ptr: *const i32) -> i32 {
    // Note: The safety comes from the `unsafe fn` signature, not the body
    if ptr.is_null() {
        0
    } else {
        *ptr
    }
}

/// Another unsafe function - name has nothing to do with "unsafe"
/// The Unsafe effect should come from the fn signature, not the name
pub unsafe fn read_value(ptr: *const i32) -> i32 {
    if ptr.is_null() { 0 } else { *ptr }
}

// ============================================
// Safe functions with various effect sets
// ============================================

/// Pure helper - should not be detected as unsafe despite name
fn check_unsafe_state() -> bool {
    true  // The word "unsafe" in name should NOT make this unsafe
}

/// A pure function
#[pure]
pub fn pure_function(x: i32) -> i32 {
    x.saturating_add(1)
}

/// A function with only IO effect
#[effect_set(IO)]
pub fn io_function(x: i32) -> i32 {
    x.saturating_add(2)
}

/// A function with Unsafe effect declared
#[effect_set(Unsafe)]
pub fn unsafe_effect_function(x: i32) -> i32 {
    x.saturating_add(3)
}

/// A function with both Unsafe and IO effects
#[effect_set(Unsafe, IO)]
pub fn unsafe_io_function(x: i32) -> i32 {
    x.saturating_add(4)
}

// ============================================
// VALID: Functions that CAN call unsafe fn
// ============================================

/// VALID: Function with Unsafe effect can call unsafe fn
#[effect_set(Unsafe)]
pub fn valid_unsafe_caller(ptr: *const i32) -> i32 {
    unsafe { deref_raw(ptr) }
}

/// VALID: Function with Unsafe+IO can call unsafe fn
#[effect_set(Unsafe, IO)]
pub fn valid_unsafe_io_caller(ptr: *const i32) -> i32 {
    unsafe { read_value(ptr) }
}

/// VALID: unsafe fn can call other unsafe fn (unsafe fn has Unsafe effect)
pub unsafe fn valid_unsafe_fn_caller(ptr: *const i32) -> i32 {
    deref_raw(ptr)
}

// ============================================
// INVALID: Functions that CANNOT call unsafe fn
// ============================================

/// VIOLATION: Pure function calling unsafe fn
/// Expected error: unsafe fn has Unsafe effect not allowed by pure function
#[pure]
pub fn invalid_pure_calling_unsafe(ptr: *const i32) -> i32 {
    unsafe { deref_raw(ptr) }
}

/// VIOLATION: IO function calling unsafe fn (IO doesn't include Unsafe)
/// Expected error: unsafe fn has Unsafe effect not allowed by IO function
#[effect_set(IO)]
pub fn invalid_io_calling_unsafe(ptr: *const i32) -> i32 {
    unsafe { read_value(ptr) }
}

/// VIOLATION: Empty effect set calling unsafe fn
/// Expected error: unsafe fn has Unsafe effect not allowed
#[effect_set()]
pub fn invalid_empty_calling_unsafe(ptr: *const i32) -> i32 {
    unsafe { deref_raw(ptr) }
}

// ============================================
// Name-based heuristic should NOT be used
// ============================================

/// This function's name contains "unsafe" but it's a safe function
/// It should NOT get the Unsafe effect just because of its name
#[pure]
pub fn name_has_unsafe_but_is_pure(x: i32) -> i32 {
    check_unsafe_state();
    x.saturating_mul(2)
}

fn main() {
    // Call functions to avoid dead code warnings
    let ptr: *const i32 = std::ptr::null();
    let _ = pure_function(1);
    let _ = io_function(2);
    let _ = unsafe_effect_function(3);
    let _ = valid_unsafe_caller(ptr);
    let _ = invalid_pure_calling_unsafe(ptr);
    let _ = invalid_io_calling_unsafe(ptr);
    let _ = name_has_unsafe_but_is_pure(5);
}
