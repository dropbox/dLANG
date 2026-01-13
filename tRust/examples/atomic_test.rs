//! Atomic types integration test (Phase 10.1)
//! Tests that atomic operations return values with correct constraints.
//!
//! Unsigned atomic types (AtomicUsize, AtomicU32, etc.) return non-negative values.
//! Signed atomic types (AtomicIsize, AtomicI32, etc.) have no constraints.
//!
//! Note: Atomic operations return the PREVIOUS value, not the new value.
//! We can't verify the actual values without modeling concurrent state,
//! but we can verify type constraints (unsigned >= 0).

use std::sync::atomic::{AtomicBool, AtomicUsize, AtomicU32, AtomicI32, Ordering};

// Test 1: AtomicUsize::load returns non-negative value
#[ensures("result >= 0")]
fn test_atomic_usize_load(a: &AtomicUsize) -> usize {
    a.load(Ordering::SeqCst)
}

// Test 2: AtomicUsize::swap returns previous value (non-negative)
#[ensures("result >= 0")]
fn test_atomic_usize_swap(a: &AtomicUsize, new_val: usize) -> usize {
    a.swap(new_val, Ordering::SeqCst)
}

// Test 3: AtomicUsize::fetch_add returns previous value (non-negative)
#[ensures("result >= 0")]
fn test_atomic_usize_fetch_add(a: &AtomicUsize, val: usize) -> usize {
    a.fetch_add(val, Ordering::SeqCst)
}

// Test 4: AtomicUsize::fetch_sub returns previous value (non-negative)
#[ensures("result >= 0")]
fn test_atomic_usize_fetch_sub(a: &AtomicUsize, val: usize) -> usize {
    a.fetch_sub(val, Ordering::SeqCst)
}

// Test 5: AtomicUsize::fetch_and returns previous value (non-negative)
#[ensures("result >= 0")]
fn test_atomic_usize_fetch_and(a: &AtomicUsize, val: usize) -> usize {
    a.fetch_and(val, Ordering::SeqCst)
}

// Test 6: AtomicUsize::fetch_or returns previous value (non-negative)
#[ensures("result >= 0")]
fn test_atomic_usize_fetch_or(a: &AtomicUsize, val: usize) -> usize {
    a.fetch_or(val, Ordering::SeqCst)
}

// Test 7: AtomicU32::load returns non-negative value
#[ensures("result >= 0")]
fn test_atomic_u32_load(a: &AtomicU32) -> u32 {
    a.load(Ordering::SeqCst)
}

// Test 8: AtomicU32::fetch_add returns previous value (non-negative)
#[ensures("result >= 0")]
fn test_atomic_u32_fetch_add(a: &AtomicU32, val: u32) -> u32 {
    a.fetch_add(val, Ordering::SeqCst)
}

// Test 9: AtomicU32::fetch_min returns previous value (non-negative)
#[ensures("result >= 0")]
fn test_atomic_u32_fetch_min(a: &AtomicU32, val: u32) -> u32 {
    a.fetch_min(val, Ordering::SeqCst)
}

// Test 10: AtomicU32::fetch_max returns previous value (non-negative)
#[ensures("result >= 0")]
fn test_atomic_u32_fetch_max(a: &AtomicU32, val: u32) -> u32 {
    a.fetch_max(val, Ordering::SeqCst)
}

// Test 11: AtomicI32::load returns a value (no constraint for signed)
// This test just verifies the function is recognized, not a specific constraint
fn test_atomic_i32_load(a: &AtomicI32) -> i32 {
    a.load(Ordering::SeqCst)
}

// Test 12: AtomicBool operations are recognized (no constraints)
fn test_atomic_bool_swap(a: &AtomicBool, new_val: bool) -> bool {
    a.swap(new_val, Ordering::SeqCst)
}

// Test 13: Combined test - use atomic in function with postcondition
// Just return the loaded value to verify the builtin contract is applied
#[ensures("result >= 0")]
fn test_atomic_combined(a: &AtomicUsize) -> usize {
    // AtomicUsize::load returns non-negative value
    a.load(Ordering::SeqCst)
}

fn main() {
    // Create atomic values for testing
    let a_usize = AtomicUsize::new(42);
    let a_u32 = AtomicU32::new(100);
    let a_i32 = AtomicI32::new(-50);
    let a_bool = AtomicBool::new(false);

    // Test the functions
    println!("AtomicUsize load: {}", test_atomic_usize_load(&a_usize));
    println!("AtomicUsize swap: {}", test_atomic_usize_swap(&a_usize, 10));
    println!("AtomicUsize fetch_add: {}", test_atomic_usize_fetch_add(&a_usize, 5));
    println!("AtomicUsize fetch_sub: {}", test_atomic_usize_fetch_sub(&a_usize, 3));
    println!("AtomicUsize fetch_and: {}", test_atomic_usize_fetch_and(&a_usize, 0xFF));
    println!("AtomicUsize fetch_or: {}", test_atomic_usize_fetch_or(&a_usize, 0x100));
    println!("AtomicU32 load: {}", test_atomic_u32_load(&a_u32));
    println!("AtomicU32 fetch_add: {}", test_atomic_u32_fetch_add(&a_u32, 10));
    println!("AtomicU32 fetch_min: {}", test_atomic_u32_fetch_min(&a_u32, 50));
    println!("AtomicU32 fetch_max: {}", test_atomic_u32_fetch_max(&a_u32, 200));
    println!("AtomicI32 load: {}", test_atomic_i32_load(&a_i32));
    println!("AtomicBool swap: {}", test_atomic_bool_swap(&a_bool, true));
    println!("Combined: {}", test_atomic_combined(&a_usize));
    println!("All atomic tests passed!");
}
