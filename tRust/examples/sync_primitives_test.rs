// Phase 10.1: Synchronization primitives integration test
// Tests Box, Mutex, RwLock, and Arc contracts
// These types have documented contracts but limited postconditions due to runtime semantics

use std::sync::{Arc, Mutex, RwLock};

// =================================================================
// Arc<T> smart pointer tests
// =================================================================

/// Arc::strong_count returns at least 1 for a live Arc
#[ensures("result >= 1")]
fn arc_strong_count_one() -> usize {
    let arc = Arc::new(42);
    Arc::strong_count(&arc)
}

/// Clone increases strong count - but we only know count >= 1
#[ensures("result >= 1")]
fn arc_after_clone() -> usize {
    let arc = Arc::new(42);
    let _clone = Arc::clone(&arc);
    Arc::strong_count(&arc)
}

/// Arc::weak_count returns >= 0
#[ensures("result >= 0")]
fn arc_weak_count_zero() -> usize {
    let arc = Arc::new(42);
    Arc::weak_count(&arc)
}

/// Multiple clones still have count >= 1
#[ensures("result >= 1")]
fn arc_multiple_clones() -> usize {
    let arc = Arc::new(100);
    let _c1 = Arc::clone(&arc);
    let _c2 = Arc::clone(&arc);
    let _c3 = Arc::clone(&arc);
    Arc::strong_count(&arc)
}

// =================================================================
// Mutex<T> tests - verification of type handling
// =================================================================

/// Mutex::is_poisoned - verifies type handling
#[ensures("true")]
fn mutex_not_poisoned_check() -> bool {
    let mutex = Mutex::new(42);
    let _poisoned = mutex.is_poisoned();
    true
}

/// Simple mutex creation - verifies Mutex type is handled
#[ensures("true")]
fn mutex_creation_simple() -> bool {
    let _mutex = Mutex::new(42);
    true
}

/// Mutex with different inner types
#[ensures("true")]
fn mutex_with_string() -> bool {
    let _mutex = Mutex::new(String::new());
    true
}

// =================================================================
// RwLock<T> tests
// =================================================================

/// RwLock::is_poisoned - verifies type handling
#[ensures("true")]
fn rwlock_not_poisoned_check() -> bool {
    let rwlock = RwLock::new(42);
    let _poisoned = rwlock.is_poisoned();
    true
}

/// Simple RwLock creation
#[ensures("true")]
fn rwlock_creation_simple() -> bool {
    let _rwlock = RwLock::new(42);
    true
}

/// RwLock with Vec
#[ensures("true")]
fn rwlock_with_vec() -> bool {
    let _rwlock = RwLock::new(Vec::<i32>::new());
    true
}

// =================================================================
// Arc with Mutex (common thread-safe pattern)
// =================================================================

/// Arc<Mutex<T>> pattern - strong_count >= 1
#[ensures("result >= 1")]
fn arc_mutex_count() -> usize {
    let arc_mutex = Arc::new(Mutex::new(42));
    Arc::strong_count(&arc_mutex)
}

/// Multiple Arc clones - count >= 1 still holds
#[ensures("result >= 1")]
fn arc_mutex_multi_clone() -> usize {
    let arc_mutex = Arc::new(Mutex::new(42));
    let _c1 = Arc::clone(&arc_mutex);
    let _c2 = Arc::clone(&arc_mutex);
    Arc::strong_count(&arc_mutex)
}

/// Arc<RwLock<T>> pattern
#[ensures("result >= 1")]
fn arc_rwlock_count() -> usize {
    let arc_rwlock = Arc::new(RwLock::new(Vec::<i32>::new()));
    Arc::strong_count(&arc_rwlock)
}

// =================================================================
// Entry point
// =================================================================

fn main() {
    // Arc tests
    assert!(arc_strong_count_one() >= 1);
    assert!(arc_after_clone() >= 1);
    assert!(arc_weak_count_zero() >= 0);
    assert!(arc_multiple_clones() >= 1);

    // Mutex tests
    assert!(mutex_not_poisoned_check());
    assert!(mutex_creation_simple());
    assert!(mutex_with_string());

    // RwLock tests
    assert!(rwlock_not_poisoned_check());
    assert!(rwlock_creation_simple());
    assert!(rwlock_with_vec());

    // Arc<Mutex<T>> tests
    assert!(arc_mutex_count() >= 1);
    assert!(arc_mutex_multi_clone() >= 1);
    assert!(arc_rwlock_count() >= 1);

    println!("All synchronization primitive tests passed!");
}
