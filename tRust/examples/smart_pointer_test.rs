//! Integration test for Rc/Arc smart pointer contracts (Phase 10.1)
//!
//! Tests builtin postconditions for:
//! - Rc::strong_count() >= 1
//! - Rc::weak_count() >= 0
//! - Arc::strong_count() >= 1
//! - Arc::weak_count() >= 0
//! - Weak::strong_count() >= 0
//! - Weak::weak_count() >= 0

use std::rc::{Rc, Weak as RcWeak};
use std::sync::{Arc, Weak as ArcWeak};

// =============================================================================
// Rc<T> strong_count tests
// =============================================================================

/// Test that Rc::strong_count() >= 1 postcondition is used
#[requires("true")]
#[ensures("result >= 1")]
fn rc_strong_count_at_least_one(rc: Rc<i32>) -> usize {
    Rc::strong_count(&rc)
}

/// Test that strong_count >= 1 allows proving result > 0
#[requires("true")]
#[ensures("result > 0")]
fn rc_strong_count_positive(rc: Rc<i32>) -> usize {
    Rc::strong_count(&rc)
}

/// Test that strong_count enables proving non-zero
#[requires("true")]
#[ensures("result != 0")]
fn rc_strong_count_nonzero(rc: Rc<i32>) -> usize {
    Rc::strong_count(&rc)
}

// =============================================================================
// Rc<T> weak_count tests
// =============================================================================

/// Test that Rc::weak_count() >= 0 postcondition is used
#[requires("true")]
#[ensures("result >= 0")]
fn rc_weak_count_nonnegative(rc: Rc<i32>) -> usize {
    Rc::weak_count(&rc)
}

// =============================================================================
// Arc<T> strong_count tests
// =============================================================================

/// Test that Arc::strong_count() >= 1 postcondition is used
#[requires("true")]
#[ensures("result >= 1")]
fn arc_strong_count_at_least_one(arc: Arc<i32>) -> usize {
    Arc::strong_count(&arc)
}

/// Test that strong_count >= 1 allows proving result > 0
#[requires("true")]
#[ensures("result > 0")]
fn arc_strong_count_positive(arc: Arc<i32>) -> usize {
    Arc::strong_count(&arc)
}

/// Test that strong_count enables proving non-zero
#[requires("true")]
#[ensures("result != 0")]
fn arc_strong_count_nonzero(arc: Arc<i32>) -> usize {
    Arc::strong_count(&arc)
}

// =============================================================================
// Arc<T> weak_count tests
// =============================================================================

/// Test that Arc::weak_count() >= 0 postcondition is used
#[requires("true")]
#[ensures("result >= 0")]
fn arc_weak_count_nonnegative(arc: Arc<i32>) -> usize {
    Arc::weak_count(&arc)
}

// =============================================================================
// Weak<T> tests (Rc-based)
// =============================================================================

/// Test that Weak::strong_count() >= 0 (can be 0 if dropped)
#[requires("true")]
#[ensures("result >= 0")]
fn rc_weak_strong_count_nonnegative(weak: RcWeak<i32>) -> usize {
    RcWeak::strong_count(&weak)
}

/// Test that Weak::weak_count() >= 0
#[requires("true")]
#[ensures("result >= 0")]
fn rc_weak_weak_count_nonnegative(weak: RcWeak<i32>) -> usize {
    RcWeak::weak_count(&weak)
}

// =============================================================================
// Weak<T> tests (Arc-based)
// =============================================================================

/// Test that Arc-based Weak::strong_count() >= 0
#[requires("true")]
#[ensures("result >= 0")]
fn arc_weak_strong_count_nonnegative(weak: ArcWeak<i32>) -> usize {
    ArcWeak::strong_count(&weak)
}

/// Test that Arc-based Weak::weak_count() >= 0
#[requires("true")]
#[ensures("result >= 0")]
fn arc_weak_weak_count_nonnegative(weak: ArcWeak<i32>) -> usize {
    ArcWeak::weak_count(&weak)
}

// =============================================================================
// Combined tests
// =============================================================================

/// Test sum of strong and weak counts is valid (both positive in some sense)
/// Uses saturating_add to avoid overflow
#[requires("true")]
#[ensures("result >= 1")]
fn rc_total_refs_positive(rc: Rc<i32>) -> usize {
    // strong_count >= 1, weak_count >= 0, so total >= 1
    let strong = Rc::strong_count(&rc);
    let weak = Rc::weak_count(&rc);
    strong.saturating_add(weak)
}

/// Test sum of strong and weak counts for Arc
/// Uses saturating_add to avoid overflow
#[requires("true")]
#[ensures("result >= 1")]
fn arc_total_refs_positive(arc: Arc<i32>) -> usize {
    // strong_count >= 1, weak_count >= 0, so total >= 1
    let strong = Arc::strong_count(&arc);
    let weak = Arc::weak_count(&arc);
    strong.saturating_add(weak)
}

fn main() {
    // Run basic tests
    let rc = Rc::new(42);
    println!("Rc strong_count: {}", rc_strong_count_at_least_one(Rc::clone(&rc)));
    println!("Rc weak_count: {}", rc_weak_count_nonnegative(Rc::clone(&rc)));
    println!("Rc total refs: {}", rc_total_refs_positive(Rc::clone(&rc)));

    let arc = Arc::new(42);
    println!("Arc strong_count: {}", arc_strong_count_at_least_one(Arc::clone(&arc)));
    println!("Arc weak_count: {}", arc_weak_count_nonnegative(Arc::clone(&arc)));
    println!("Arc total refs: {}", arc_total_refs_positive(Arc::clone(&arc)));

    // Test with weak references
    let rc_weak = Rc::downgrade(&rc);
    println!("RcWeak strong_count: {}", rc_weak_strong_count_nonnegative(RcWeak::clone(&rc_weak)));
    println!("RcWeak weak_count: {}", rc_weak_weak_count_nonnegative(RcWeak::clone(&rc_weak)));

    let arc_weak = Arc::downgrade(&arc);
    println!("ArcWeak strong_count: {}", arc_weak_strong_count_nonnegative(ArcWeak::clone(&arc_weak)));
    println!("ArcWeak weak_count: {}", arc_weak_weak_count_nonnegative(ArcWeak::clone(&arc_weak)));

    println!("Smart pointer tests completed!");
}
