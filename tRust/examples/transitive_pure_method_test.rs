//! Test for transitive pure method inlining (Phase 11.5)
//!
//! This test verifies that pure methods which call other pure methods
//! can be automatically inlined in specifications.
//!
//! Previously, only simple pure methods (single basic block) could be inlined.
//! Phase 11.5 adds support for transitive inlining where a pure method can
//! call another pure method, and both get resolved in the specification.
//!
//! Status: VERIFIED
//! Expected: All functions VERIFIED

#![allow(dead_code)]

// ============================================
// Test 1: Basic transitive inlining
// ============================================

// Inner struct with simple pure method
pub struct Inner {
    pub value: i32,
}

impl Inner {
    #[pure]
    pub fn get(&self) -> i32 {
        self.value
    }
}

// Outer struct with transitive pure method
pub struct Outer {
    pub inner: Inner,
}

impl Outer {
    // This method calls another pure method - transitive case
    #[pure]
    pub fn inner_value(&self) -> i32 {
        self.inner.get()
    }
}

// @expect: VERIFIED
#[ensures("result.inner.value == 42")]
pub fn test_basic_field_access() -> Outer {
    Outer { inner: Inner { value: 42 } }
}

// @expect: VERIFIED
#[ensures("result.inner_value() == 100")]
pub fn test_transitive_pure_method() -> Outer {
    Outer { inner: Inner { value: 100 } }
}

// @expect: VERIFIED
#[ensures("result.inner.get() == 55")]
pub fn test_direct_inner_method() -> Outer {
    Outer { inner: Inner { value: 55 } }
}

// ============================================
// Test 2: Multiple levels of wrapping
// ============================================

pub struct Level1 {
    pub data: i32,
}

impl Level1 {
    #[pure]
    pub fn val(&self) -> i32 {
        self.data
    }
}

pub struct Level2 {
    pub l1: Level1,
}

impl Level2 {
    #[pure]
    pub fn get_val(&self) -> i32 {
        self.l1.val()
    }
}

pub struct Level3 {
    pub l2: Level2,
}

impl Level3 {
    // Two levels of transitive inlining would be needed here
    // Currently only supports one level, so we use direct field access
    #[pure]
    pub fn inner_val(&self) -> i32 {
        self.l2.l1.data
    }
}

// @expect: VERIFIED
#[ensures("result.l2.l1.data == 77")]
pub fn test_deep_field() -> Level3 {
    Level3 { l2: Level2 { l1: Level1 { data: 77 } } }
}

// @expect: VERIFIED
#[ensures("result.l2.get_val() == 88")]
pub fn test_level2_transitive() -> Level3 {
    Level3 { l2: Level2 { l1: Level1 { data: 88 } } }
}

// ============================================
// Test 3: Named fields with transitive inlining
// ============================================

pub struct Counter {
    pub count: usize,
    pub name: i32,
}

impl Counter {
    #[pure]
    pub fn current_count(&self) -> usize {
        self.count
    }

    #[pure]
    pub fn get_name(&self) -> i32 {
        self.name
    }
}

pub struct CounterWrapper {
    pub counter: Counter,
}

impl CounterWrapper {
    #[pure]
    pub fn wrapped_count(&self) -> usize {
        self.counter.current_count()
    }

    #[pure]
    pub fn wrapped_name(&self) -> i32 {
        self.counter.get_name()
    }
}

// @expect: VERIFIED
#[ensures("result.wrapped_count() == 10")]
pub fn test_wrapped_count() -> CounterWrapper {
    CounterWrapper {
        counter: Counter { count: 10, name: 0 },
    }
}

// @expect: VERIFIED
#[ensures("result.wrapped_name() == 42")]
pub fn test_wrapped_name() -> CounterWrapper {
    CounterWrapper {
        counter: Counter { count: 0, name: 42 },
    }
}

// ============================================
// Test 4: Parameter-dependent transitive methods
// ============================================

// @expect: VERIFIED
#[ensures("result.inner_value() == n")]
pub fn test_parametric_transitive(n: i32) -> Outer {
    Outer { inner: Inner { value: n } }
}

fn main() {
    println!("test_basic_field_access().inner.value = {}", test_basic_field_access().inner.value);
    println!("test_transitive_pure_method().inner_value() = {}", test_transitive_pure_method().inner_value());
    println!("test_direct_inner_method().inner.get() = {}", test_direct_inner_method().inner.get());
    println!("test_deep_field().l2.l1.data = {}", test_deep_field().l2.l1.data);
    println!("test_level2_transitive().l2.get_val() = {}", test_level2_transitive().l2.get_val());
    println!("test_wrapped_count().wrapped_count() = {}", test_wrapped_count().wrapped_count());
    println!("test_wrapped_name().wrapped_name() = {}", test_wrapped_name().wrapped_name());
    println!("test_parametric_transitive(77).inner_value() = {}", test_parametric_transitive(77).inner_value());
}
