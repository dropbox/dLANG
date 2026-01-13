//! Test for automatic pure method inlining (Phase 11.1 + 11.1.1 Named Fields)
//!
//! This test demonstrates automatic MIR extraction for #[pure] methods
//! that do NOT have explicit #[pure_returns] annotations.
//!
//! The verifier analyzes the MIR of simple pure functions and automatically
//! extracts the return expression for use in specification inlining.
//!
//! Phase 11.1: Tuple-like structs (self.0) - IMPLEMENTED
//! Phase 11.1.1: Named struct fields (self.field_name) - IMPLEMENTED
//!
//! Expected: VERIFIED (all functions pass verification via automatic extraction)

#![allow(dead_code)]

// Test 1: Simple newtype getter (no #[pure_returns] - automatic extraction)
pub struct Idx(pub usize);

impl Idx {
    // Only #[pure], no #[pure_returns] - MIR extraction should find "self.0"
    #[pure]
    pub fn index(&self) -> usize {
        self.0
    }
}

// @expect: VERIFIED
// result.index() should be automatically inlined to result.0
#[ensures("result.index() == 42")]
pub fn make_idx_42() -> Idx {
    Idx(42)
}

// Test 2: Named field accessor (NOW SUPPORTED in Phase 1.1)
// Named fields are automatically extracted from MIR with proper field names
pub struct Point {
    pub x: i32,
    pub y: i32,
}

impl Point {
    // No #[pure_returns] needed - automatic MIR extraction gets field names
    #[pure]
    pub fn get_x(&self) -> i32 {
        self.x
    }

    #[pure]
    pub fn get_y(&self) -> i32 {
        self.y
    }
}

// @expect: VERIFIED (automatic extraction of "self.x")
#[ensures("result.get_x() == 10")]
pub fn make_point() -> Point {
    Point { x: 10, y: 20 }
}

// Test 2b: Also test get_y with automatic extraction
// @expect: VERIFIED
#[ensures("result.get_y() == 20")]
pub fn get_point_y() -> Point {
    Point { x: 10, y: 20 }
}

// Test 3: Multiple method calls with automatic inlining
// @expect: VERIFIED
#[ensures("result.index() + 1 > result.index()")]
pub fn trivial_inequality() -> Idx {
    Idx(0)
}

// Test 4: Method call with parametric comparison
// @expect: VERIFIED
#[ensures("result.index() == n")]
pub fn make_idx_n(n: usize) -> Idx {
    Idx(n)
}

// Test 5: Comparison of struct with automatic method inlining
// @expect: VERIFIED
#[ensures("result.index() >= 0")]
pub fn make_positive_idx() -> Idx {
    Idx(100)
}

// Test 6: Mixed - one with annotation, one without
pub struct Wrapper(pub usize);

impl Wrapper {
    // With explicit annotation (existing mechanism)
    #[pure]
    #[pure_returns("self.0")]
    pub fn with_anno(&self) -> usize {
        self.0
    }

    // Without annotation (automatic MIR extraction)
    #[pure]
    pub fn without_anno(&self) -> usize {
        self.0
    }
}

// Both methods should work for spec inlining
// @expect: VERIFIED
#[ensures("result.with_anno() == 50")]
pub fn test_with_anno() -> Wrapper {
    Wrapper(50)
}

// @expect: VERIFIED (depends on automatic MIR extraction)
#[ensures("result.without_anno() == 60")]
pub fn test_without_anno() -> Wrapper {
    Wrapper(60)
}

// Baseline: no method calls (should always work)
// @expect: VERIFIED
#[ensures("result == 99")]
pub fn baseline_int() -> usize {
    99
}

// @expect: VERIFIED
#[ensures("result.0 == 77")]
pub fn baseline_field_access() -> Idx {
    Idx(77)
}

fn main() {
    println!("make_idx_42().index() = {}", make_idx_42().index());
    println!("make_point().get_x() = {}", make_point().get_x());
    println!("trivial_inequality().index() = {}", trivial_inequality().index());
    println!("make_idx_n(100).index() = {}", make_idx_n(100).index());
    println!("make_positive_idx().index() = {}", make_positive_idx().index());
    println!("test_with_anno().with_anno() = {}", test_with_anno().with_anno());
    println!("test_without_anno().without_anno() = {}", test_without_anno().without_anno());
}
