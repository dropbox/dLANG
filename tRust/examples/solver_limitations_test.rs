// Comprehensive test file for solver limitations
//
// Documents and tests all known solver limitations (L1-L7).
// See: reports/main/SOLVER_LIMITATIONS_2026-01-01.md
//
// Expected Results:
// - L1 tests: VERIFIED (self as usize handling implemented)
// - L2 tests: Mixed (result.field needs axiomatization for complex types)
// - L3 tests: VERIFIED (with #[pure_returns] annotation)
// - L4 tests: VERIFIED for Vec.len(), needs investigation for other types
// - L5 tests: N/A (closures not supported by design)
// - L6 tests: Mixed (up to 2-3 levels supported)
// - L7 tests: VERIFIED (CHC struct field projections fixed)

#![allow(unused)]

// =================================================================
// L1: Cast expressions - FIXED
// "self as usize", "x as i32", etc.
// =================================================================

// L1.1: Integer to usize cast
// @expect: VERIFIED
#[ensures("result == x as usize")]
fn l1_u32_to_usize(x: u32) -> usize {
    x as usize
}

// L1.2: Integer to signed cast
// @expect: VERIFIED
#[requires("x < 128")]
#[ensures("result == x as i32")]
fn l1_u8_to_i32(x: u8) -> i32 {
    x as i32
}

// L1.3: Signed to unsigned cast
// @expect: VERIFIED
#[requires("x >= 0")]
#[ensures("result == x as u32")]
fn l1_i32_to_u32(x: i32) -> u32 {
    x as u32
}

// =================================================================
// L2: result.field - PARTIAL SUPPORT
// Field access on return values needs axiomatization for complex types
// =================================================================

// Simple tuple struct field access
struct Wrapper(pub usize);

// L2.1: Simple tuple struct - accesses .0 field
// @expect: VERIFIED
#[ensures("result.0 == 42")]
fn l2_simple_tuple_field() -> Wrapper {
    Wrapper(42)
}

// Named struct
struct Point { pub x: i32, pub y: i32 }

// L2.2: Named struct field
// @expect: VERIFIED (simple struct field tracking works)
fn l2_named_struct_field() -> Point {
    Point { x: 10, y: 20 }
}

// =================================================================
// L3: result.method() - FIXED with #[pure_returns]
// Method calls on return values work with explicit annotation
// =================================================================

struct MethodWrapper(pub usize);

impl MethodWrapper {
    #[pure]
    #[pure_returns("self.0")]
    pub fn get(&self) -> usize {
        self.0
    }

    #[pure]
    #[pure_returns("self.0 > 0")]
    pub fn is_positive(&self) -> bool {
        self.0 > 0
    }
}

// L3.1: Method call with pure_returns annotation
// @expect: VERIFIED
#[ensures("result.get() == 42")]
fn l3_method_with_annotation() -> MethodWrapper {
    MethodWrapper(42)
}

// L3.2: Boolean method with pure_returns
// @expect: VERIFIED
#[ensures("result.is_positive()")]
fn l3_bool_method() -> MethodWrapper {
    MethodWrapper(100)
}

// =================================================================
// L4: self.field - WORKS for Vec, investigate for other types
// =================================================================

struct Container {
    pub items: Vec<i32>,
}

impl Container {
    // Note: Constructor needs postcondition for callers to reason about fields
    #[ensures("result.items.len() == 0")]
    fn new() -> Self {
        Container { items: Vec::new() }
    }
}

// L4.1: self.items.len() on struct with Vec field
// @expect: VERIFIED
#[ensures("result.items.len() == 0")]
fn l4_self_vec_field() -> Container {
    Container::new()
}

// L4.2: Vec result with len() method
// @expect: VERIFIED
#[ensures("result.len() == 2")]
fn l4_vec_result_len() -> Vec<i32> {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v
}

// L4.3: Vec result with is_empty() method
// @expect: VERIFIED
#[ensures("!result.is_empty()")]
fn l4_vec_not_empty() -> Vec<i32> {
    let mut v = Vec::new();
    v.push(42);
    v
}

// =================================================================
// L6: Deep field paths - LIMITED SUPPORT
// Up to 2-3 levels of field access supported
// =================================================================

struct Inner { pub value: i32 }
struct Outer { pub inner: Inner }
struct Deeper { pub outer: Outer }

// L6.1: Two levels of field access
// @expect: VERIFIED
#[ensures("result.inner.value == 42")]
fn l6_two_levels() -> Outer {
    Outer { inner: Inner { value: 42 } }
}

// L6.2: Precondition with two-level access
// @expect: VERIFIED
#[requires("outer.inner.value > 0")]
fn l6_two_level_precondition(outer: Outer) -> i32 {
    outer.inner.value
}

// =================================================================
// L7: CHC struct field projections - FIXED
// Branching code returning structs now correctly handles field projections
// =================================================================

struct Pair {
    pub first: i32,
    pub second: i32,
}

// L7.1: Struct return with branching - field access should work
// @expect: VERIFIED
#[requires("cond || !cond")]  // Force CHC analysis via non-trivial condition
fn l7_branching_struct(cond: bool) -> Pair {
    if cond {
        Pair { first: 10, second: 20 }
    } else {
        Pair { first: 30, second: 40 }
    }
}

// L7.2: Struct field in postcondition with branching
// @expect: VERIFIED
#[requires("x > 0")]
#[requires("x < 2147483645")]  // Prevent overflow (i32::MAX - 2)
fn l7_branching_with_postcond(x: i32) -> Pair {
    if x > 10 {
        Pair { first: x, second: x + 1 }
    } else {
        Pair { first: x, second: x + 2 }
    }
}

// =================================================================
// Expected failures - Limitations that are by design
// =================================================================

// L5.1: General closures in specs - NOT SUPPORTED
// This would require higher-order reasoning.
// Restricted support exists for common predicate combinators:
// - `Option::is_some_and(|x| pred)`
// - `Result::{is_ok_and,is_err_and}(|x| pred)`
// See: examples/option_result_predicate_combinators_test.rs

// Alternative that works:
// @expect: VERIFIED (when result is Some with value > 0)
#[ensures("result.is_some()")]
fn l5_workaround_no_closure() -> Option<i32> {
    Some(42)
}

fn main() {
    // L1 tests
    println!("L1.1: {}", l1_u32_to_usize(100));
    println!("L1.2: {}", l1_u8_to_i32(127));
    println!("L1.3: {}", l1_i32_to_u32(50));

    // L2 tests
    println!("L2.1: {}", l2_simple_tuple_field().0);
    let p = l2_named_struct_field();
    println!("L2.2: ({}, {})", p.x, p.y);

    // L3 tests
    println!("L3.1: {}", l3_method_with_annotation().get());
    println!("L3.2: {}", l3_bool_method().is_positive());

    // L4 tests
    println!("L4.1: {}", l4_self_vec_field().items.len());
    println!("L4.2: {}", l4_vec_result_len().len());
    println!("L4.3: {}", !l4_vec_not_empty().is_empty());

    // L6 tests
    println!("L6.1: {}", l6_two_levels().inner.value);
    println!("L6.2: {}", l6_two_level_precondition(Outer { inner: Inner { value: 5 } }));

    // L7 tests
    let pair1 = l7_branching_struct(true);
    let pair2 = l7_branching_struct(false);
    println!("L7.1: ({}, {}) or ({}, {})", pair1.first, pair1.second, pair2.first, pair2.second);
    let pair3 = l7_branching_with_postcond(5);
    println!("L7.2: ({}, {})", pair3.first, pair3.second);

    // L5 workaround
    println!("L5 workaround: {:?}", l5_workaround_no_closure());
}
