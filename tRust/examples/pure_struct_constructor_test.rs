//! Test L7e: Pure struct constructor postcondition extraction
//!
//! This tests the Phase 11.6 feature: automatic extraction of implicit postconditions
//! from pure functions that return struct aggregates. When a #[pure] function returns
//! a struct, tRust automatically extracts field->param mappings as postconditions.
//!
//! Expected: All 8 functions VERIFIED

// Test 1: Basic pure struct constructor (single field)
pub struct SingleField { pub value: usize }

#[cfg_attr(trust_verify, pure)]
fn single_field_new(v: usize) -> SingleField { SingleField { value: v } }

#[cfg_attr(trust_verify, ensures("result.value == x"))]
pub fn test_single_field(x: usize) -> SingleField { single_field_new(x) }

// Test 2: Pure struct constructor with multiple fields
pub struct MultiField { pub a: usize, pub b: usize }

#[cfg_attr(trust_verify, pure)]
fn multi_field_new(x: usize, y: usize) -> MultiField { MultiField { a: x, b: y } }

#[cfg_attr(trust_verify, ensures("result.a == p"))]
#[cfg_attr(trust_verify, ensures("result.b == q"))]
pub fn test_multi_field(p: usize, q: usize) -> MultiField { multi_field_new(p, q) }

// Test 3: Chained pure function calls
// The outer function calls the inner pure function, and the implicit postcondition
// is propagated through the call chain.
pub struct Squared { pub value: usize, pub original: usize }

#[cfg_attr(trust_verify, pure)]
fn make_squared(n: usize) -> Squared { Squared { value: n, original: n } }

#[cfg_attr(trust_verify, ensures("result.original == x"))]
pub fn test_chained_call(x: usize) -> Squared { make_squared(x) }

// Test 4: Pure struct with different param names than fields
pub struct Point { pub x: usize, pub y: usize }

#[cfg_attr(trust_verify, pure)]
fn make_point(horizontal: usize, vertical: usize) -> Point {
    Point { x: horizontal, y: vertical }
}

#[cfg_attr(trust_verify, ensures("result.x == h"))]
#[cfg_attr(trust_verify, ensures("result.y == v"))]
pub fn test_point(h: usize, v: usize) -> Point { make_point(h, v) }

// Test 5: Direct return vs helper call equivalence
pub struct Wrapper { pub item: usize }

#[cfg_attr(trust_verify, pure)]
fn wrap(i: usize) -> Wrapper { Wrapper { item: i } }

#[cfg_attr(trust_verify, ensures("result.item == n"))]
pub fn via_helper(n: usize) -> Wrapper { wrap(n) }

#[cfg_attr(trust_verify, ensures("result.item == n"))]
pub fn direct_construction(n: usize) -> Wrapper { Wrapper { item: n } }

// Test 6: Pure constructor with constant field
pub struct WithConstant { pub dynamic: usize, pub constant: usize }

#[cfg_attr(trust_verify, pure)]
fn with_const(d: usize) -> WithConstant { WithConstant { dynamic: d, constant: 42 } }

#[cfg_attr(trust_verify, ensures("result.dynamic == x"))]
pub fn test_with_constant(x: usize) -> WithConstant { with_const(x) }

fn main() {
    // Runtime tests
    let s = test_single_field(10);
    assert_eq!(s.value, 10);

    let m = test_multi_field(1, 2);
    assert_eq!(m.a, 1);
    assert_eq!(m.b, 2);

    let sq = test_chained_call(7);
    assert_eq!(sq.original, 7);
    assert_eq!(sq.value, 7);

    let p = test_point(100, 200);
    assert_eq!(p.x, 100);
    assert_eq!(p.y, 200);

    let w1 = via_helper(77);
    let w2 = direct_construction(77);
    assert_eq!(w1.item, w2.item);

    let wc = test_with_constant(99);
    assert_eq!(wc.dynamic, 99);
    assert_eq!(wc.constant, 42);

    println!("All runtime tests passed!");
}
