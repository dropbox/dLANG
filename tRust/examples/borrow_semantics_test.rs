//! Borrow Semantics Verification Test (N3.1b)
//!
//! This test demonstrates tRust's verification of Rust's borrowing rules:
//! - Aliasing XOR Mutability: &mut T parameters don't alias with other refs
//! - Borrow tracking: mutable borrows are tracked in verification
//!
//! Expected outcomes:
//! All functions: @expect: VERIFIED
//!
//! The verifier generates non-aliasing VCs for functions with &mut parameters,
//! ensuring that mutable references don't alias with other reference parameters.

// Test 1: Basic non-aliasing of two mutable references
// The verifier generates: addr(a) != addr(b)
fn swap_values(a: &mut i32, b: &mut i32) {
    let tmp = *a;
    *a = *b;
    *b = tmp;
}

// Test 2: Two mutable refs to same type - must be disjoint
fn increment_both(a: &mut i32, b: &mut i32) {
    *a = (*a).saturating_add(1);
    *b = (*b).saturating_add(1);
}

// Test 3: Mixed &mut and & - mutable must not alias shared
// The function modifies a but reads b - they must point to different locations
fn add_from_ref(a: &mut i32, b: &i32) -> i32 {
    *a = (*a).saturating_add(*b);
    *a
}

// Test 4: Returning a shared reference while another exists
// Demonstrates multiple shared refs can coexist (no aliasing VC needed)
fn get_ref_value(x: &i32, _y: &i32) -> i32 {
    *x
}

// Test 5: Split at mut semantics (inspired by slice::split_at_mut)
// The two resulting slices must be disjoint
fn set_left(left: &mut i32, _right: &mut i32, value: i32) {
    *left = value;
}

// Test 6: Three mutable references - pairwise non-aliasing required
// Generates 3 VCs: a!=b, a!=c, b!=c
fn increment_triple(a: &mut i32, b: &mut i32, c: &mut i32) {
    *a = (*a).saturating_add(1);
    *b = (*b).saturating_add(2);
    *c = (*c).saturating_add(3);
}

// Test 7: Mutable reference to struct field
struct Point {
    x: i32,
    y: i32,
}

fn sum_point(p: &Point) -> i32 {
    (p.x).saturating_add(p.y)
}

fn set_x(p: &mut Point, new_x: i32) {
    p.x = new_x;
}

// Test 8: Borrowing through method call pattern
fn identity_through_ref(value: &i32) -> i32 {
    *value
}

// Test 9: Sequential borrows are allowed (non-overlapping lifetimes)
fn sequential_borrows() {
    let mut x: i32 = 10;
    {
        let r1 = &mut x;
        *r1 = (*r1).saturating_add(1);
    } // r1 ends here
    {
        let r2 = &mut x;
        *r2 = (*r2).saturating_add(1);
    } // r2 ends here
    assert!(x == 12);
}

// Test 10: Nested references
fn double_deref_immut(r: &&i32) -> i32 {
    **r
}

fn double_deref_mut(r: &mut &mut i32, value: i32) {
    **r = value;
}

fn main() {
    // Test swap_values
    let mut a = 1;
    let mut b = 2;
    swap_values(&mut a, &mut b);
    assert!(a == 2 && b == 1);
    println!("swap_values: PASS");

    // Test increment_both
    let mut x = 10;
    let mut y = 20;
    increment_both(&mut x, &mut y);
    assert!(x == 11 && y == 21);
    println!("increment_both: PASS");

    // Test add_from_ref
    let mut m = 5;
    let n = 3;
    let result = add_from_ref(&mut m, &n);
    assert!(result == 8);
    println!("add_from_ref: PASS");

    // Test get_ref_value
    let p = 42;
    let q = 24;
    let val = get_ref_value(&p, &q);
    assert!(val == 42);
    println!("get_ref_value: PASS");

    // Test set_left
    let mut left = 0;
    let mut right = 0;
    set_left(&mut left, &mut right, 100);
    assert!(left == 100);
    println!("set_left: PASS");

    // Test increment_triple
    let mut t1 = 0;
    let mut t2 = 0;
    let mut t3 = 0;
    increment_triple(&mut t1, &mut t2, &mut t3);
    assert!(t1 == 1 && t2 == 2 && t3 == 3);
    println!("increment_triple: PASS");

    // Test Point operations
    let point = Point { x: 10, y: 20 };
    let sum = sum_point(&point);
    assert!(sum == 30);
    println!("sum_point: PASS");

    let mut point2 = Point { x: 0, y: 5 };
    set_x(&mut point2, 42);
    assert!(point2.x == 42);
    println!("set_x: PASS");

    // Test sequential borrows
    sequential_borrows();
    println!("sequential_borrows: PASS");

    // Test nested references
    let val = 100;
    let ref1 = &val;
    let ref2 = &&val;
    assert!(double_deref_immut(ref2) == 100);
    println!("double_deref_immut: PASS");

    let mut inner = 50;
    let mut outer = &mut inner;
    double_deref_mut(&mut outer, 99);
    assert!(inner == 99);
    println!("double_deref_mut: PASS");

    println!("\nAll borrow semantics tests passed!");
}
