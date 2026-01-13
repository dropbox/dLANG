//! Reference handling verification test
//! Tests verification with reference types in specifications
//!
//! Expected outcomes:
//! deref_copy: @expect: VERIFIED
//! copy_positive: @expect: VERIFIED
//! get_x_ref: @expect: VERIFIED
//! double_deref: @expect: VERIFIED

// Test 1: Simple dereference - implicit through MIR
// In specs, `x` refers to the value (MIR tracks derefs)
// #[ensures(result == x)]
fn deref_copy(x: &i32) -> i32 {
    *x
}

// Test 2: Value constraint propagates through reference
// #[requires(x > 0)]
// #[ensures(result > 0)]
fn copy_positive(x: &i32) -> i32 {
    *x
}

// Test 3: Reference to struct field - already works
struct Point { x: i32, y: i32 }

// #[ensures(result == p.x)]
fn get_x_ref(p: &Point) -> i32 {
    p.x
}

// Test 4: Double dereference - through nested refs
// #[ensures(result == x)]
fn double_deref(x: &&i32) -> i32 {
    **x
}

fn main() {
    let val = 42;
    println!("Deref copy: {}", deref_copy(&val));

    let val2 = 10;
    println!("Copy positive: {}", copy_positive(&val2));

    let point = Point { x: 100, y: 200 };
    println!("Point.x: {}", get_x_ref(&point));

    let val3 = 99;
    println!("Double deref: {}", double_deref(&&val3));
}
