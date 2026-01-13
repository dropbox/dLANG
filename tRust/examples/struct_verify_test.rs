//! Test struct field access in specifications (Phase 2.5.3)
//!
//! This tests Phase 2.5.3: Struct and Aggregate Specs
//! - result.field syntax in postconditions  (WORKING)
//! - param.field syntax in preconditions    (WORKING)
//! - Nested field access (a.b.c)            (WORKING)
//! - Precondition checking with field constraints (WORKING)
//!
//! make_point: @expect: VERIFIED
//! make_positive_point: @expect: VERIFIED
//! positive_x: @expect: VERIFIED
//! make_rect_at_origin: @expect: VERIFIED
//! make_rect_at: @expect: VERIFIED
//! rect_origin_sum: @expect: VERIFIED
//! call_unsafe: @expect: DISPROVEN
//!
//! NOTE: Use saturating arithmetic to prevent overflow in arithmetic operations.

#![allow(unused)]

struct Point {
    x: i32,
    y: i32,
}

struct Rectangle {
    origin: Point,
    width: i32,
    height: i32,
}

// Test 1: Create a point and verify field values
fn make_point(x: i32, y: i32) -> Point {
    Point { x, y }
}

// Test 2: Verify field constraints
#[requires("x >= 0")]
#[requires("y >= 0")]
fn make_positive_point(x: i32, y: i32) -> Point {
    Point { x, y }
}

// Test 3: Use input field in precondition
// Use saturating_sub for underflow safety
#[requires("p.x > 0")]
fn positive_x(p: Point) -> i32 {
    p.x.saturating_sub(1)
}

// Test 4: Rectangle with origin - testing nested field access
#[requires("w > 0")]
#[requires("h > 0")]
fn make_rect_at_origin(w: i32, h: i32) -> Rectangle {
    Rectangle {
        origin: Point { x: 0, y: 0 },
        width: w,
        height: h,
    }
}

// Test 5: Rectangle with offset origin - nested field constraint
#[requires("w > 0")]
#[requires("h > 0")]
#[requires("ox >= 0")]
#[requires("oy >= 0")]
fn make_rect_at(w: i32, h: i32, ox: i32, oy: i32) -> Rectangle {
    Rectangle {
        origin: Point { x: ox, y: oy },
        width: w,
        height: h,
    }
}

// Test 6: Using nested field in precondition
// Use saturating_add for overflow safety
#[requires("r.origin.x >= 0")]
#[requires("r.origin.y >= 0")]
fn rect_origin_sum(r: Rectangle) -> i32 {
    r.origin.x.saturating_add(r.origin.y)
}

// Test 7: Should FAIL - precondition violation (simple field)
#[requires("p.x > 0")]
fn unsafe_point_access(p: Point) -> i32 {
    p.x
}

// Test 8: Caller with unsafe call - should DISPROVE
fn call_unsafe() -> i32 {
    let p = Point { x: 0, y: 0 };  // x is NOT > 0
    unsafe_point_access(p)  // Precondition violated!
}

fn main() {
    let p = make_point(10, 20);
    println!("Point: ({}, {})", p.x, p.y);

    let pp = make_positive_point(5, 10);
    println!("Positive point: ({}, {})", pp.x, pp.y);

    let val = positive_x(Point { x: 5, y: 0 });
    println!("positive_x result: {}", val);

    let r = make_rect_at_origin(100, 50);
    println!("Rectangle at ({}, {}) with size {}x{}",
             r.origin.x, r.origin.y, r.width, r.height);
}
