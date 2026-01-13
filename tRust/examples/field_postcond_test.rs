//! Test struct field access in postconditions (Phase 2.5.3)
//!
//! This tests that we can reference struct fields in #[ensures] clauses
//! like `#[ensures("result.x == x")]` and nested fields like `#[ensures("result.origin.x == 0")]`
//!
//! make_point_x: @expect: VERIFIED
//! make_point: @expect: VERIFIED
//! origin_point: @expect: VERIFIED
//! next_x: @expect: VERIFIED
//! origin_rect: @expect: VERIFIED

#![allow(unused)]

struct Point {
    x: i32,
    y: i32,
}

// Test 1: Single field postcondition
#[ensures("result.x == x")]
fn make_point_x(x: i32, y: i32) -> Point {
    Point { x, y }
}

// Test 2: Two field postconditions
#[ensures("result.x == x")]
#[ensures("result.y == y")]
fn make_point(x: i32, y: i32) -> Point {
    Point { x, y }
}

// Test 3: Constant value postcondition
#[ensures("result.x == 0")]
#[ensures("result.y == 0")]
fn origin_point() -> Point {
    Point { x: 0, y: 0 }
}

// Test 4: Field with arithmetic postcondition (using regular add)
// Note: Verification proves result.x == x + 1 when no overflow
#[requires("x >= 0")]
#[requires("x < 2147483647")]  // Prevent overflow
#[ensures("result.x == x + 1")]
fn next_x(x: i32) -> Point {
    Point { x: x + 1, y: 0 }
}

// Test 5: Nested field postcondition
struct Rectangle {
    origin: Point,
    width: i32,
    height: i32,
}

#[requires("w > 0")]
#[requires("h > 0")]
#[ensures("result.origin.x == 0")]
#[ensures("result.origin.y == 0")]
fn origin_rect(w: i32, h: i32) -> Rectangle {
    Rectangle {
        origin: Point { x: 0, y: 0 },
        width: w,
        height: h,
    }
}

fn main() {
    let p = make_point(10, 20);
    println!("Point: ({}, {})", p.x, p.y);
}
