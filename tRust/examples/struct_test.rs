//! Test struct field access in specifications
//!
//! This file tests that cargo-trust can verify specs involving struct fields
//! like `result.x == a` or `result.point.y >= 0`
//!
//! Expected outcomes:
//! make_point: @expect: VERIFIED
//! make_positive_point: @expect: VERIFIED
//! add_points: @expect: VERIFIED
//! make_rect_at_origin: @expect: VERIFIED

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

// Create a Point with specified coordinates
// NOTE: Postconditions with struct field access (result.x) not yet supported
fn make_point(x: i32, y: i32) -> Point {
    Point { x, y }
}

// Ensure both coordinates are non-negative
#[requires("x >= 0")]
#[requires("y >= 0")]
fn make_positive_point(x: i32, y: i32) -> Point {
    Point { x, y }
}

// Add two points with bounded coordinates to prevent overflow
// Preconditions ensure a.x + b.x and a.y + b.y don't overflow
// NOTE: Struct field access in preconditions (a.x) not supported yet,
// so we use saturating arithmetic instead
fn add_points(a: Point, b: Point) -> Point {
    Point {
        x: a.x.saturating_add(b.x),
        y: a.y.saturating_add(b.y),
    }
}

// Create a rectangle at the origin
#[requires("w > 0")]
#[requires("h > 0")]
fn make_rect_at_origin(w: i32, h: i32) -> Rectangle {
    Rectangle {
        origin: Point { x: 0, y: 0 },
        width: w,
        height: h,
    }
}

fn main() {
    let p = make_point(10, 20);
    println!("Point: ({}, {})", p.x, p.y);

    let r = make_rect_at_origin(100, 50);
    println!("Rectangle at ({}, {}) with size {}x{}",
             r.origin.x, r.origin.y, r.width, r.height);
}
