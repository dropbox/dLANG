//! Test for deep field path support (Phase 11.3 / L6 Fix)
//!
//! This test verifies that specifications can reference fields at 3+ levels deep.
//! Previously L6 limitation blocked specs like `result.a.b.c`.
//!
//! Status: VERIFIED (L6 fix complete)
//! Expected: All functions VERIFIED

#![allow(dead_code)]

// Level 3: result.a.b.c
pub struct Level3A { pub b: Level3B }
pub struct Level3B { pub c: Level3C }
pub struct Level3C { pub value: i32 }

// @expect: VERIFIED
#[ensures("result.b.c.value == 42")]
pub fn three_levels() -> Level3A {
    Level3A { b: Level3B { c: Level3C { value: 42 } } }
}

// Level 4: result.a.b.c.d
pub struct Level4A { pub b: Level4B }
pub struct Level4B { pub c: Level4C }
pub struct Level4C { pub d: Level4D }
pub struct Level4D { pub value: usize }

// @expect: VERIFIED
#[ensures("result.b.c.d.value == 100")]
pub fn four_levels() -> Level4A {
    Level4A { b: Level4B { c: Level4C { d: Level4D { value: 100 } } } }
}

// Level 5: result.v.w.x.y.z
pub struct Level5V { pub w: Level5W }
pub struct Level5W { pub x: Level5X }
pub struct Level5X { pub y: Level5Y }
pub struct Level5Y { pub z: Level5Z }
pub struct Level5Z { pub value: u32 }

// @expect: VERIFIED
#[ensures("result.w.x.y.z.value == 999")]
pub fn five_levels() -> Level5V {
    Level5V { w: Level5W { x: Level5X { y: Level5Y { z: Level5Z { value: 999 } } } } }
}

// Mixed types at different levels
pub struct Outer { pub inner: Inner }
pub struct Inner { pub data: Data }
pub struct Data { pub x: i32, pub y: i32 }

// @expect: VERIFIED
#[ensures("result.inner.data.x == 10 && result.inner.data.y == 20")]
pub fn mixed_fields() -> Outer {
    Outer { inner: Inner { data: Data { x: 10, y: 20 } } }
}

// Using deep paths with comparison
// @expect: VERIFIED
#[ensures("result.inner.data.x < result.inner.data.y")]
pub fn deep_comparison() -> Outer {
    Outer { inner: Inner { data: Data { x: 5, y: 15 } } }
}

// Parameter-dependent deep path
// @expect: VERIFIED
#[ensures("result.b.c.value == n")]
pub fn parametric_deep(n: i32) -> Level3A {
    Level3A { b: Level3B { c: Level3C { value: n } } }
}

fn main() {
    println!("three_levels().b.c.value = {}", three_levels().b.c.value);
    println!("four_levels().b.c.d.value = {}", four_levels().b.c.d.value);
    println!("five_levels().w.x.y.z.value = {}", five_levels().w.x.y.z.value);
    println!("mixed_fields().inner.data.x = {}", mixed_fields().inner.data.x);
    println!("deep_comparison().inner.data = ({}, {})",
             deep_comparison().inner.data.x,
             deep_comparison().inner.data.y);
    println!("parametric_deep(77).b.c.value = {}", parametric_deep(77).b.c.value);
}
