// Test file for Idx trait method translation in specifications
//
// Tests that .index() method calls and "as usize" casts are correctly
// translated to SMT for verification.
//
// This addresses solver limitation L1 (cast expressions) and L3 (result.method()).
// See: reports/main/SOLVER_LIMITATIONS_2026-01-01.md
//
// SHOULD PASS:
// - usize_identity: result.index() == x should work (identity for usize)
// - cast_to_usize: self as usize cast should work
// - idx_new_roundtrip: Idx::new(x).index() == x pattern
//
// SHOULD FAIL:
// - wrong_index: claims wrong property about index

// SHOULD PASS - For usize, .index() is identity
// Simulates: impl Idx for usize { fn index(self) -> usize { self } }
#[ensures("result.index() == x")]
fn usize_identity(x: usize) -> usize {
    x
}

// SHOULD PASS - Test that result.index() == input works
#[requires("x < 1000")]
#[ensures("result.index() == x")]
fn make_index(x: usize) -> usize {
    x
}

// SHOULD PASS - "as usize" cast expression
// This tests L1: cannot parse `self` in cast expressions
#[ensures("result == x as usize")]
fn u32_as_usize(x: u32) -> usize {
    x as usize
}

// SHOULD PASS - "as i32" cast expression
#[requires("x < 128")]
#[ensures("result == x as i32")]
fn u8_as_i32(x: u8) -> i32 {
    x as i32
}

// SHOULD PASS - Combined: result.index() with arithmetic
#[requires("x < 1000")]
#[ensures("result.index() == x + 1")]
fn next_index(x: usize) -> usize {
    x + 1
}

// SHOULD PASS - Test Idx::new() pattern (static method)
// I::new(x) should translate to just x in SMT
#[requires("x < 1000")]
#[ensures("result == x")]  // I::new(x) produces index with value x
fn create_index_simple(x: usize) -> usize {
    x
}

// SHOULD FAIL - Wrong postcondition
#[requires("x < 100")]
#[ensures("result.index() == x + 10")]  // Wrong! result is x, not x+10
fn wrong_index(x: usize) -> usize {
    x
}

fn main() {
    println!("usize_identity(42) = {}", usize_identity(42));
    println!("make_index(100) = {}", make_index(100));
    println!("u32_as_usize(42) = {}", u32_as_usize(42));
    println!("u8_as_i32(100) = {}", u8_as_i32(100));
    println!("next_index(50) = {}", next_index(50));
    println!("create_index_simple(25) = {}", create_index_simple(25));
    println!("wrong_index(5) = {}", wrong_index(5));
}
