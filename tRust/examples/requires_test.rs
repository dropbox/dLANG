// Test file for #[requires] precondition integration with auto-verification
//
// This file tests that #[requires] preconditions are used to constrain
// the SMT solver queries in automatic overflow and bounds checking.
//
// OVERFLOW CHECKS - SHOULD PASS (precondition constrains inputs):
// - add_with_requires: a < 100 && b < 100 constrains inputs, so a+b <= 198 < 255
// - sub_with_requires: b <= a ensures no underflow
// - div_with_requires: b != 0 ensures no division by zero
//
// OVERFLOW CHECKS - SHOULD FAIL (no precondition or insufficient precondition):
// - add_no_requires: no constraint on inputs, overflow possible
// - add_weak_requires: a < 200 && b < 200 still allows overflow (199+199=398 > 255)
//
// BOUNDS CHECKS - SHOULD PASS (fixed-size array, length known from type):
// - index_with_requires: i < 3, array is [i32; 3], so i < len is provable
//
// BOUNDS CHECKS - SHOULD FAIL:
// - index_no_requires: no precondition, could be out of bounds
// - combined_requires: slice (not fixed array), length unknown statically
//   Note: For slices, the actual length comes from Len(arr) in MIR, which is
//   not connected to a user parameter. Use fixed-size arrays for static bounds.

// SHOULD PASS - precondition constrains both operands
#[requires("a < 100 && b < 100")]
fn add_with_requires(a: u8, b: u8) -> u8 {
    a + b  // OK: max is 99+99=198 < 255
}

// SHOULD PASS - precondition prevents underflow
#[requires("b <= a")]
fn sub_with_requires(a: u8, b: u8) -> u8 {
    a - b  // OK: b <= a means result >= 0
}

// SHOULD PASS - precondition constrains index within bounds
#[requires("i < 3")]
fn index_with_requires(arr: &[i32; 3], i: usize) -> i32 {
    arr[i]  // OK: i < 3 means i is within bounds
}

// SHOULD FAIL - no precondition means overflow is possible
fn add_no_requires(a: u8, b: u8) -> u8 {
    a + b  // ERROR: could overflow
}

// SHOULD FAIL - no precondition means out-of-bounds is possible
fn index_no_requires(arr: &[i32; 3], i: usize) -> i32 {
    arr[i]  // ERROR: i could be >= 3
}

// SHOULD FAIL - precondition too weak, still allows overflow
#[requires("a < 200 && b < 200")]
fn add_weak_requires(a: u8, b: u8) -> u8 {
    a + b  // ERROR: 199+199=398 > 255
}

// SHOULD PASS - division with non-zero divisor precondition
#[requires("b != 0")]
fn div_with_requires(a: u32, b: u32) -> u32 {
    a / b  // OK: b != 0 means no division by zero
}

// SHOULD FAIL - slice length unknown statically (see file header comment)
// This demonstrates a limitation: for slices, we can't connect user parameters
// to the actual slice length. Use fixed-size arrays instead.
#[requires("i < len && len <= 100")]
#[allow(unused_variables)]
fn combined_requires(arr: &[i32], i: usize, len: usize) -> i32 {
    // Note: The `len` parameter is not automatically connected to arr.len()
    // For slices, the actual length in MIR comes from Len(arr), not a parameter
    arr[i]  // EXPECTED FAIL: slice length unknown
}

fn main() {
    println!("add_with_requires(50, 50) = {}", add_with_requires(50, 50));
    println!("sub_with_requires(100, 50) = {}", sub_with_requires(100, 50));
    let arr = [1, 2, 3];
    println!("index_with_requires(&arr, 1) = {}", index_with_requires(&arr, 1));
    println!("div_with_requires(10, 2) = {}", div_with_requires(10, 2));
}
