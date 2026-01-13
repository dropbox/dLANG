// Test file for constant propagation in auto-verification
//
// This file demonstrates how constant propagation reduces false positives
// by tracking constant values through MIR locals, including tuple field extraction.
//
// SHOULD PASS (constant propagation proves safety):
// - safe_constant_index: arr[0] with len=3 (direct constant)
// - safe_last_index: arr[2] with len=3 (direct constant)
// - safe_constant_add: 100_u8 + 50_u8 (direct constants, no overflow)
// - computed_constant_index: 1+1=2 index with len=5 (tuple field tracking)
// - computed_subtraction_index: 3-1=2 index with len=5 (SubWithOverflow tuple)
// - computed_multiplication_index: 2*1=2 index with len=5 (MulWithOverflow tuple)
//
// SHOULD FAIL (true positives):
// - oob_constant_index: arr[3] with len=3 (constant propagation correctly detects)
// - variable_index: arr[i] where i is parameter (could be >= len)
// - variable_add: a + b where a,b are parameters (could overflow)

// SHOULD PASS - constant index 0 is within bounds of length 3
fn safe_constant_index() -> i32 {
    let arr = [10, 20, 30];
    arr[0]  // OK: constant propagation knows index=0, len=3
}

// SHOULD PASS - constant index 2 is within bounds of length 3
fn safe_last_index() -> i32 {
    let arr = [10, 20, 30];
    arr[2]  // OK: constant propagation knows index=2, len=3
}

// SHOULD FAIL - constant index 3 is OUT of bounds for length 3
fn oob_constant_index() -> i32 {
    let arr = [10, 20, 30];
    arr[3]  // ERROR: index 3 >= length 3
}

// SHOULD FAIL - variable index could be out of bounds
fn variable_index(arr: &[i32; 3], i: usize) -> i32 {
    arr[i]  // ERROR: i could be >= 3
}

// SHOULD PASS - constant arithmetic doesn't overflow
fn safe_constant_add() -> u8 {
    let a: u8 = 100;
    let b: u8 = 50;
    a + b  // OK: 100 + 50 = 150 < 255
}

// SHOULD PASS - computed constant via AddWithOverflow tuple
// MIR transforms `1 + 1` to AddWithOverflow which returns a tuple (result, overflow_flag),
// and our constant propagation now tracks tuple field extraction.
fn computed_constant_index() -> i32 {
    let arr = [1, 2, 3, 4, 5];
    let idx = 1 + 1;  // idx = 2, MIR: _3 = AddWithOverflow(1, 1); _2 = (_3.0)
    arr[idx]  // OK: tuple tracking knows idx=2, len=5, 2 < 5
}

// SHOULD PASS - computed constant via SubWithOverflow tuple
fn computed_subtraction_index() -> i32 {
    let arr = [1, 2, 3, 4, 5];
    let idx = 3 - 1;  // idx = 2, MIR: _3 = SubWithOverflow(3, 1); _2 = (_3.0)
    arr[idx]  // OK: tuple tracking knows idx=2, len=5, 2 < 5
}

// SHOULD PASS - computed constant via MulWithOverflow tuple
fn computed_multiplication_index() -> i32 {
    let arr = [1, 2, 3, 4, 5];
    let idx = 2 * 1;  // idx = 2, MIR: _3 = MulWithOverflow(2, 1); _2 = (_3.0)
    arr[idx]  // OK: tuple tracking knows idx=2, len=5, 2 < 5
}

// SHOULD FAIL - variable arithmetic could overflow
fn variable_add(a: u8, b: u8) -> u8 {
    a + b  // ERROR: a + b could exceed 255
}

fn main() {
    println!("safe_constant_index() = {}", safe_constant_index());
    println!("safe_last_index() = {}", safe_last_index());
    // Note: oob_constant_index would panic at runtime - don't call it
    println!("safe_constant_add() = {}", safe_constant_add());
    println!("computed_constant_index() = {}", computed_constant_index());
    println!("computed_subtraction_index() = {}", computed_subtraction_index());
    println!("computed_multiplication_index() = {}", computed_multiplication_index());
}
