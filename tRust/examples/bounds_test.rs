// Test file for automatic array bounds checking
// This file demonstrates what tRust should detect automatically
//
// TRUE POSITIVES (should be detected):
// - Variable indices into arrays
// - Variable indices into slices (unknown length)
//
// FALSE POSITIVES (known limitation - MIR transforms constants to variables):
// - Constant indices that are within bounds
//
// This is a first implementation; future work can add constant propagation.

// This function should FAIL verification - index could be out of bounds
fn get_element(arr: &[i32; 3], i: usize) -> i32 {
    arr[i]  // ERROR: i could be >= 3
}

// This function should FAIL - slice length is unknown
fn get_from_slice(arr: &[i32], i: usize) -> i32 {
    arr[i]  // ERROR: i could be >= arr.len()
}

// This function uses safe access - should PASS (no bounds check in MIR)
fn safe_get(arr: &[i32], i: usize) -> Option<&i32> {
    arr.get(i)  // OK: returns None if out of bounds
}

fn main() {
    let arr3 = [1, 2, 3];
    println!("get_element([1,2,3], 1) = {}", get_element(&arr3, 1));

    let slice: &[i32] = &arr3[..];
    println!("get_from_slice(slice, 2) = {}", get_from_slice(slice, 2));

    println!("safe_get(slice, 10) = {:?}", safe_get(slice, 10));
}
