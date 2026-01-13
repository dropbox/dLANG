//! Array/slice indexing verification test
//! Tests parsing and verification of arr[i] syntax in specifications
//!
//! NOTE: Tests 1-3 use constant indices (0, 1, 2) which are statically known
//! to be within bounds of [i32; 3]. Test 4 requires a precondition.

#![allow(unused)]

// Test 1: Simple array access with constant index
// Constant index 0 is within bounds of length 3
fn first_element(arr: &[i32; 3]) -> i32 {
    arr[0]
}

// Test 2: Return specific element by index (constant)
// Constant index 1 is within bounds of length 3
fn second_element(arr: &[i32; 3]) -> i32 {
    arr[1]
}

// Test 3: Simple array creation and element access
// Constant index 0 is within bounds of length 3
fn create_and_access() -> i32 {
    let arr = [42, 10, 20];
    arr[0]
}

// Test 4: Variable index access with precondition
#[requires("i < 3")]
fn get_element(arr: &[i32; 3], i: usize) -> i32 {
    arr[i]
}

// Test 5: Array with struct elements - relates result to input
struct Pair {
    x: i32,
    y: i32,
}

// Note: This test shows the limit of verification for array + struct combinations.
fn first_pair(pairs: &[Pair; 2]) -> Pair {
    Pair { x: pairs[0].x, y: pairs[0].y }
}

fn main() {
    // Test first_element
    let arr = [1, 2, 3];
    println!("First: {}", first_element(&arr));

    // Test second_element
    println!("Second: {}", second_element(&arr));

    // Test create_and_access
    println!("Created: {}", create_and_access());

    // Test get_element
    println!("Element[1]: {}", get_element(&arr, 1));

    // Test first_pair
    let pairs = [Pair { x: 10, y: 20 }, Pair { x: 30, y: 40 }];
    let p = first_pair(&pairs);
    println!("Pair: ({}, {})", p.x, p.y);
}
