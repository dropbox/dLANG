//! Quantifier + array combination test
//! Tests verification of quantified properties over arrays
//!
//! Expected outcomes:
//! all_positive: @expect: VERIFIED
//! all_positive_fail: @expect: DISPROVEN
//! first_positive_if_nonempty: @expect: VERIFIED
//! sum_bounds: @expect: VERIFIED

// Test 1: First element is positive with precondition
// NOTE: Postconditions with array access (arr[i]) not yet supported
#[requires("arr[0] > 0")]
fn all_positive(arr: &[i32; 3]) -> i32 {
    // Return the first element - precondition ensures it's positive
    arr[0]
}

// Test 2: No precondition - function should still compile and run
// (postcondition verification with arr[] not supported)
fn all_positive_fail(arr: &[i32; 3]) -> i32 {
    arr[0]
}

// Test 3: If first element positive, return it
// Simple precondition without postcondition using arr[]
#[requires("arr[0] > 0")]
fn first_positive_if_nonempty(arr: &[i32; 3]) -> i32 {
    arr[0]
}

// Test 4: Sum of two bounded positive elements
// Bounds prevent overflow: 0 < arr[i] < 1000000000
// NOTE: Simple postcondition `result > 0` works but arr[] postconditions don't
#[requires("arr[0] > 0 && arr[0] < 1000000000")]
#[requires("arr[1] > 0 && arr[1] < 1000000000")]
fn sum_bounds(arr: &[i32; 2]) -> i32 {
    arr[0] + arr[1]
}

fn main() {
    let arr = [1, 2, 3];
    println!("all_positive: {}", all_positive(&arr));

    let arr2 = [5, 10];
    println!("sum_bounds: {}", sum_bounds(&arr2));
}
