//! Array Indexing in Preconditions Test
//!
//! This tests the array indexing syntax (arr[i]) in #[requires] attributes.
//! Array access is translated to SMT-LIB select: arr[i] -> (select arr i)
//!
//! NOTE: Postconditions with array access (ensures with arr[i]) are NOT yet supported
//! in kani_bridge.rs. This test focuses on preconditions only.
//!
//! Run with: rustc examples/array_index_spec_test.rs -Zverify
//!
//! Expected outcomes:
//! All functions should VERIFY (no overflow/underflow errors) because
//! the preconditions constrain the array elements appropriately.

#![allow(unused)]

/// Sum of first two elements bounded to prevent overflow
/// Precondition: arr[0] >= 0 && arr[1] >= 0 && arr[0] + arr[1] < 100
/// This proves the addition cannot overflow (result < 100 < 255)
#[requires("arr[0] >= 0")]
#[requires("arr[1] >= 0")]
#[requires("arr[0] + arr[1] < 100")]
fn sum_bounded(arr: &[u8; 3]) -> u8 {
    arr[0] + arr[1]
}

/// Element at index i - precondition constrains both i and element
/// i < 3 ensures valid index (though compiler checks this at runtime)
/// arr[i] >= 0 could be used for downstream reasoning
#[requires("i < 3")]
#[requires("arr[i] >= 0")]
fn index_with_var(arr: &[i32; 4], i: usize) -> i32 {
    arr[i]
}

/// Two array parameters with element comparison
/// a[0] > b[0] means a[0] - b[0] > 0, proving no underflow for positive result
/// However, we also need a[0] < MAX and b[0] > MIN to prove no overflow
#[requires("a[0] >= 0")]
#[requires("b[0] >= 0")]
#[requires("a[0] > b[0]")]
fn compare_safe(a: &[i32; 2], b: &[i32; 2]) -> i32 {
    a[0] - b[0]
}

/// Addition of two array elements with explicit overflow prevention
#[requires("arr[0] >= 0")]
#[requires("arr[0] < 128")]
#[requires("arr[1] >= 0")]
#[requires("arr[1] < 128")]
fn add_bounded(arr: &[u8; 2]) -> u8 {
    arr[0] + arr[1]
}

fn main() {
    let arr2 = [10u8, 20, 30];
    println!("sum_bounded: {}", sum_bounded(&arr2));

    let arr3 = [1, 2, 3, 4];
    println!("index_with_var: {}", index_with_var(&arr3, 1));

    let a = [10, 0];
    let b = [5, 0];
    println!("compare_safe: {}", compare_safe(&a, &b));

    let arr4 = [50u8, 60];
    println!("add_bounded: {}", add_bounded(&arr4));
}
