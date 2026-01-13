//! Array Indexing in Postconditions Test
//!
//! This tests that the array/slice indexing syntax `arr[i]` is supported in:
//! - `#[requires("...")]`
//! - `#[ensures("...")]`
//!
//! Array access in specs is translated to an uninterpreted function:
//!   arr[i] -> (at arr i)
//!
//! Run with: rustc examples/array_index_postcondition_test.rs -Zverify
//!
//! Expected outcomes:
//! All functions should VERIFY.

#![allow(unused)]

/// Preconditions can constrain array elements and postconditions can reference them.
#[requires("arr[0] >= 0")]
#[ensures("arr[0] >= 0")]
fn postcond_reuses_precond(arr: &[i32; 4]) -> i32 {
    let _ = arr.get(0);
    0
}

/// Variable indices in array expressions are allowed in postconditions.
#[requires("i >= 0 && i < 4")]
#[ensures("arr[i] == arr[i]")]
fn postcond_tautology_var_index(arr: &[i32; 4], i: usize) -> i32 {
    let _ = (arr.get(0), i);
    0
}

/// Chained indexing is translated as nested selects.
#[requires("i >= 0 && i < 4")]
#[requires("j >= 0 && j < 4")]
#[ensures("mat[i][j] == mat[i][j]")]
fn postcond_tautology_nested_index(mat: &[[i32; 4]; 4], i: usize, j: usize) -> i32 {
    let _ = (mat.get(0), i, j);
    0
}

fn main() {
    let arr = [1, 2, 3, 4];
    let _ = postcond_reuses_precond(&arr);
    let _ = postcond_tautology_var_index(&arr, 2);

    let mat = [[0i32; 4]; 4];
    let _ = postcond_tautology_nested_index(&mat, 1, 3);
}
