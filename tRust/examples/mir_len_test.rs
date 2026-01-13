//! Test MIR PtrMetadata (len) handling
//! In nightly rustc, arr.len() compiles to UnaryOp(PtrMetadata, ...).
//! This test verifies the verifier correctly interprets these operations.
//!
//! Expected outcomes:
//! returns_len: @expect: VERIFIED
//! len_equals_five: @expect: VERIFIED
//! len_in_condition: @expect: VERIFIED
//! len_mismatch_fail: @expect: DISPROVEN

/// Returns the length of a 5-element array
// #[ensures(result == 5)]
fn returns_len(arr: &[i32; 5]) -> usize {
    arr.len()
}

/// Uses len() in code and verifies it equals array size
// #[ensures(result == arr.len())]
fn len_equals_five(arr: &[i32; 5]) -> usize {
    let n = arr.len();
    n
}

/// Uses len() in a condition - returns 1 if len > 0, else 0
// #[ensures(result == 1)]
fn len_in_condition(arr: &[i32; 3]) -> i32 {
    if arr.len() > 0 {
        1
    } else {
        0
    }
}

/// Incorrectly claims the result is len + 1
// #[ensures(result == arr.len() + 1)]
fn len_mismatch_fail(arr: &[i32; 3]) -> usize {
    arr.len()  // Returns 3, not 4
}

fn main() {
    let a = [1, 2, 3, 4, 5];
    println!("len: {}", returns_len(&a));
    println!("len_equals: {}", len_equals_five(&a));

    let b = [10, 20, 30];
    println!("condition: {}", len_in_condition(&b));
    println!("mismatch: {}", len_mismatch_fail(&b));
}
