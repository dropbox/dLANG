// Test initial Vec<T> length/is_empty modeling (Phase 10.1)
//
// Current builtin modeling:
// - Vec::new / Vec::with_capacity: len(result) == 0
// - Vec::len: result == len(self)
// - Vec::is_empty: result == (len(self) == 0)
//
// Note: This only models length; element contents are not modeled.

// Vec::new().len() == 0
// VERIFIED
#[ensures("result == 0")]
fn vec_new_len_zero() -> usize {
    let v: Vec<i32> = Vec::new();
    v.len()
}

// Vec::new().is_empty() == true
// VERIFIED
#[ensures("result")]
fn vec_new_is_empty_true() -> bool {
    let v: Vec<i32> = Vec::new();
    v.is_empty()
}

// Vec::with_capacity(n).len() == 0
// VERIFIED
#[ensures("result == 0")]
fn vec_with_capacity_len_zero() -> usize {
    let v: Vec<i32> = Vec::with_capacity(10);
    v.len()
}

// Vec::with_capacity(n).is_empty() == true
// VERIFIED
#[ensures("result")]
fn vec_with_capacity_is_empty_true() -> bool {
    let v: Vec<i32> = Vec::with_capacity(10);
    v.is_empty()
}

// Local postconditions: v.len() == 0 and v.is_empty()
// VERIFIED
#[ensures("v.len() == 0")]
#[ensures("v.is_empty()")]
fn vec_new_local_postconditions() {
    let v: Vec<i32> = Vec::new();
    let _n = v.len();
}

fn main() {
    assert_eq!(vec_new_len_zero(), 0);
    assert!(vec_new_is_empty_true());
    assert_eq!(vec_with_capacity_len_zero(), 0);
    assert!(vec_with_capacity_is_empty_true());
    vec_new_local_postconditions();
}

