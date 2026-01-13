// Test file for L2: result.field with method calls (Solver Limitation L2)
//
// Tests that specs can access fields on result and call methods on those fields.
// These patterns are critical for rustc-index-verified integration.
//
// Fixed in Worker #305: Added vec::from_elem postcondition support for vec![elem; n] macro.
//
// Verified patterns:
// - result.field (simple struct field access)
// - result.field.len() == 0 (method on field with constant)
// - result.field.len() == n (method on field with parameter - requires from_elem tracking)
// - result.0 (tuple struct field access)
//
// Key addition: vec::from_elem builtin postcondition (= (len result) n)

#![allow(unused)]

// Baseline: simple struct field access
struct Wrapper {
    inner: usize,
}

#[ensures("result.inner == x")]
fn make_wrapper(x: usize) -> Wrapper {
    Wrapper { inner: x }
}

// L2: Vec field with .len() method call
struct VecWrapper {
    data: Vec<i32>,
}

// Empty Vec via Vec::new() - builtin postcondition len(result) == 0
#[ensures("result.data.len() == 0")]
fn make_empty_vec_wrapper() -> VecWrapper {
    VecWrapper { data: Vec::new() }
}

// Parameterized Vec via vec![elem; n] - NEW from_elem postcondition len(result) == n
#[requires("n < 1000")]
#[ensures("result.data.len() == n")]
fn make_vec_wrapper_n(n: usize) -> VecWrapper {
    VecWrapper { data: vec![0; n] }
}

// Tuple struct (newtype pattern) with .0 field access
struct Idx(usize);

#[ensures("result.0 == x")]
fn make_idx(x: usize) -> Idx {
    Idx(x)
}

// Pattern matching rustc_index::IndexVec
struct IndexVecLike {
    raw: Vec<u32>,
}

// Matches the pattern from rustc_index::IndexVec::new()
#[ensures("result.raw.len() == 0")]
fn make_index_vec_new() -> IndexVecLike {
    IndexVecLike { raw: Vec::new() }
}

fn main() {
    let w = make_wrapper(42);
    println!("Wrapper: inner = {}", w.inner);

    let vw = make_empty_vec_wrapper();
    println!("VecWrapper: len = {}", vw.data.len());

    let vw2 = make_vec_wrapper_n(5);
    println!("VecWrapper(5): len = {}", vw2.data.len());

    let idx = make_idx(100);
    println!("Idx: 0 = {}", idx.0);

    let ivl = make_index_vec_new();
    println!("IndexVecLike: raw.len = {}", ivl.raw.len());
}
