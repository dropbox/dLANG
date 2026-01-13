//! Integration test for Vec/slice sorting and reverse contracts (Phase 10.1)
//!
//! Tests that sort, sort_unstable, sort_by, reverse, rotate, and similar
//! methods preserve the length of vectors and slices.
//!
//! All functions should verify as PROVEN since sorting/reversing only
//! reorders elements without changing the container's length.

#![allow(unused)]

// ===== Vec::sort preserves length =====

/// Vec::sort preserves length - return sorted vec
#[ensures("result.len() == 3")]
fn vec_sort_return() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(3);
    v.push(1);
    v.push(2);
    v.sort();
    v
}

/// Vec::sort_unstable preserves length - return sorted vec
#[ensures("result.len() == 3")]
fn vec_sort_unstable_return() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(3);
    v.push(1);
    v.push(2);
    v.sort_unstable();
    v
}

/// Vec::sort_by preserves length
#[ensures("result.len() == 3")]
fn vec_sort_by_return() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(3);
    v.push(1);
    v.push(2);
    v.sort_by(|a, b| a.cmp(b));
    v
}

/// Vec::sort_unstable_by preserves length
#[ensures("result.len() == 3")]
fn vec_sort_unstable_by_return() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(3);
    v.push(1);
    v.push(2);
    v.sort_unstable_by(|a, b| a.cmp(b));
    v
}

// ===== Vec::reverse preserves length =====

/// Vec::reverse preserves length
#[ensures("result.len() == 3")]
fn vec_reverse_return() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.reverse();
    v
}

/// Vec::reverse on empty vec - still empty
#[ensures("result.len() == 0")]
fn vec_reverse_empty() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.reverse();
    v
}

// ===== Vec::split_off =====

/// Vec::split_off splits at index
/// After split_off(1) on a 3-element vec, self has 1 element
#[ensures("result.len() == 1")]
fn vec_split_off_self() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    let _second = v.split_off(1);
    v
}

/// Vec::split_off returns the second part
/// After split_off(1) on a 3-element vec, returned vec has 2 elements
#[ensures("result.len() == 2")]
fn vec_split_off_returned() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.split_off(1)
}

// ===== Combined operations =====

/// Sort then reverse preserves length
#[ensures("result.len() == 3")]
fn vec_sort_then_reverse() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(3);
    v.push(1);
    v.push(2);
    v.sort();
    v.reverse();
    v
}

/// Multiple sorts preserve length
#[ensures("result.len() == 3")]
fn vec_multiple_sorts() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(3);
    v.push(1);
    v.push(2);
    v.sort();
    v.sort_unstable();
    v.sort();
    v
}

/// Push after sort preserves expected length
#[ensures("result.len() == 4")]
fn vec_sort_then_push() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(3);
    v.push(1);
    v.push(2);
    v.sort();
    v.push(4);
    v
}

/// Reverse then push preserves expected length
#[ensures("result.len() == 4")]
fn vec_reverse_then_push() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.push(3);
    v.push(1);
    v.push(2);
    v.reverse();
    v.push(4);
    v
}

fn main() {
    // Runtime tests - call functions to exercise the verified code
    let _ = vec_sort_return();
    let _ = vec_sort_unstable_return();
    let _ = vec_sort_by_return();
    let _ = vec_sort_unstable_by_return();
    let _ = vec_reverse_return();
    let _ = vec_reverse_empty();
    let _ = vec_split_off_self();
    let _ = vec_split_off_returned();
    let _ = vec_sort_then_reverse();
    let _ = vec_multiple_sorts();
    let _ = vec_sort_then_push();
    let _ = vec_reverse_then_push();
}
