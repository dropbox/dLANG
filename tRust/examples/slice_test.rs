// Test slice ([T]/&[T]) builtin contracts (Phase 10.1)
//
// Slice methods are modeled via length only:
// - [T]::get(i): returns Some iff i < len(self)
// - [T]::first/last: returns Some iff len(self) > 0
// - [T]::contains(x): empty slice => false; true => non-empty
//
// Element values are not modeled.

#![allow(unused)]

// =============================================================================
// [T]::get tests
// =============================================================================

// get(i) returns Some iff i < len(self)
// VERIFIED
#[requires("idx >= 0")]
#[ensures("idx < s.len() ==> result.is_some()")]
#[ensures("idx >= s.len() ==> result.is_none()")]
fn slice_get_some_iff_in_bounds(s: &[i32], idx: usize) -> Option<&i32> {
    s.get(idx)
}

// =============================================================================
// [T]::first / [T]::last tests
// =============================================================================

// first() returns Some iff slice is non-empty
// VERIFIED
#[ensures("result.is_some() == (!s.is_empty())")]
fn slice_first_some_iff_nonempty(s: &[i32]) -> Option<&i32> {
    s.first()
}

// last() returns Some iff slice is non-empty
// VERIFIED
#[ensures("result.is_some() == (!s.is_empty())")]
fn slice_last_some_iff_nonempty(s: &[i32]) -> Option<&i32> {
    s.last()
}

// =============================================================================
// [T]::contains tests
// =============================================================================

// contains(x) is always false on an empty slice
// VERIFIED
#[requires("s.is_empty()")]
#[ensures("!result")]
fn slice_contains_empty_is_false(s: &[i32]) -> bool {
    s.contains(&0)
}

// contains(x) being true implies the slice is non-empty
// VERIFIED
#[ensures("result ==> !s.is_empty()")]
fn slice_contains_true_implies_nonempty(s: &[i32]) -> bool {
    s.contains(&0)
}

fn main() {
    let arr = [1, 2, 3];
    let s: &[i32] = &arr[..];

    let _ = slice_get_some_iff_in_bounds(s, 0);
    let _ = slice_first_some_iff_nonempty(s);
    let _ = slice_last_some_iff_nonempty(s);

    let empty_arr: [i32; 0] = [];
    let empty: &[i32] = &empty_arr[..];
    let _ = slice_contains_empty_is_false(empty);
    let _ = slice_contains_true_implies_nonempty(s);
}

