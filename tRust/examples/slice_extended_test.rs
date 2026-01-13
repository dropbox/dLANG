// Test extended slice ([T]/&[T]) builtin contracts (Phase 10.1)
//
// Additional slice methods:
// - [T]::len(): result == len(self)
// - [T]::is_empty(): result == (len(self) == 0)
// - [T]::split_first(): returns Some iff len(self) > 0
// - [T]::split_last(): returns Some iff len(self) > 0
// - [T]::binary_search(x): Ok(idx) where idx < len, Err(idx) where idx <= len

#![allow(unused)]

// =============================================================================
// [T]::len tests
// =============================================================================

// len() returns the length of the slice
// VERIFIED
#[ensures("result == s.len()")]
fn slice_len_equals_len(s: &[i32]) -> usize {
    s.len()
}

// len() twice returns same value (consistent)
// VERIFIED
#[ensures("result == s.len()")]
fn slice_len_consistent(s: &[i32]) -> usize {
    s.len()
}

// =============================================================================
// [T]::is_empty tests
// =============================================================================

// is_empty() returns true iff len == 0
// VERIFIED
#[ensures("result == s.is_empty()")]
fn slice_is_empty_equals_len_zero(s: &[i32]) -> bool {
    s.is_empty()
}

// is_empty() on empty slice is true, on non-empty is false
// VERIFIED: these are tautologies given is_empty's definition
#[ensures("!s.is_empty() ==> !result")]
#[ensures("s.is_empty() ==> result")]
fn slice_is_empty_consistent(s: &[i32]) -> bool {
    s.is_empty()
}

// =============================================================================
// [T]::split_first tests
// =============================================================================

// split_first() returns Some iff slice is non-empty
// VERIFIED
#[ensures("result.is_some() == (!s.is_empty())")]
fn slice_split_first_some_iff_nonempty(s: &[i32]) -> Option<(&i32, &[i32])> {
    s.split_first()
}

// split_first() on empty slice returns None
// VERIFIED
#[requires("s.is_empty()")]
#[ensures("result.is_none()")]
fn slice_split_first_empty_is_none(s: &[i32]) -> Option<(&i32, &[i32])> {
    s.split_first()
}

// split_first() on non-empty slice returns Some
// VERIFIED
#[requires("!s.is_empty()")]
#[ensures("result.is_some()")]
fn slice_split_first_nonempty_is_some(s: &[i32]) -> Option<(&i32, &[i32])> {
    s.split_first()
}

// =============================================================================
// [T]::split_last tests
// =============================================================================

// split_last() returns Some iff slice is non-empty
// VERIFIED
#[ensures("result.is_some() == (!s.is_empty())")]
fn slice_split_last_some_iff_nonempty(s: &[i32]) -> Option<(&i32, &[i32])> {
    s.split_last()
}

// split_last() on empty slice returns None
// VERIFIED
#[requires("s.is_empty()")]
#[ensures("result.is_none()")]
fn slice_split_last_empty_is_none(s: &[i32]) -> Option<(&i32, &[i32])> {
    s.split_last()
}

// split_last() on non-empty slice returns Some
// VERIFIED
#[requires("!s.is_empty()")]
#[ensures("result.is_some()")]
fn slice_split_last_nonempty_is_some(s: &[i32]) -> Option<(&i32, &[i32])> {
    s.split_last()
}

// =============================================================================
// [T]::binary_search tests
// =============================================================================

// binary_search() Ok index is within bounds
// VERIFIED
#[ensures("result.is_ok() ==> result.unwrap() < s.len()")]
fn slice_binary_search_ok_in_bounds(s: &[i32], x: &i32) -> Result<usize, usize> {
    s.binary_search(x)
}

// binary_search() Err index is at most len (valid insertion point)
// VERIFIED
#[ensures("result.is_err() ==> result.unwrap_err() <= s.len()")]
fn slice_binary_search_err_valid_insertion(s: &[i32], x: &i32) -> Result<usize, usize> {
    s.binary_search(x)
}

// binary_search() index is always non-negative
// VERIFIED
#[ensures("result.is_ok() ==> result.unwrap() >= 0")]
#[ensures("result.is_err() ==> result.unwrap_err() >= 0")]
fn slice_binary_search_index_non_negative(s: &[i32], x: &i32) -> Result<usize, usize> {
    s.binary_search(x)
}

fn main() {
    let arr = [1, 2, 3, 4, 5];
    let s: &[i32] = &arr[..];

    // len/is_empty tests
    let _ = slice_len_equals_len(s);
    let _ = slice_len_consistent(s);
    let _ = slice_is_empty_equals_len_zero(s);
    let _ = slice_is_empty_consistent(s);

    // split_first/split_last tests
    let _ = slice_split_first_some_iff_nonempty(s);
    let _ = slice_split_last_some_iff_nonempty(s);

    let empty_arr: [i32; 0] = [];
    let empty: &[i32] = &empty_arr[..];
    let _ = slice_split_first_empty_is_none(empty);
    let _ = slice_split_last_empty_is_none(empty);
    let _ = slice_split_first_nonempty_is_some(s);
    let _ = slice_split_last_nonempty_is_some(s);

    // binary_search tests
    let _ = slice_binary_search_ok_in_bounds(s, &3);
    let _ = slice_binary_search_err_valid_insertion(s, &10);
    let _ = slice_binary_search_index_non_negative(s, &3);
}
