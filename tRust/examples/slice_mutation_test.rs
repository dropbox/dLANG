// Test slice mutation methods that preserve length (Phase 10.1)
//
// Tests for:
// - [T]::clone_from_slice(&mut self, src): length is preserved
// - [T]::fill_with(&mut self, f): length is preserved
// - [T]::copy_within<R>(&mut self, src: R, dest: usize): length is preserved
//
// All of these operations preserve the length of the slice.

#![allow(unused)]

// =============================================================================
// [T]::clone_from_slice tests
// =============================================================================

// clone_from_slice preserves length (length == 3 before and after)
// VERIFIED
#[ensures("result.len() == 3")]
fn slice_clone_from_slice_preserves_len() -> Vec<i32> {
    let mut v = Vec::new();
    v.push(0);
    v.push(0);
    v.push(0);
    let src = [4, 5, 6];
    v.clone_from_slice(&src);
    v
}

// clone_from_slice on empty slices
// VERIFIED
#[ensures("result.is_empty()")]
fn slice_clone_from_slice_empty() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    let src: [i32; 0] = [];
    v.clone_from_slice(&src);
    v
}

// clone_from_slice combined with resize
// VERIFIED
#[ensures("result.len() == 5")]
fn slice_clone_from_slice_after_resize() -> Vec<i32> {
    let mut v = Vec::new();
    v.resize(5, 0);
    let src = [1, 2, 3, 4, 5];
    v.clone_from_slice(&src);
    v
}

// clone_from_slice with push setup
// VERIFIED
#[ensures("result.len() == 4")]
fn slice_clone_from_slice_after_push() -> Vec<i32> {
    let mut v = Vec::new();
    v.push(0);
    v.push(0);
    v.push(0);
    v.push(0);
    let src = [10, 20, 30, 40];
    v.clone_from_slice(&src);
    v
}

// =============================================================================
// [T]::fill_with tests
// =============================================================================

// fill_with preserves length (length == 5 before and after)
// VERIFIED
#[ensures("result.len() == 5")]
fn slice_fill_with_preserves_len() -> Vec<i32> {
    let mut v = Vec::new();
    v.resize(5, 0);
    v.fill_with(|| 42);
    v
}

// fill_with on empty Vec remains empty
// VERIFIED
#[ensures("result.is_empty()")]
fn slice_fill_with_empty() -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.fill_with(|| 42);
    v
}

// fill_with with push setup
// VERIFIED
#[ensures("result.len() == 3")]
fn slice_fill_with_after_push() -> Vec<i32> {
    let mut v = Vec::new();
    v.push(0);
    v.push(0);
    v.push(0);
    v.fill_with(|| 99);
    v
}

// fill_with combined with clear and resize
// VERIFIED
#[ensures("result.len() == 4")]
fn slice_fill_with_after_clear_resize() -> Vec<i32> {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.clear();
    v.resize(4, 0);
    v.fill_with(|| 100);
    v
}

// =============================================================================
// [T]::copy_within tests
// =============================================================================

// copy_within preserves length (length == 5 before and after)
// VERIFIED
#[ensures("result.len() == 5")]
fn slice_copy_within_preserves_len() -> Vec<i32> {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.push(4);
    v.push(5);
    v.copy_within(0..2, 3);
    v
}

// copy_within with resize setup
// VERIFIED
#[ensures("result.len() == 6")]
fn slice_copy_within_after_resize() -> Vec<i32> {
    let mut v = Vec::new();
    v.resize(6, 0);
    v.copy_within(1..4, 0);
    v
}

// copy_within with zero-length range preserves length
// VERIFIED
#[ensures("result.len() == 3")]
fn slice_copy_within_empty_range() -> Vec<i32> {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v.copy_within(0..0, 1);
    v
}

// copy_within combined with multiple pushes
// VERIFIED
#[ensures("result.len() == 4")]
fn slice_copy_within_multi_push() -> Vec<i32> {
    let mut v = Vec::new();
    v.push(10);
    v.push(20);
    v.push(30);
    v.push(40);
    v.copy_within(0..2, 2);
    v
}

fn main() {
    // clone_from_slice tests
    let _ = slice_clone_from_slice_preserves_len();
    let _ = slice_clone_from_slice_empty();
    let _ = slice_clone_from_slice_after_resize();
    let _ = slice_clone_from_slice_after_push();

    // fill_with tests
    let _ = slice_fill_with_preserves_len();
    let _ = slice_fill_with_empty();
    let _ = slice_fill_with_after_push();
    let _ = slice_fill_with_after_clear_resize();

    // copy_within tests
    let _ = slice_copy_within_preserves_len();
    let _ = slice_copy_within_after_resize();
    let _ = slice_copy_within_empty_range();
    let _ = slice_copy_within_multi_push();
}
