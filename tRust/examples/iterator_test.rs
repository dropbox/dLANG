// Test Iterator method modeling (Phase 10.1)
//
// Current builtin modeling:
// - std::iter::Iterator::count: result >= 0
// - std::iter::ExactSizeIterator::len: result >= 0
//
// Note: Iterator methods like last, nth, max, min, sum, product return None
// for their postconditions since we don't track iterator contents.
//
// VERIFIED: 12 functions

// =================================================================
// Iterator::count() tests
// =================================================================

// count() returns non-negative value
// VERIFIED
#[ensures("result >= 0")]
fn count_nonneg(v: Vec<i32>) -> usize {
    v.into_iter().count()
}

// count() of empty vec is 0
// Note: We can't verify this since we don't track Vec -> iterator element count relationship
// This test verifies the postcondition works even when Vec is constructed inline
// VERIFIED (postcondition result >= 0 is trivially satisfied)
#[ensures("result >= 0")]
fn count_from_vec_new() -> usize {
    let v: Vec<i32> = Vec::new();
    v.into_iter().count()
}

// =================================================================
// ExactSizeIterator::len() tests
// (via slice::Iter implementation)
// =================================================================

// iter().len() returns non-negative value
// VERIFIED
#[ensures("result >= 0")]
fn iter_len_nonneg(v: &Vec<i32>) -> usize {
    v.iter().len()
}

// iter_mut().len() returns non-negative value
// VERIFIED
#[ensures("result >= 0")]
fn iter_mut_len_nonneg(v: &mut Vec<i32>) -> usize {
    v.iter_mut().len()
}

// into_iter().len() returns non-negative value
// VERIFIED
#[ensures("result >= 0")]
fn into_iter_len_nonneg(v: Vec<i32>) -> usize {
    v.into_iter().len()
}

// =================================================================
// Slice iterator len tests
// =================================================================

// Slice iter len is non-negative
// VERIFIED
#[ensures("result >= 0")]
fn slice_iter_len_nonneg(s: &[i32]) -> usize {
    s.iter().len()
}

// =================================================================
// Iterator chain tests
// These verify that postconditions work through iterator chains
// =================================================================

// filter doesn't break count postcondition
// VERIFIED
#[ensures("result >= 0")]
fn filter_count_nonneg(v: Vec<i32>) -> usize {
    v.into_iter().filter(|x| *x > 0).count()
}

// map doesn't break count postcondition
// VERIFIED
#[ensures("result >= 0")]
fn map_count_nonneg(v: Vec<i32>) -> usize {
    v.into_iter().map(|x| x * 2).count()
}

// take doesn't break count postcondition
// VERIFIED
#[ensures("result >= 0")]
fn take_count_nonneg(v: Vec<i32>) -> usize {
    v.into_iter().take(5).count()
}

// skip doesn't break count postcondition
// VERIFIED
#[ensures("result >= 0")]
fn skip_count_nonneg(v: Vec<i32>) -> usize {
    v.into_iter().skip(2).count()
}

// chain count still non-negative
// NOTE: chain() generates internal loops that require invariants.
// Since we can't add invariants to library code, this function is not verified.
fn chain_count_nonneg(v1: Vec<i32>, v2: Vec<i32>) -> usize {
    v1.into_iter().chain(v2.into_iter()).count()
}

// =================================================================
// Empty iterator tests (using Vec::new())
// =================================================================

// Empty Vec iter len is 0
// Note: Can't verify == 0 since we don't track Vec length -> iter length relationship
// VERIFIED (>= 0 is satisfied)
#[ensures("result >= 0")]
fn empty_vec_iter_len() -> usize {
    let v: Vec<i32> = Vec::new();
    v.iter().len()
}

fn main() {
    // Basic function calls to verify they compile and run
    // Note: vec! macro triggers overflow warnings, so we use Vec::new()
    let v1: Vec<i32> = Vec::new();
    let v2: Vec<i32> = Vec::new();
    let arr = [1, 2, 3];

    // count tests - use empty vectors to avoid vec! macro
    let _ = count_nonneg(v1);
    let _ = count_from_vec_new();

    // ExactSizeIterator::len tests
    let v = Vec::<i32>::new();
    let _ = iter_len_nonneg(&v);
    let mut v3 = Vec::<i32>::new();
    let _ = iter_mut_len_nonneg(&mut v3);
    let _ = into_iter_len_nonneg(Vec::new());

    // Slice tests
    let _ = slice_iter_len_nonneg(&arr);

    // Chain tests - use empty vectors
    let _ = filter_count_nonneg(Vec::new());
    let _ = map_count_nonneg(Vec::new());
    let _ = take_count_nonneg(Vec::new());
    let _ = skip_count_nonneg(Vec::new());
    let _ = chain_count_nonneg(Vec::new(), v2);

    // Empty tests
    assert!(empty_vec_iter_len() == 0);
}
