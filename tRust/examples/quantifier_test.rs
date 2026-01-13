//! Quantifier Test File
//!
//! This tests forall and exists quantifier support in the SMT precondition parser.
//!
//! Syntax: forall |var: Type| body
//!         exists |var: Type| body
//!
//! The quantifiers can be used in preconditions to express properties over
//! ranges of values, which is essential for array/collection specifications.
//!
//! Expected outcomes:
//! bounded_index: @expect: VERIFIED
//! has_larger_value: @expect: VERIFIED
//! ordered_pair_bound: @expect: VERIFIED
//! has_additive_inverse: @expect: VERIFIED
//! valid_next_index: @expect: VERIFIED
//! is_sorted_precond: @expect: VERIFIED

// Test 1: Simple forall - all elements in range satisfy property
#[requires("forall |i: usize| i >= 0 && i < len ==> i < 1000")]
fn bounded_index(len: usize) -> usize {
    if len > 0 && len <= 1000 {
        len - 1
    } else {
        0
    }
}

// Test 2: Simple exists - there exists an element satisfying property
#[requires("exists |x: i32| x > n")]
fn has_larger_value(n: i32) -> bool {
    // If n is not i32::MAX, there exists a larger value
    n < i32::MAX
}

// Test 3: Forall with multiple quantified variables
// Models: for all pairs (i,j) where i < j, some property holds
#[requires("forall |i: usize, j: usize| i < j ==> i < n && j <= n")]
fn ordered_pair_bound(n: usize) -> usize {
    n
}

// Test 4: Nested quantifiers
// Models: for all x, there exists y such that x + y = 0
#[requires("forall |x: i32| exists |y: i32| x + y == 0")]
fn has_additive_inverse(_x: i32) -> bool {
    true  // Always true for integers
}

// Test 5: Forall with conjunction in body
#[requires("forall |i: usize| i >= 0 && i < len ==> i + 1 <= len")]
fn valid_next_index(len: usize) -> usize {
    if len > 0 {
        len - 1
    } else {
        0
    }
}

// Test 6: Practical use case - array bound reasoning
// "For all valid indices i, j: if i < j and j < len then i < len"
#[requires("len >= 0")]
#[requires("forall |i: usize, j: usize| i < j && j < len ==> i < len")]
fn is_sorted_precond(len: usize) -> bool {
    // The precondition ensures any pair of valid indices is well-ordered
    len <= 100
}

fn main() {
    // Test the functions
    let _ = bounded_index(10);
    let _ = has_larger_value(42);
    let _ = ordered_pair_bound(5);
    let _ = has_additive_inverse(-7);
    let _ = valid_next_index(10);
    let _ = is_sorted_precond(50);
}
