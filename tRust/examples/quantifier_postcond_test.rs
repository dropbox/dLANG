//! Quantifier Postcondition Test File
//!
//! This tests forall and exists quantifier support in POSTCONDITIONS (ensures).
//! The quantifiers are parsed in kani_bridge.rs for postcondition verification.
//!
//! Syntax: forall |var: Type| body
//!         exists |var: Type| body
//!
//! Expected outcomes:
//! all_indices_bounded: @expect: VERIFIED
//! exists_greater: @expect: VERIFIED
//! forall_implies: @expect: VERIFIED
//! forall_simple_identity: @expect: VERIFIED

// Test 1: Forall postcondition - result property holds for all values
// The postcondition states: for all i, if i < result then i < 100
#[requires("n > 0 && n <= 100")]
#[ensures("forall |i: usize| i < result ==> i < 100")]
fn all_indices_bounded(n: usize) -> usize {
    // Returns n, which is at most 100
    // So any i < result means i < 100
    n
}

// Test 2: Exists postcondition - there exists some value with a property
// The postcondition states: there exists x such that x > result
#[requires("n >= 0 && n < 1000")]
#[ensures("exists |x: i32| x > result")]
fn exists_greater(n: i32) -> i32 {
    // Returns n, and since n < 1000, there exists n+1 which is greater
    n
}

// Test 3: Forall with implication in postcondition
// The postcondition: for all i,j: if i < j and j < n then i < n
#[requires("n > 0")]
#[ensures("forall |i: usize, j: usize| i < j && j < result ==> i < result")]
fn forall_implies(n: usize) -> usize {
    // This is a tautology: if i < j < n then i < n by transitivity
    n
}

// Test 4: Simple identity with forall
// The postcondition: for all x, x == x (trivially true)
#[ensures("forall |x: i32| x == x")]
fn forall_simple_identity() -> bool {
    true
}

fn main() {
    let _ = all_indices_bounded(50);
    let _ = exists_greater(42);
    let _ = forall_implies(10);
    let _ = forall_simple_identity();
    println!("All quantifier postcondition tests passed!");
}
