//! Implication Operator Test
//!
//! This file demonstrates the ==> (implication) operator in specifications.
//! Implication is useful for expressing conditional properties:
//! - "If the input is positive, then the output is positive"
//! - "If A holds, then B must hold"
//!
//! Implication P ==> Q is logically equivalent to !P || Q
//!
//! Expected outcomes:
//! conditional_positive: @expect: VERIFIED
//! nested_conditional: @expect: VERIFIED
//! conjunction_implies: @expect: VERIFIED
//! disjunction_implies: @expect: VERIFIED
//! non_negative_preserved: @expect: VERIFIED
//! preserve_positive: @expect: VERIFIED
//! safe_add: @expect: VERIFIED

// Test 1: Simple conditional postcondition
// If n > 0, then result > 0
#[ensures("n > 0 ==> result > 0")]
fn conditional_positive(n: i32) -> i32 {
    if n > 0 { n } else { 0 }
}

// Test 2: Multiple implications (right-associative)
// If n > 0, then (if n < 100, then result < 100)
// Parses as: n > 0 ==> (n < 100 ==> result < 100)
#[ensures("n > 0 ==> n < 100 ==> result < 100")]
fn nested_conditional(n: i32) -> i32 {
    if n > 0 && n < 100 { n } else { 0 }
}

// Test 3: Implication with && (lower precedence than &&)
// (n > 0 && n < 100) ==> result >= 0
#[ensures("n > 0 && n < 100 ==> result >= 0")]
fn conjunction_implies(n: i32) -> i32 {
    if n > 0 && n < 100 { n } else { 0 }
}

// Test 4: Implication with || (lower precedence than ||)
// (n < 0 || n > 100) ==> result == 0
#[ensures("n < 0 || n > 100 ==> result == 0")]
fn disjunction_implies(n: i32) -> i32 {
    if n < 0 || n > 100 { 0 } else { n }
}

// Test 5: Conditional postcondition - result is non-negative when input is
// If the input is non-negative, the result is also non-negative
#[ensures("x >= 0 ==> result >= 0")]
fn non_negative_preserved(x: i32) -> i32 {
    if x >= 0 { x } else { -x }  // abs function
}

// Test 6: Conditional postcondition - positive preserved
// If the old value was positive, the result should also be positive
#[ensures("x > 0 ==> result > 0")]
fn preserve_positive(x: i32) -> i32 {
    if x > 0 { x } else { 0 }
}

// Test 7: Safe operation based on condition
// If both inputs are positive, then the result equals their sum
// Note: We constrain to bounded values to avoid overflow
#[requires("a >= 0 && a < 1000")]
#[requires("b >= 0 && b < 1000")]
#[ensures("a > 0 && b > 0 ==> result > 0")]
fn safe_add(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    println!("conditional_positive(5) = {}", conditional_positive(5));
    println!("conditional_positive(-3) = {}", conditional_positive(-3));
    println!("nested_conditional(50) = {}", nested_conditional(50));
    println!("conjunction_implies(50) = {}", conjunction_implies(50));
    println!("disjunction_implies(50) = {}", disjunction_implies(50));
    println!("non_negative_preserved(-5) = {}", non_negative_preserved(-5));
    println!("preserve_positive(5) = {}", preserve_positive(5));
    println!("safe_add(3, 4) = {}", safe_add(3, 4));
}
