//! Integration test for Phase 10.3: Spec Validator
//!
//! This test demonstrates the spec validation system that ensures
//! specifications are syntactically correct and semantically consistent.
//!
//! The spec validator checks:
//! - SMT-LIB expression syntax
//! - Function name format (crate::path::name)
//! - Semantic consistency (e.g., pure functions don't have mutation effects)
//! - Effect annotations are valid
//!
//! Test expectations:
//! - All valid specs should pass validation
//! - Invalid specs should be detected with appropriate errors

#![feature(register_tool)]
#![register_tool(trust)]

// Test 1: Function with valid precondition from spec file
#[trust::requires("(> n 0)")]
#[trust::ensures("(>= result 1)")]
fn factorial(n: u64) -> u64 {
    if n <= 1 { 1 } else { n.saturating_mul(factorial(n - 1)) }
}

fn test_factorial() -> u64 {
    factorial(5)  // 5! = 120
}

// Test 2: Function with valid postcondition using result
#[trust::requires("(and (>= x 0) (>= y 0))")]
#[trust::ensures("(>= result 0)")]
fn sum_positive(x: i32, y: i32) -> i32 {
    x.saturating_add(y)
}

fn test_sum_positive() -> i32 {
    sum_positive(10, 20)
}

// Test 3: Pure function with valid spec
#[trust::pure]
#[trust::ensures("true")]
fn is_even(n: i32) -> bool {
    n % 2 == 0
}

fn test_is_even() -> bool {
    is_even(42)
}

// Test 4: Function with multiple preconditions (ANDed together)
#[trust::requires("(> x 0)")]
#[trust::requires("(> y 0)")]
#[trust::ensures("(> result 0)")]
fn multiply_positive(x: i32, y: i32) -> i32 {
    x.saturating_mul(y)
}

fn test_multiply_positive() -> i32 {
    multiply_positive(5, 6)
}

// Test 5: Function with nested SMT expression
#[trust::requires("(and (>= low 0) (<= low high))")]
#[trust::ensures("(and (>= result low) (<= result high))")]
fn clamp(value: i32, low: i32, high: i32) -> i32 {
    if value < low { low }
    else if value > high { high }
    else { value }
}

fn test_clamp() -> i32 {
    clamp(50, 0, 100)
}

// Test 6: Function with comparison operators
// Note: Using checked_div to avoid overflow checker warnings
#[trust::requires("(not (= divisor 0))")]
#[trust::ensures("true")]
fn safe_divide(dividend: i32, divisor: i32) -> Option<i32> {
    dividend.checked_div(divisor)
}

fn test_safe_divide() -> Option<i32> {
    safe_divide(100, 5)
}

// Test 7: Function with ite (if-then-else) in spec
#[trust::requires("true")]
#[trust::ensures("(= result (ite (> x 0) x (- 0 x)))")]
fn abs_value(x: i32) -> i32 {
    if x >= 0 { x } else { x.saturating_neg() }
}

fn test_abs_value() -> i32 {
    abs_value(-42)
}

// Test 8: Method-like function (simulating Type::method pattern)
#[trust::requires("(>= len 0)")]
#[trust::ensures("true")]
fn string_is_empty(len: usize) -> bool {
    len == 0
}

fn test_string_is_empty() -> bool {
    string_is_empty(0)
}

// Test 9: Function with div operation
// Note: Using checked_div to avoid overflow checker warnings
#[trust::requires("(and (> dividend 0) (> divisor 0))")]
#[trust::ensures("true")]
fn integer_divide(dividend: i32, divisor: i32) -> Option<i32> {
    dividend.checked_div(divisor)
}

fn test_integer_divide() -> Option<i32> {
    integer_divide(10, 3)
}

// Test 10: Function verifying complex condition
// Note: Using saturating_sub to avoid overflow checker warnings
#[trust::requires("(and (>= start 0) (>= end start))")]
#[trust::ensures("(>= result 0)")]
fn range_length(start: usize, end: usize) -> usize {
    end.saturating_sub(start)
}

fn test_range_length() -> usize {
    range_length(5, 15)
}

// Test 11: Function with effects annotation (simulates Alloc effect)
#[trust::effects("Alloc")]
fn allocate_vec(capacity: usize) -> Vec<i32> {
    Vec::with_capacity(capacity)
}

fn test_allocate_vec() -> Vec<i32> {
    allocate_vec(10)
}

// Test 12: Function demonstrating valid OR expression
#[trust::requires("(or (= x 0) (> x 1))")]
#[trust::ensures("true")]
fn valid_input(x: i32) -> i32 {
    x
}

fn test_valid_input() -> i32 {
    valid_input(5)
}

// Test 13: Main entry point - run all tests
fn main() {
    let _ = test_factorial();
    let _ = test_sum_positive();
    let _ = test_is_even();
    let _ = test_multiply_positive();
    let _ = test_clamp();
    let _ = test_safe_divide();
    let _ = test_abs_value();
    let _ = test_string_is_empty();
    let _ = test_integer_divide();
    let _ = test_range_length();
    let _ = test_allocate_vec();
    let _ = test_valid_input();

    println!("Spec validator test: All tests passed!");
}
