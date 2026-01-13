//! End-to-end integration test for #[tactic(...)] attribute parsing and execution
//!
//! This test verifies the Phase 8.3 proof tactics infrastructure:
//! - Tactic attribute parsing (#[tactic(induction)], #[tactic(case_split)], etc.)
//! - Tactic execution with subgoal generation
//! - Integration with the verification pipeline
//!
//! Tactics provide guidance to the verifier when automatic proof search fails.
//! They help structure proofs for complex properties like recursive functions
//! and conditional logic.

#![allow(unused)]

// ============================================================================
// Test 1: Induction tactic on recursive function
// The #[tactic(induction("n"))] guides the verifier to use induction on n
// ============================================================================

/// Sum from 0 to n using induction tactic
/// Expected: VERIFIED (tactic guides the proof structure)
#[tactic(induction("n"))]
#[requires("n >= 0")]
#[ensures("result == n * (n + 1) / 2")]
fn sum_to_n(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        n.saturating_add(sum_to_n(n.saturating_sub(1)))
    }
}

/// Factorial with induction on parameter
/// Expected: VERIFIED (uses parameter index for induction)
#[tactic(induction(param = 0))]
#[requires("n >= 0")]
#[ensures("result >= 1")]
fn factorial(n: i32) -> i32 {
    if n <= 1 {
        1
    } else {
        n.saturating_mul(factorial(n.saturating_sub(1)))
    }
}

// ============================================================================
// Test 2: Case split tactic on conditional logic
// The #[tactic(case_split(...))] guides the verifier to split on a condition
// ============================================================================

/// Absolute value with case split on expression
/// Expected: VERIFIED (splits on x >= 0)
#[tactic(case_split("x >= 0"))]
#[ensures("result >= 0")]
fn abs_value(x: i32) -> i32 {
    if x >= 0 {
        x
    } else {
        x.saturating_neg()
    }
}

/// Sign function with case split on sign
/// Expected: VERIFIED (splits on sign of x)
#[tactic(case_split_sign("x"))]
#[ensures("(x > 0 && result == 1) || (x == 0 && result == 0) || (x < 0 && result == -1)")]
fn signum(x: i32) -> i32 {
    if x > 0 {
        1
    } else if x < 0 {
        -1
    } else {
        0
    }
}

// ============================================================================
// Test 3: Case split on Option type
// The #[tactic(case_split_option(...))] splits on Some/None cases
// ============================================================================

/// Unwrap with default using case split on Option
/// Expected: VERIFIED (splits on Some/None)
#[tactic(case_split_option("opt"))]
#[ensures("result >= 0")]
fn unwrap_or_zero(opt: Option<i32>) -> i32 {
    match opt {
        Some(x) if x >= 0 => x,
        Some(_) => 0, // negative values become 0
        None => 0,
    }
}

// ============================================================================
// Test 4: Case split on Result type
// The #[tactic(case_split_result(...))] splits on Ok/Err cases
// ============================================================================

/// Safe unwrap using case split on Result
/// Expected: VERIFIED (splits on Ok/Err)
#[tactic(case_split_result("res"))]
#[ensures("result >= -1")]
fn safe_unwrap(res: Result<i32, ()>) -> i32 {
    match res {
        Ok(x) if x >= 0 => x,
        Ok(_) => 0,  // negative ok values become 0
        Err(_) => -1, // error case returns -1
    }
}

// ============================================================================
// Test 5: Custom tactic
// The #[tactic(custom("my_tactic"))] allows for user-defined tactics
// ============================================================================

/// Function using a custom tactic
/// Expected: VERIFIED (custom tactic is parsed but may not be executed)
#[tactic(custom("simplify_arithmetic"))]
#[requires("a >= 0 && b >= 0")]
#[ensures("result >= a && result >= b")]
fn max_of_two(a: i32, b: i32) -> i32 {
    if a >= b {
        a
    } else {
        b
    }
}

// ============================================================================
// Test 6: Complex induction with base case and step hints
// ============================================================================

/// Fibonacci with induction hints
/// Expected: VERIFIED (uses base case and step hints)
#[tactic(induction("n", base = "0", step = 1))]
#[requires("n >= 0")]
#[ensures("result >= 0")]
fn fib(n: i32) -> i32 {
    if n <= 0 {
        0
    } else if n == 1 {
        1
    } else {
        fib(n.saturating_sub(1)).saturating_add(fib(n.saturating_sub(2)))
    }
}

// ============================================================================
// Test 7: Simple induction on single variable
// NOTE: Tuple syntax with array literals not supported in attributes
// ============================================================================

/// GCD using simple induction on a
/// Expected: VERIFIED (induction on a)
#[tactic(induction("a"))]
#[requires("a >= 0 && b >= 0")]
#[ensures("result >= 0")]
fn gcd(a: i32, b: i32) -> i32 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

// ============================================================================
// Test 8: Verify tactic doesn't break normal verification
// Functions without tactics should still verify normally
// ============================================================================

/// Simple function without tactic
/// Expected: VERIFIED (normal verification, no tactic)
#[requires("x >= 0 && x < 2147483647")]
#[ensures("result > 0")]
fn increment(x: i32) -> i32 {
    x + 1
}

/// Function with only postcondition (no tactic)
/// Expected: VERIFIED
#[ensures("result >= 0")]
fn constant_42() -> i32 {
    42
}

fn main() {
    // Test basic functionality
    println!("sum_to_n(5) = {}", sum_to_n(5));
    println!("factorial(5) = {}", factorial(5));
    println!("abs_value(-5) = {}", abs_value(-5));
    println!("signum(-10) = {}", signum(-10));
    println!("unwrap_or_zero(Some(5)) = {}", unwrap_or_zero(Some(5)));
    println!("unwrap_or_zero(None) = {}", unwrap_or_zero(None));
    println!("safe_unwrap(Ok(10)) = {}", safe_unwrap(Ok(10)));
    println!("safe_unwrap(Err(())) = {}", safe_unwrap(Err(())));
    println!("max_of_two(3, 7) = {}", max_of_two(3, 7));
    println!("fib(10) = {}", fib(10));
    println!("gcd(48, 18) = {}", gcd(48, 18));
    println!("increment(5) = {}", increment(5));
    println!("constant_42() = {}", constant_42());
}
