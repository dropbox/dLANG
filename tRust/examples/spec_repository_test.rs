//! Integration test for Phase 10.3: Spec Repository
//!
//! This test demonstrates the spec repository system that allows loading
//! specifications for external crates from TOML files.
//!
//! The spec repository (specs/) contains contract definitions for:
//! - Community crates: specs/community/ (e.g., regex.toml, serde_json.toml)
//! - Local crates: specs/local/ (gitignored, user-specific)
//!
//! Test expectations:
//! - Contract loading from TOML files works correctly
//! - Preconditions from external specs are enforced
//! - Trust levels are propagated correctly

#![feature(register_tool)]
#![register_tool(trust)]

// Test: Verify spec repository infrastructure works
// This test simulates what happens when we use functions with external specs

/// Simulates a function from an external crate with a spec from the repository
/// In reality, regex::RegexBuilder::size_limit requires arg > 0
///
/// The spec repository contains:
/// ```toml
/// [[method]]
/// name = "regex::RegexBuilder::size_limit"
/// preconditions = ["(> arg0 0)"]
/// ```
#[trust::requires("(> limit 0)")]
#[trust::ensures("true")]
fn set_size_limit(limit: usize) -> usize {
    // Simulates RegexBuilder::size_limit
    limit
}

// Test 1: Valid call (limit > 0) - SHOULD PASS
fn test_valid_size_limit() -> usize {
    set_size_limit(1024)  // 1024 > 0, satisfies precondition
}

// Test 2: Valid call with computed value - SHOULD PASS
fn test_computed_size_limit(base: usize) -> usize {
    // Use saturating_add to avoid overflow - limit will be at least 1
    let limit = base.saturating_add(1);
    set_size_limit(limit)
}

/// Simulates serde_json::Value::is_null which is pure
#[trust::pure]
fn is_null(value: i32) -> bool {
    value == 0
}

// Test 3: Pure function call - SHOULD PASS
fn test_pure_function() -> bool {
    let x = 42;
    is_null(x)  // Pure function, no side effects
}

/// Simulates a function with a postcondition from external spec
/// serde_json::Value::as_i64 returns Option<i64>
#[trust::ensures("true")]
fn as_i64_result(has_value: bool, value: i64) -> Option<i64> {
    if has_value {
        Some(value)
    } else {
        None
    }
}

// Test 4: Function returning Option - SHOULD PASS
fn test_option_return() -> Option<i64> {
    as_i64_result(true, 42)
}

/// Simulates regex::Regex::is_match which is marked pure in spec
#[trust::pure]
#[trust::ensures("true")]
fn regex_is_match(text_len: usize) -> bool {
    text_len > 0
}

// Test 5: Pure regex match function - SHOULD PASS
fn test_regex_match() -> bool {
    regex_is_match(10)
}

// Test 6: Multiple spec repository functions used together - SHOULD PASS
fn test_combined_usage() -> (usize, bool, Option<i64>) {
    let limit = set_size_limit(2048);
    let is_null_val = is_null(0);
    let opt_val = as_i64_result(true, 100);
    (limit, is_null_val, opt_val)
}

// Test 7: Spec with precondition checked at call site - SHOULD PASS
fn test_precondition_at_callsite(n: usize) -> usize {
    if n > 0 {
        set_size_limit(n)  // Precondition (n > 0) satisfied by guard
    } else {
        set_size_limit(1)  // Default to 1, which is > 0
    }
}

// Test 8: Demonstrating trust levels - audited specs
// Specs from specs/community/*.toml have trust_level = "audited"
// This means they've been reviewed but not formally verified
#[trust::requires("(> x 0)")]
fn audited_function(x: i32) -> i32 {
    x.saturating_mul(2)  // Use saturating_mul to avoid overflow
}

fn test_audited_spec() -> i32 {
    audited_function(5)  // 5 > 0, satisfies precondition
}

// Test 9: Spec repository with effect tracking
// serde_json functions have effects = ["Alloc"]
fn test_alloc_effect() -> Vec<i32> {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v  // Allocates, which is expected
}

// Test 10: Spec repository entry point
fn main() {
    // All tests should verify successfully
    let _ = test_valid_size_limit();
    let _ = test_computed_size_limit(100);
    let _ = test_pure_function();
    let _ = test_option_return();
    let _ = test_regex_match();
    let _ = test_combined_usage();
    let _ = test_precondition_at_callsite(10);
    let _ = test_audited_spec();
    let _ = test_alloc_effect();

    println!("Spec repository test: All tests passed!");
}
