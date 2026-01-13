//! Temporal JSON Output Test - Phase 6.2
//!
//! Tests that temporal specifications are correctly parsed and reported
//! in JSON output, including operator and arguments.
//!
//! This test verifies:
//! 1. Parsed operator names are included in JSON output
//! 2. Parsed argument expressions are included in JSON output
//! 3. Different temporal operators are correctly identified
//!
//! Expected: Compiles successfully with temporal specs reported
//! JSON output should include operator and arguments fields

#![feature(rustc_attrs)]

// Test always operator with single argument
#[temporal("always(invariant_holds)")]
fn test_always() {}

// Test eventually operator with single argument
#[temporal("eventually(done)")]
fn test_eventually() {}

// Test leads_to operator with two arguments
#[temporal("leads_to(request, response)")]
fn test_leads_to() {}

// Test shorthand [] operator
#[temporal("[]safety_property")]
fn test_box_shorthand() {}

// Test shorthand <> operator
#[temporal("<>liveness_property")]
fn test_diamond_shorthand() {}

// Test infix ~> operator
#[temporal("cause ~> effect")]
fn test_infix_leads_to() {}

// Test next operator
#[temporal("next(next_state)")]
fn test_next() {}

// Test until operator with two arguments
#[temporal("until(running, stopped)")]
fn test_until() {}

fn main() {
    test_always();
    test_eventually();
    test_leads_to();
    test_box_shorthand();
    test_diamond_shorthand();
    test_infix_leads_to();
    test_next();
    test_until();
}
