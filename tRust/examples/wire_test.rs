//! Wire verification test file - Phase 6.5
//!
//! Tests the wiring verification feature that proves structural
//! connectivity in programs. Wire annotations ensure code paths
//! exist from entry points through all annotated states.
//!
//! Wire annotations:
//! - #[wire_start] - entry point for reachability analysis
//! - #[wire_state("name")] - named state that must be reachable
//! - #[wire_must_reach("state1, state2")] - required successors
//! - #[wire_recoverable] - error state with recovery path
//! - #[wire_terminal] - valid end point
//!
//! This test demonstrates:
//! 1. Entry point to state reachability
//! 2. must_reach constraint verification
//! 3. Recoverable error state with recovery path
//!
//! Expected: All wire constraints pass (verified connectivity)

// ============================================
// Entry Point
// ============================================

#[wire_start]
#[wire_must_reach("browse, checkout")]
fn main() {
    let logged_in = std::hint::black_box(true);
    if logged_in {
        checkout();
    } else {
        browse();
    }
}

// ============================================
// Application States
// ============================================

#[wire_state("browse")]
#[wire_terminal]
fn browse() {
    println!("Browsing products...");
    display_catalog();
}

#[wire_state("checkout")]
#[wire_must_reach("payment_success, payment_error")]
fn checkout() {
    println!("Processing checkout...");
    let payment_ok = std::hint::black_box(true);
    if payment_ok {
        payment_success();
    } else {
        payment_error();
    }
}

#[wire_state("payment_success")]
#[wire_terminal]
fn payment_success() {
    println!("Payment successful!");
}

#[wire_state("payment_error")]
#[wire_recoverable]
fn payment_error() {
    println!("Payment failed, retrying...");
    // Recovery path: retry checkout
    checkout();
}

// ============================================
// Helper Functions (no wire annotations)
// ============================================

fn display_catalog() {
    println!("Product catalog:");
    println!("- Widget $10");
    println!("- Gadget $20");
}
