//! Neural Network CROWN Verification Test - Phase 7.3
//!
//! Tests the CROWN backend integration for verifying neural network properties.
//!
//! This test uses:
//! - #[nn_model("path")] to specify the network weights
//! - #[nn_bounds(...)] to specify output bounds that should be verified
//!
//! The test model (test_model.json) is a simple 2-layer network:
//! - Input: 2 dimensions
//! - Layer 1: Linear(2->2) + ReLU
//! - Layer 2: Linear(2->1)
//! - For inputs in [0,1]^2, output is in [0,1]
//!
//! Expected: CROWN backend verifies bounds using IBP

// ============================================
// Model with verifiable bounds
// ============================================

/// A neural network inference function with model and bounds specs.
/// The model outputs are bounded in [0, 1] for inputs in [0, 1]^2.
/// This should PROVE with IBP.
#[nn_model("examples/test_model.json")]
#[nn_bounds("lower = [0.0], upper = [1.0]")]
fn bounded_network(x: f32, y: f32) -> f32 {
    // Placeholder implementation - actual NN weights in test_model.json
    let h1 = (0.5 * x + 0.5 * y).max(0.0);
    let h2 = (0.3 * x + 0.7 * y).max(0.0);
    0.4 * h1 + 0.6 * h2
}

/// A network with tight bounds that should also prove.
/// Output is exactly [0, 1] for unit hypercube input.
#[nn_model("examples/test_model.json")]
#[nn_bounds("lower = [0.0], upper = [1.0]")]
fn tight_bounds_network(x: f32, y: f32) -> f32 {
    let h1 = (0.5 * x + 0.5 * y).max(0.0);
    let h2 = (0.3 * x + 0.7 * y).max(0.0);
    0.4 * h1 + 0.6 * h2
}

// ============================================
// Model with bounds too tight for IBP
// ============================================

/// A network with bounds that are too tight for IBP to verify.
/// The actual bounds are [0, 1] but we claim [0.3, 0.7].
/// This should return UNKNOWN with IBP.
#[nn_model("examples/test_model.json")]
#[nn_bounds("lower = [0.3], upper = [0.7]")]
fn tight_unverifiable_network(x: f32, y: f32) -> f32 {
    let h1 = (0.5 * x + 0.5 * y).max(0.0);
    let h2 = (0.3 * x + 0.7 * y).max(0.0);
    0.4 * h1 + 0.6 * h2
}

// ============================================
// Model without explicit bounds
// ============================================

/// A network with just model path, no bounds to verify.
/// Should report model is loaded but no bounds to check.
#[nn_model("examples/test_model.json")]
fn model_only_network(x: f32, y: f32) -> f32 {
    let h1 = (0.5 * x + 0.5 * y).max(0.0);
    let h2 = (0.3 * x + 0.7 * y).max(0.0);
    0.4 * h1 + 0.6 * h2
}

// ============================================
// Main Entry Point
// ============================================

fn main() {
    println!("=== Neural Network CROWN Verification Test ===\n");

    // Test bounded network
    println!("--- Bounded Network ---");
    let result = bounded_network(0.5, 0.5);
    println!("bounded_network(0.5, 0.5) = {:.4}", result);

    // Test corner cases
    let min_result = bounded_network(0.0, 0.0);
    let max_result = bounded_network(1.0, 1.0);
    println!("bounded_network(0.0, 0.0) = {:.4} (should be 0)", min_result);
    println!("bounded_network(1.0, 1.0) = {:.4} (should be <= 1)", max_result);

    // Test tight bounds
    println!("\n--- Tight Bounds Network ---");
    let tight = tight_bounds_network(0.5, 0.5);
    println!("tight_bounds_network(0.5, 0.5) = {:.4}", tight);

    // Test tight unverifiable
    println!("\n--- Tight Unverifiable Network ---");
    let tight_unverifiable = tight_unverifiable_network(0.5, 0.5);
    println!("tight_unverifiable_network(0.5, 0.5) = {:.4}", tight_unverifiable);

    // Test model only
    println!("\n--- Model Only Network ---");
    let model_only = model_only_network(0.5, 0.5);
    println!("model_only_network(0.5, 0.5) = {:.4}", model_only);

    println!("\n=== Test Complete ===");
    println!("Check trustc output for CROWN verification results.");
}
