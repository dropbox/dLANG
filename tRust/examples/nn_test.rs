//! Neural Network Verification Test - Phase 7
//!
//! Tests the neural network specification feature for verifying ML models.
//!
//! NN annotations specify properties that must hold for neural networks:
//! - #[certified_robust(epsilon = 0.01, norm = "linf")] - local robustness
//! - #[monotonic(input = "0", output = "0", increasing = true)] - monotonicity
//! - #[fair(exclude = [0, 1])] - fairness (output doesn't depend on protected attributes)
//! - #[nn_bounds(lower = [-1.0], upper = [1.0])] - output bounds
//!
//! This test demonstrates:
//! 1. Certified robustness specs (perturbation bounds)
//! 2. Monotonicity specs (input-output relationships)
//! 3. Fairness specs (protected attribute independence)
//! 4. Output bounds specs (bounded outputs)
//!
//! Expected: All NN specs are parsed (CROWN verification TBD in Phase 7)
//!
//! NOTE: This test requires a stage1 rustc rebuild to recognize the NN attributes.
//! Run: cd upstream/rustc && ./x build --stage 1

// ============================================
// Certified Robustness Specs
// ============================================

/// A simple classifier that should be robust to small perturbations
/// The spec says outputs don't change under L-infinity perturbations of epsilon=0.01
#[certified_robust("epsilon = 0.01, norm = linf")]
fn robust_classifier(features: &[f32]) -> i32 {
    // Simple thresholding classifier
    let sum: f32 = features.iter().sum();
    if sum > 0.0 { 1 } else { 0 }
}

/// A regressor robust under L2 perturbations
#[certified_robust("epsilon = 0.1, norm = l2")]
fn robust_regressor(x: f32, y: f32) -> f32 {
    // Simple linear combination
    0.5 * x + 0.3 * y + 0.1
}

// ============================================
// Monotonicity Specs
// ============================================

/// A function that should be monotonically increasing in its first input
/// As input[0] increases, output[0] should increase
#[monotonic("input = 0, output = 0, increasing = true")]
fn monotonic_increasing(x: f32, bias: f32) -> f32 {
    // ReLU-like activation ensures monotonicity for positive inputs
    if x > 0.0 { x + bias } else { bias }
}

/// A function that should be monotonically decreasing in its input
#[monotonic("input = 0, output = 0, increasing = false")]
fn monotonic_decreasing(x: f32) -> f32 {
    // Negation creates decreasing function
    -x
}

/// A multi-input monotonic function
#[monotonic("inputs = [0, 1], outputs = [0], increasing = true")]
fn multi_input_monotonic(x: f32, y: f32) -> f32 {
    // Sum of inputs is monotonic in both
    x + y
}

// ============================================
// Fairness Specs
// ============================================

/// A decision function that should not depend on protected attributes
/// Protected attributes at indices 0 and 1 should not influence the output
#[fair("exclude = [0, 1]")]
fn fair_decision(protected_attr1: f32, protected_attr2: f32, feature: f32) -> i32 {
    // Only use the non-protected feature for decision
    if feature > 0.5 { 1 } else { 0 }
}

/// A scoring function that excludes demographic attributes
#[fair("exclude = [0]")]
fn fair_score(demographic: f32, skill_level: f32, experience: f32) -> f32 {
    // Score based only on skill and experience, not demographics
    skill_level * 0.4 + experience * 0.6
}

// ============================================
// Output Bounds Specs
// ============================================

/// A function with bounded output in [-1, 1]
#[nn_bounds("lower = [-1.0], upper = [1.0]")]
fn bounded_activation(x: f32) -> f32 {
    // Tanh-like bounded activation
    if x > 1.0 { 1.0 }
    else if x < -1.0 { -1.0 }
    else { x }
}

/// A probability output bounded in [0, 1]
#[nn_bounds("lower = [0.0], upper = [1.0]")]
fn probability_output(x: f32) -> f32 {
    // Sigmoid-like bounded output
    1.0 / (1.0 + (-x).exp())
}

/// Multi-output bounded function
#[nn_bounds("lower = [0.0, 0.0], upper = [1.0, 1.0]")]
fn softmax_like(x: f32, y: f32) -> (f32, f32) {
    let sum = x.abs() + y.abs() + 1e-6;
    (x.abs() / sum, y.abs() / sum)
}

// ============================================
// Combined Specs
// ============================================

/// A classifier with multiple specifications
/// - Must be robust to perturbations
/// - Must be fair w.r.t. protected attribute
/// - Must have bounded output
#[certified_robust("epsilon = 0.01, norm = linf")]
#[fair("exclude = [0]")]
#[nn_bounds("lower = [0.0], upper = [1.0]")]
fn multi_spec_classifier(protected: f32, feature1: f32, feature2: f32) -> f32 {
    // Only use non-protected features, bounded sigmoid output
    let raw = feature1 * 0.5 + feature2 * 0.5;
    1.0 / (1.0 + (-raw).exp())
}

// ============================================
// Main Entry Point
// ============================================

fn main() {
    println!("=== Neural Network Verification Test ===\n");

    // Robustness tests
    println!("--- Certified Robustness ---");
    let features = [0.1_f32, 0.2, 0.3];
    let class = robust_classifier(&features);
    println!("robust_classifier({:?}) = {}", features, class);

    let pred = robust_regressor(1.0, 2.0);
    println!("robust_regressor(1.0, 2.0) = {:.3}\n", pred);

    // Monotonicity tests
    println!("--- Monotonicity ---");
    let y1 = monotonic_increasing(1.0, 0.5);
    let y2 = monotonic_increasing(2.0, 0.5);
    println!("monotonic_increasing: f(1.0) = {:.3}, f(2.0) = {:.3} (should be increasing)", y1, y2);

    let y3 = monotonic_decreasing(1.0);
    let y4 = monotonic_decreasing(2.0);
    println!("monotonic_decreasing: f(1.0) = {:.3}, f(2.0) = {:.3} (should be decreasing)", y3, y4);

    let y5 = multi_input_monotonic(1.0, 1.0);
    println!("multi_input_monotonic(1.0, 1.0) = {:.3}\n", y5);

    // Fairness tests
    println!("--- Fairness ---");
    // Same decision regardless of protected attributes
    let d1 = fair_decision(0.0, 0.0, 0.7);
    let d2 = fair_decision(1.0, 1.0, 0.7);
    println!("fair_decision: protected=(0,0) -> {}, protected=(1,1) -> {} (should be same)", d1, d2);

    let s1 = fair_score(0.0, 0.8, 5.0);
    let s2 = fair_score(1.0, 0.8, 5.0);
    println!("fair_score: demographic=0 -> {:.3}, demographic=1 -> {:.3} (should be same)\n", s1, s2);

    // Bounds tests
    println!("--- Output Bounds ---");
    let b1 = bounded_activation(0.5);
    let b2 = bounded_activation(2.0);
    let b3 = bounded_activation(-2.0);
    println!("bounded_activation: f(0.5) = {:.3}, f(2.0) = {:.3}, f(-2.0) = {:.3}", b1, b2, b3);

    let p1 = probability_output(0.0);
    let p2 = probability_output(2.0);
    println!("probability_output: f(0.0) = {:.3}, f(2.0) = {:.3}\n", p1, p2);

    // Combined spec test
    println!("--- Combined Specs ---");
    let result = multi_spec_classifier(0.0, 0.5, 0.5);
    println!("multi_spec_classifier(protected=0, 0.5, 0.5) = {:.3}", result);

    println!("\n=== Neural Network Verification Test Complete ===");
}
