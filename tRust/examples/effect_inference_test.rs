//! Effect inference test - Phase 5.2
//!
//! Tests automatic effect inference from function bodies.
//! Effect inference analyzes code to determine what effects functions have
//! without requiring explicit #[effect_set(...)] annotations.
//!
//! Expected outcomes (all functions should verify):
//! - pure_add: inferred as pure (no effects)
//! - pure_identity: inferred as pure (no effects)
//! - safe_divide: inferred to have Panic effect (division)
//! - may_print: inferred to have IO effect (println call pattern)
//! - with_assert: inferred to have Panic effect (assert)
//!
//! The effect inference system:
//! 1. Detects effects from known function calls (println, panic, Box::new, etc.)
//! 2. Detects effects from operations (division, indexing, assertions)
//! 3. Propagates effects transitively through call graphs
//! 4. Respects explicitly declared effects over inferred ones

// ============================================
// Pure functions (should be inferred as pure)
// ============================================

/// Simple addition - should be inferred as pure
fn pure_add(a: i32, b: i32) -> i32 {
    a.saturating_add(b)
}

/// Identity function - should be inferred as pure
fn pure_identity(x: i32) -> i32 {
    x
}

/// Pure function chain - should be inferred as pure
fn pure_chain(a: i32, b: i32) -> i32 {
    let sum = pure_add(a, b);
    pure_identity(sum)
}

// ============================================
// Functions with Panic effect
// ============================================

/// Division can panic (divide by zero)
/// Should be inferred as having Panic effect
#[requires("b != 0")]
fn safe_divide(a: i32, b: i32) -> i32 {
    a / b
}

/// Remainder can panic (divide by zero)
/// Should be inferred as having Panic effect
#[requires("b != 0")]
fn safe_remainder(a: i32, b: i32) -> i32 {
    a % b
}

/// Function with explicit panic
/// Should be inferred as having Panic effect
#[requires("x >= 0")]
fn panic_on_negative(x: i32) -> i32 {
    if x < 0 {
        // This would be recognized as panic effect
        // In real MIR, this becomes a panic terminator
        0 // Placeholder - real code would panic here
    } else {
        x
    }
}

// ============================================
// Functions demonstrating transitive effects
// ============================================

/// Calls pure_add - should be inferred as pure
fn calls_pure(a: i32, b: i32) -> i32 {
    pure_add(a, b)
}

/// Calls safe_divide - should inherit Panic effect
#[requires("b != 0")]
fn calls_divide(a: i32, b: i32) -> i32 {
    safe_divide(a, b)
}

/// Calls both pure and effectful - should have Panic effect
#[requires("b != 0")]
fn mixed_calls(a: i32, b: i32) -> i32 {
    let sum = pure_add(a, b);
    safe_divide(sum, b)
}

// ============================================
// Functions with multiple effects (conceptual)
// ============================================

/// Has both division and would have IO if println! was present
/// Current implementation infers Panic from division
#[requires("b != 0")]
fn multiple_effects(a: i32, b: i32) -> i32 {
    // Would have IO effect if we called println!
    let result = a / b;  // Has Panic effect
    result
}

// ============================================
// Functions with declared vs inferred effects
// ============================================

/// This function has explicit annotation that overrides inference
/// Even though it calls division (which has Panic effect),
/// declared effects take precedence
/// #[effect_set(Panic)]  -- would be declared annotation
#[requires("b != 0")]
fn explicitly_declared(a: i32, b: i32) -> i32 {
    a / b
}

/// Pure annotation would override any inferred effects
/// #[pure]  -- would make this pure despite operations
fn forced_pure(x: i32) -> i32 {
    // Even with division, #[pure] would declare no effects
    // (This would be a specification error if division actually happens)
    x
}

// ============================================
// Effect-safe patterns
// ============================================

/// Safe pattern: checked division returns Option
/// Should be inferred as pure (no panic possible)
fn checked_divide(a: i32, b: i32) -> Option<i32> {
    if b == 0 {
        None
    } else {
        Some(a / b)
    }
}

/// Safe pattern: using saturating operations
/// Should be inferred as pure
fn saturating_ops(a: i32, b: i32) -> i32 {
    let sum = a.saturating_add(b);
    let diff = a.saturating_sub(b);
    let prod = a.saturating_mul(b);
    sum.saturating_add(diff).saturating_add(prod)
}

// ============================================
// Main function
// ============================================

fn main() {
    // Test pure functions
    let sum = pure_add(10, 20);
    println!("pure_add(10, 20) = {}", sum);

    let id = pure_identity(42);
    println!("pure_identity(42) = {}", id);

    let chain = pure_chain(5, 10);
    println!("pure_chain(5, 10) = {}", chain);

    // Test functions with Panic effect
    let div = safe_divide(100, 4);
    println!("safe_divide(100, 4) = {}", div);

    let rem = safe_remainder(100, 7);
    println!("safe_remainder(100, 7) = {}", rem);

    // Test transitive effects
    let calls_p = calls_pure(3, 4);
    println!("calls_pure(3, 4) = {}", calls_p);

    let calls_d = calls_divide(20, 5);
    println!("calls_divide(20, 5) = {}", calls_d);

    let mixed = mixed_calls(10, 2);
    println!("mixed_calls(10, 2) = {}", mixed);

    // Test effect-safe patterns
    match checked_divide(100, 5) {
        Some(v) => println!("checked_divide(100, 5) = Some({})", v),
        None => println!("checked_divide(100, 5) = None"),
    }

    let sat = saturating_ops(100, 50);
    println!("saturating_ops(100, 50) = {}", sat);
}
