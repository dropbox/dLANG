//! Negation (unary minus) bounds propagation test for tRust `-Zverify`.
//!
//! Run with:
//! `upstream/rustc/build/host/stage1/bin/rustc -Zverify examples/negation_bounds_test.rs -o /tmp/negation_bounds_test`
//!
//! This test exercises unary negation verification:
//! - Constant negation and double negation (via constant folding)
//! - Zero negation identity
//! - Negation in loops with constant indices

/// Test 1: Zero negation (trivial case)
/// -0 == 0, so indexing at position 0 is safe
fn test_zero_negation() -> u8 {
    let table: [u8; 1] = [42];
    let zero = 0i32;
    let negated = -zero;  // -0 == 0
    table[negated as usize]
}

/// Test 2: Constant double negation
/// Constant folding proves -(-5) == 5
fn test_constant_double_negation() -> u8 {
    let table: [u8; 6] = [0; 6];
    let five = 5i32;
    let neg_five = -five;      // -5
    let idx = -neg_five;       // -(-5) == 5
    table[idx as usize]
}

/// Test 3: Multi-step zero negation
/// Multiple negations of zero still yield zero
fn test_multi_zero_negation() -> u8 {
    let table: [u8; 1] = [99];
    let a = 0i32;
    let b = -a;   // 0
    let c = -b;   // 0
    let d = -c;   // 0
    table[d as usize]
}

/// Test 4: Negation of small constants (individual)
/// Each constant is separately negated and double-negated
fn test_small_constant_negation() -> u8 {
    let table: [u8; 4] = [0; 4];
    let one = 1i32;
    let two = 2i32;
    let three = 3i32;

    // Each -(-x) == x (constant folding)
    let a = -(-one);    // 1
    let b = -(-two);    // 2
    let c = -(-three);  // 3

    let _ = table[a as usize];
    let _ = table[b as usize];
    table[c as usize]
}

/// Test 5: Constant negation in loop
/// Loop body uses only constant indices
fn test_loop_constant_negation() {
    let table: [u8; 8] = [0; 8];
    for _ in 0..10 {
        let val = 3i32;
        let neg = -val;       // -3
        let idx = -neg;       // 3
        let _ = table[idx as usize];
    }
}

/// Test 6: Negation chain with constants
fn test_negation_chain() -> u8 {
    let table: [u8; 8] = [0; 8];
    let x = 7i32;
    let a = -x;         // -7
    let b = -a;         // 7
    let c = -b;         // -7
    let d = -c;         // 7
    table[d as usize]
}

/// Test 7: Different constant magnitudes
/// Start with positive constants and use double negation
fn test_various_magnitudes() {
    let table: [u8; 128] = [0; 128];

    // Small constant (positive -> negative -> positive)
    let val_a = 1i32;
    let neg_a = -val_a;     // -1
    let a = -neg_a;         // 1
    let _ = table[a as usize];

    // Medium constant
    let val_b = 50i32;
    let neg_b = -val_b;     // -50
    let b = -neg_b;         // 50
    let _ = table[b as usize];

    // Boundary constant
    let val_c = 127i32;
    let neg_c = -val_c;     // -127
    let c = -neg_c;         // 127
    let _ = table[c as usize];
}

/// Test 8: Negation with zero in various forms
fn test_zero_variants() -> u8 {
    let table: [u8; 1] = [55];

    // Explicit zero
    let a = -0i32;

    // Computed zero via subtraction
    let five = 5i32;
    let b = -(five - 5);  // -(0) = 0

    // Both should be zero
    let _ = table[a as usize];
    table[b as usize]
}

fn main() {
    let _ = test_zero_negation();
    let _ = test_constant_double_negation();
    let _ = test_multi_zero_negation();
    let _ = test_small_constant_negation();
    test_loop_constant_negation();
    let _ = test_negation_chain();
    test_various_magnitudes();
    let _ = test_zero_variants();
}
