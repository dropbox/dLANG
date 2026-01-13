//! Effect-based optimization test - Phase 5.3
//!
//! Tests the effect-based optimization system that derives compiler
//! optimization hints from effect analysis.
//!
//! Optimization hints derived from effects:
//! - Memoizable: pure functions can have results cached
//! - NoUnwind: functions without Panic effect don't need unwind tables
//! - EmbeddedSafe: functions without Alloc effect can run in no_std
//! - ConstEvalCandidate: functions without IO effect may be const
//! - ThreadSafe: functions without GlobalState effect are thread-safe
//! - MemorySafe: functions without Unsafe effect are memory safe
//!
//! Expected outcomes (all functions should verify):
//! - pure_memoizable: demonstrates all optimizations for pure functions
//! - no_panic_no_unwind: demonstrates NoUnwind optimization
//! - no_alloc_embedded: demonstrates EmbeddedSafe optimization
//! - no_io_const: demonstrates ConstEvalCandidate optimization
//! - no_global_thread_safe: demonstrates ThreadSafe optimization
//! - combined_optimizations: demonstrates multiple partial optimizations

// ============================================
// Pure function: all optimizations apply
// ============================================

/// Pure function - all optimizations apply
///
/// Optimizations:
/// - Memoizable: results can be cached
/// - NoUnwind: no panic possible
/// - EmbeddedSafe: no heap allocation
/// - ConstEvalCandidate: no IO
/// - ThreadSafe: no global state mutation
/// - MemorySafe: no unsafe operations
#[pure]
fn pure_memoizable(x: i32, y: i32) -> i32 {
    x.saturating_add(y)
}

/// Another pure function using saturating arithmetic
#[pure]
fn pure_square(x: i32) -> i32 {
    x.saturating_mul(x)
}

/// Pure function composition - still fully optimizable
#[pure]
fn pure_combined(x: i32, y: i32) -> i32 {
    let sum = pure_memoizable(x, y);
    pure_square(sum)
}

// ============================================
// No-panic functions: NoUnwind applies
// ============================================

/// Function with IO effect but no panic - NoUnwind applies
///
/// Optimizations:
/// - NoUnwind: no panic possible (no unwind tables needed)
/// - EmbeddedSafe: no heap allocation
/// - ThreadSafe: no global state mutation
/// - MemorySafe: no unsafe operations
///
/// NOT applicable:
/// - Memoizable: has IO effect
/// - ConstEvalCandidate: has IO effect
#[effect_set(IO)]
fn no_panic_no_unwind(x: i32) -> i32 {
    // Conceptually does IO but cannot panic
    x.saturating_add(1)
}

// ============================================
// No-alloc functions: EmbeddedSafe applies
// ============================================

/// Function with Panic effect but no allocation - EmbeddedSafe applies
///
/// Optimizations:
/// - EmbeddedSafe: no heap allocation (safe for no_std)
/// - ConstEvalCandidate: no IO effect
/// - ThreadSafe: no global state mutation
/// - MemorySafe: no unsafe operations
///
/// NOT applicable:
/// - Memoizable: has Panic effect
/// - NoUnwind: has Panic effect
#[effect_set(Panic)]
fn no_alloc_embedded(x: i32) -> i32 {
    // May panic but doesn't allocate
    x.checked_add(1).unwrap_or(0)
}

// ============================================
// No-IO functions: ConstEvalCandidate applies
// ============================================

/// Function with Alloc effect but no IO - ConstEvalCandidate applies
///
/// Optimizations:
/// - ConstEvalCandidate: no IO effect
/// - NoUnwind: no Panic effect
/// - ThreadSafe: no global state mutation
/// - MemorySafe: no unsafe operations
///
/// NOT applicable:
/// - Memoizable: has Alloc effect
/// - EmbeddedSafe: has Alloc effect
#[effect_set(Alloc)]
fn no_io_const(x: i32) -> i32 {
    // Allocates but no IO - could be const fn candidate
    x.saturating_mul(2)
}

// ============================================
// No-GlobalState functions: ThreadSafe applies
// ============================================

/// Function with IO and Alloc but no GlobalState - ThreadSafe applies
///
/// Optimizations:
/// - ThreadSafe: no global state mutation
/// - MemorySafe: no unsafe operations
/// - NoUnwind: no Panic effect
///
/// NOT applicable:
/// - Memoizable: has effects
/// - EmbeddedSafe: has Alloc effect
/// - ConstEvalCandidate: has IO effect
#[effect_set(IO, Alloc)]
fn no_global_thread_safe(x: i32) -> i32 {
    // Has IO and Alloc but safe for concurrent use
    x.saturating_add(10)
}

// ============================================
// Combined effect scenarios
// ============================================

/// Function with Panic and Alloc - limited optimizations
///
/// Optimizations:
/// - ConstEvalCandidate: no IO effect
/// - ThreadSafe: no global state mutation
/// - MemorySafe: no unsafe operations
///
/// NOT applicable:
/// - Memoizable: has effects
/// - NoUnwind: has Panic effect
/// - EmbeddedSafe: has Alloc effect
#[effect_set(Panic, Alloc)]
fn combined_optimizations(x: i32) -> i32 {
    // Demonstrates partial optimization applicability
    x.checked_mul(3).unwrap_or(i32::MAX)
}

/// Function with all effects except Unsafe - still MemorySafe
#[effect_set(IO, Alloc, Panic, Diverge, GlobalState)]
fn memory_safe_only(x: i32) -> i32 {
    // Has many effects but still memory safe
    x.saturating_add(5)
}

/// Function with Unsafe effect - no MemorySafe optimization
#[effect_set(Unsafe)]
fn not_memory_safe(x: i32) -> i32 {
    // Has unsafe operations
    x.saturating_sub(1)
}

// ============================================
// Inference-based optimization
// ============================================

/// Function without declared effects - inferred from operations
///
/// Effect inference will analyze the function body and determine
/// what optimizations are safe. This function performs only
/// arithmetic operations, so should be inferred as pure.
fn inferred_pure(a: i32, b: i32) -> i32 {
    let sum = a.saturating_add(b);
    let product = sum.saturating_mul(2);
    product.saturating_sub(a)
}

/// Function with inferred Panic effect from division
///
/// Division can panic on divide-by-zero, so NoUnwind should NOT apply.
fn inferred_panic(a: i32, b: i32) -> i32 {
    // Division can panic - inferred Panic effect
    if b != 0 { a / b } else { 0 }
}

// ============================================
// Optimization hints for higher-order functions
// ============================================

/// Higher-order function with polymorphic effects
///
/// The effects depend on the callback parameter. If called with
/// a pure callback, this function is fully optimizable.
#[effects_of(f)]
fn apply_twice<F>(x: i32, f: F) -> i32
where F: Fn(i32) -> i32 {
    f(f(x))
}

/// Call apply_twice with a pure callback - fully optimizable
#[pure]
fn twice_pure(x: i32) -> i32 {
    // When called with pure_square, apply_twice becomes pure
    apply_twice(x, pure_square)
}

// ============================================
// Main function with optimization summary
// ============================================

fn main() {
    // Test pure functions (all optimizations)
    let v1 = pure_memoizable(10, 20);
    let v2 = pure_square(5);
    let v3 = pure_combined(3, 4);
    println!("Pure functions: {}, {}, {}", v1, v2, v3);

    // Test no-panic functions (NoUnwind optimization)
    let v4 = no_panic_no_unwind(42);
    println!("No-panic: {}", v4);

    // Test no-alloc functions (EmbeddedSafe optimization)
    let v5 = no_alloc_embedded(100);
    println!("No-alloc: {}", v5);

    // Test no-IO functions (ConstEvalCandidate optimization)
    let v6 = no_io_const(7);
    println!("No-IO: {}", v6);

    // Test no-GlobalState functions (ThreadSafe optimization)
    let v7 = no_global_thread_safe(15);
    println!("Thread-safe: {}", v7);

    // Test combined effects
    let v8 = combined_optimizations(8);
    let v9 = memory_safe_only(9);
    let v10 = not_memory_safe(50);
    println!("Combined: {}, {}, {}", v8, v9, v10);

    // Test inference
    let v11 = inferred_pure(5, 10);
    let v12 = inferred_panic(100, 5);
    println!("Inferred: {}, {}", v11, v12);

    // Test polymorphic effects
    let v13 = twice_pure(3);
    println!("Polymorphic: {}", v13);

    // Summary
    println!("\nEffect-based optimization test complete!");
    println!("Each function demonstrates different optimization hints:");
    println!("- Pure functions: all 6 optimizations");
    println!("- No-panic: NoUnwind (skip unwind tables)");
    println!("- No-alloc: EmbeddedSafe (no_std compatible)");
    println!("- No-IO: ConstEvalCandidate (const fn eligible)");
    println!("- No-GlobalState: ThreadSafe (concurrent safe)");
    println!("- No-unsafe: MemorySafe (full memory safety)");
}
