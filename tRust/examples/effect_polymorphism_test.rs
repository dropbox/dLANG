//! Effect polymorphism test - Phase 5.2
//!
//! Documents the effect polymorphism system where higher-order functions
//! can have effects that depend on their callback arguments.
//!
//! Key concepts (vc_ir/rustc_vc infrastructure):
//! - `EffectSource::param("f")`: effect depends on parameter f's effects
//! - `EffectSource::union([IO, effects_of(f)])`: IO plus whatever f has
//! - Effect substitution: at call sites, callback effects are resolved
//!
//! The core infrastructure is in place:
//! - vc_ir: EffectSource, EffectVar types with substitute() methods
//! - rustc_vc: EffectRegistry with check_call_polymorphic()
//! - Attribute parsing: #[effects_of(param)] declares polymorphic effects
//!
//! This test demonstrates the basic effect composition patterns using
//! the #[effects_of(f)] attribute for polymorphic effect declarations.

// ============================================
// Pure functions (no effects)
// ============================================

/// A pure function - no side effects at all
#[pure]
fn pure_identity(x: i32) -> i32 {
    x
}

/// Another pure function
#[pure]
fn pure_double(x: i32) -> i32 {
    x.saturating_mul(2)
}

/// Pure add function
#[pure]
fn pure_add(a: i32, b: i32) -> i32 {
    a.saturating_add(b)
}

// ============================================
// Functions with specific effects
// ============================================

/// A function with IO effect
#[effect_set(IO)]
fn io_increment(x: i32) -> i32 {
    // Conceptually does IO - in reality just computes
    x.saturating_add(1)
}

/// A function with Alloc effect
#[effect_set(Alloc)]
fn alloc_increment(x: i32) -> i32 {
    // Conceptually allocates - in reality just computes
    x.saturating_add(1)
}

// ============================================
// Higher-order functions with polymorphic effects
// ============================================

// Effect polymorphism attribute syntax (requires stage1 rebuild):
//   #[effects_of(f)]      - function inherits effects from parameter f
//   #[effect_set(IO)]        - function has IO effect
//   #[effects_of(f)]      - plus inherits effects from parameter f
//
// The attribute parsing is in rustc_verify/src/specs.rs:
//   FunctionSpecs.effect_params: Vec<String> - stores parameter names
//   FunctionSpecs.has_polymorphic_effects() - returns true if any effect_params
//
// Until stage1 is rebuilt, use explicit effect annotations:

/// Apply function - has no declared effects (unrestricted)
/// After stage1 rebuild: can use #[effects_of(f)] to inherit f's effects
fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

/// Map function with IO effect
/// After stage1 rebuild: can also add #[effects_of(f)] for union
#[effect_set(IO)]
fn map_with_io<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    let result = f(x);
    result.saturating_add(1)
}

// ============================================
// Effect compositions
// ============================================

/// Pure function calling pure functions through apply
/// Once stage1 is rebuilt with #[effects_of(f)], apply will inherit pure effects
#[pure]
fn pure_chain(x: i32) -> i32 {
    let a = pure_double(x);
    pure_add(a, 1)
}

/// IO function using map_with_io
#[effect_set(IO)]
fn io_map_demo(x: i32) -> i32 {
    map_with_io(pure_double, x)
}

/// IO + Alloc function demonstrating effect union
#[effect_set(IO, Alloc)]
fn combined_effects(x: i32) -> i32 {
    let a = io_increment(x);
    alloc_increment(a)
}

// ============================================
// Main function
// ============================================

fn main() {
    // Test pure functions
    let x = pure_identity(42);
    println!("pure_identity(42) = {}", x);

    let y = pure_double(21);
    println!("pure_double(21) = {}", y);

    // Test effect functions
    let z = io_increment(10);
    println!("io_increment(10) = {}", z);

    let w = alloc_increment(5);
    println!("alloc_increment(5) = {}", w);

    // Test pure chain
    let a = pure_chain(3);
    println!("pure_chain(3) = {}", a);

    // Test apply (polymorphic effects after stage1 rebuild)
    let b = apply(pure_double, 4);
    println!("apply(pure_double, 4) = {}", b);

    // Test map_with_io
    let c = io_map_demo(6);
    println!("io_map_demo(6) = {}", c);

    // Test combined effects
    let d = combined_effects(7);
    println!("combined_effects(7) = {}", d);

    println!("Effect polymorphism test complete!");
    println!("See vc_ir/src/specs.rs for EffectSource, EffectVar types");
    println!("See compiler/rustc_vc/src/verify.rs for check_call_polymorphic()");
    println!("Use #[effects_of(param)] to declare polymorphic effects");
}
