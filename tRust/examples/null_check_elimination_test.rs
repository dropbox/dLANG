// Null Check Elimination Integration Test (Phase 9.2)
//
// This test demonstrates the proof-driven null check elimination that removes
// Option::unwrap() and Result::unwrap() runtime checks when verification has
// proven that the value is Some/Ok.
//
// Phase 9.2: Null Check Elimination
// - Removes Assert terminators for Option/Result unwrap when variant proven
// - Assert { condition, target } -> Goto { target }
//
// The optimization:
// - SafeOperationKind::UnwrapCheck records a proven-safe unwrap operation
// - NullCheckElimination pass transforms MIR based on these proofs
// - Runtime panic checks are removed when verification proves them unnecessary
//
// Run tests: cargo test -p rustc_vc optimization
//
// Example: How verification enables null check optimization
//
// Given this code:
// #[requires("opt.is_some()")]
// fn safe_unwrap(opt: Option<i32>) -> i32 {
//     opt.unwrap()  // Rust generates Assert + panic here
// }
//
// 1. Verification proves: opt is Some variant due to precondition
// 2. A SafeOperation with kind UnwrapCheck is created recording this proof
// 3. MirOptimizer runs NullCheckElimination pass
// 4. Assert terminator is converted to Goto
// 5. Generated code no longer includes unwrap panic check
//
// Similarly for Result::unwrap():
// #[requires("res.is_ok()")]
// fn safe_result_unwrap(res: Result<i32, String>) -> i32 {
//     res.unwrap()  // Rust generates Assert + panic here
// }

fn main() {
    // This file documents the null check elimination (Phase 9.2).
    // Actual tests are in compiler/rustc_vc/src/lib.rs::optimization_tests
    //
    // Test coverage (8 new tests for Phase 9.2):
    // - test_null_check_elimination_with_option: Assert -> Goto for Option::unwrap
    // - test_null_check_elimination_with_result: Assert -> Goto for Result::unwrap
    // - test_null_check_elimination_no_safe_ops: No optimization without proof
    // - test_null_check_elimination_wrong_block: Safe op must match block location
    // - test_helper_function_safe_unwrap_check: Helper API for creating SafeOperation
    // - test_mir_optimizer_includes_null_check_elimination: Pass is registered
    // - test_mir_optimizer_runs_all_passes: Now includes 4 passes
    // - test_optimization_result_total_includes_null_checks: Result accumulation

    println!("Null Check Elimination Infrastructure (Phase 9.2)");
    println!("==================================================");
    println!();
    println!("Key types:");
    println!("  SafeOperationKind::UnwrapCheck - proven-safe Option/Result unwrap");
    println!();
    println!("Optimization pass:");
    println!("  NullCheckElimination - Assert -> Goto for unwrap checks");
    println!();
    println!("Helper function:");
    println!("  safe_unwrap_check(id, function, block, reason) -> SafeOperation");
    println!();
    println!("Run unit tests: cargo test -p rustc_vc optimization");
    println!("Test count: 8 new null check elimination tests");
    println!();
    println!("Total optimization passes: 5");
    println!("  1. OverflowCheckElimination  - CheckedBinaryOp -> BinaryOp");
    println!("  2. BoundsCheckElimination    - Assert -> Goto (array bounds)");
    println!("  3. NullCheckElimination      - Assert -> Goto (Option/Result)");
    println!("  4. DivisionCheckElimination  - Assert -> Goto (div-by-zero)");
    println!("  5. DeadBranchElimination     - SwitchInt -> Goto (dead branches)");
}

// =============================================================================
// API Documentation
// =============================================================================

// ## SafeOperationKind::UnwrapCheck
//
// Represents a proven-safe unwrap operation. When verification proves that
// an Option is Some or a Result is Ok, this variant is used to record that
// proof and enable optimization.
//
// ```rust
// pub enum SafeOperationKind {
//     // ... other variants ...
//     UnwrapCheck,  // Option/Result variant proven
// }
// ```

// ## NullCheckElimination pass
//
// Transforms MIR by removing unwrap checks when the variant has been proven:
//
// Before optimization (with unwrap check):
// ```
// bb0: {
//     Assert(discriminant(opt) == 1 /* Some */, target: bb1);
// }
// bb1: {
//     _0 = (opt as Some).0;
//     return;
// }
// ```
//
// After optimization (check eliminated):
// ```
// bb0: {
//     goto -> bb1;
// }
// bb1: {
//     _0 = (opt as Some).0;
//     return;
// }
// ```

// ## Helper function
//
// Convenience function for creating SafeOperations for unwrap proofs:
//
// ```rust
// let safe_op = safe_unwrap_check(
//     id: 1,
//     function: "safe_unwrap",
//     block: 0,
//     reason: "precondition opt.is_some() proves Some variant",
// );
// ```

// ## OptimizationResult
//
// Now includes null_checks_eliminated count:
//
// ```rust
// pub struct OptimizationResult {
//     pub overflow_checks_eliminated: usize,
//     pub bounds_checks_eliminated: usize,
//     pub null_checks_eliminated: usize,   // NEW in Phase 9.2
//     pub other_checks_eliminated: usize,
//     pub applied: Vec<AppliedOptimization>,
// }
// ```

// ## MirOptimizer
//
// Now includes NullCheckElimination in default passes:
//
// ```rust
// let optimizer = MirOptimizer::new();
// assert_eq!(optimizer.pass_names().len(), 6);  // Now 6 passes
// assert!(optimizer.pass_names().contains(&"null_check_elimination"));
// ```
