# PHASE 4: Termination and Loops

**Date**: 2025-12-30
**Priority**: HIGH - Core verification features for loops and recursion
**Status**: Phase 4.1-4.5 Complete (4.6 Future)

## Overview

Phase 4 handles termination proofs for loops and recursive functions. Sound verification requires proving that programs terminate - otherwise, postconditions could vacuously hold for non-terminating code.

## Current State

The verification infrastructure from Phase 2.5 and 3 provides:
- Loop detection via CFG back-edge analysis (`find_loops()`)
- Recursive call detection (`find_recursive_calls()`)
- Loop invariant verification (base case + preservation)
- Decreases measure verification (non-negative + decreasing)

## Goals

1. Handle loops soundly with invariants
2. Handle recursion soundly with decreases measures
3. Provide escape hatches for intentionally diverging code
4. Support advanced features (mutual recursion, inference)

## Design

### 4.1 Loop Invariants (COMPLETE)

Loop invariants must:
- **Hold initially**: Before entering the loop
- **Be preserved**: After each iteration, assuming the invariant holds

```rust
// #[invariant(sum >= 0 && i >= 0)]
fn sum_to_n(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n {
        sum = sum + i;
        i = i + 1;
    }
    sum
}
```

### 4.2 Decreases Measures (COMPLETE)

Decreases measures for recursion must:
- **Be non-negative**: At function entry
- **Decrease**: At each recursive call

```rust
// #[decreases(n)]
fn factorial(n: i32) -> i32 {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}
```

### 4.3 May Diverge Escape Hatch (Phase 4.3)

For intentionally non-terminating functions (event loops, servers, REPL):

```rust
// #[may_diverge]
fn event_loop() {
    loop {
        process_events();
    }
}
```

When `#[may_diverge]` is present:
- Skip loop invariant requirement
- Skip decreases measure requirement
- Mark postconditions as "assumed" rather than "proven" (or skip verification)

## Implementation Checklist

### Phase 4.1: Loop Invariants (COMPLETE - previous commits)
- [x] Detect loops via CFG back-edge analysis
- [x] Parse `// #[invariant(...)]` annotations
- [x] Verify invariant base case (holds initially)
- [x] Verify invariant preservation (holds after iteration)
- [x] Integration test: `examples/loop_test.rs` (2/3 - one intentionally fails)

### Phase 4.2: Decreases Measures (COMPLETE - previous commits)
- [x] Detect recursive calls via call site analysis
- [x] Parse `// #[decreases(...)]` annotations
- [x] Verify measure non-negativity
- [x] Verify measure decreases at recursive call sites
- [x] Integration test: `examples/recursive_test.rs` (2/3 - one intentionally fails)

### Phase 4.3: May Diverge Escape Hatch (COMPLETE - commit #36)
- [x] Add `may_diverge: bool` field to `FunctionSpec`
- [x] Parse `// #[may_diverge]` and `#[may_diverge]` annotations
- [x] Skip loop/recursion checks when `may_diverge` is true
- [x] Create test: `examples/may_diverge_test.rs` (3/3 verified)
- [x] Unit tests for parsing (2 new tests, 54 total)

### Phase 4.4: Loop Variants (COMPLETE - commit #37)
- [x] Add `loop_variant: Option<SpecItem>` field to `FunctionSpec`
- [x] Parse `// #[variant(...)]` and `#[variant(...)]` annotations
- [x] Verify variant non-negativity (invariant => variant >= 0)
- [x] Verify variant decreases each iteration (variant' < variant)
- [x] Create test: `examples/loop_variant_test.rs` (3/4 - one intentionally fails)
- [x] Unit tests for parsing (2 new tests, 56 total)

### Phase 4.5: Mutual Recursion (COMPLETE - commit #38)
- [x] Add `mutual_recursion: Vec<String>` field to `FunctionSpec`
- [x] Parse `// #[mutual_recursion(fn1, fn2, ...)]` annotation
- [x] Extend `find_recursive_calls()` to accept target function names list
- [x] Verify decreases measure at calls to any function in mutual recursion group
- [x] Create test: `examples/mutual_recursion_test.rs` (5/7 - 2 intentionally fail)
- [x] Test even/odd classic mutual recursion pattern
- [x] Test three-way mutual recursion pattern

### Phase 4.6: Automatic Inference (Future)
- [ ] Infer simple invariants (non-negativity bounds)
- [ ] Infer decreases measures from argument patterns
- [ ] Report inferred annotations to user

## Success Criteria

```bash
$ cargo trust verify may_diverge_test.rs
=== tRust Verification ===

--- Verifying: event_loop ---
  Marked as may_diverge: skipping termination checks
  Postconditions: skipped (function may not terminate)
  Status: ASSUMED (may_diverge)

--- Verifying: factorial ---
  Decreases measure: n
  result >= 1: PROVEN
  Status: ALL PROVEN
```

## Test Results

Current state (after Phase 4.5):
- Unit tests: 56/56 pass
- Loop test: 2/3 (intentional fail for no-invariant case)
- Recursive test: 2/3 (intentional fail for no-decreases case)
- May diverge test: 3/3 (loop, recursion, event_loop all verified)
- Loop variant test: 3/4 (3 pass with variants, 1 intentional fail for variant-without-invariant)
- Mutual recursion test: 5/7 (5 pass, 2 intentionally fail for missing decreases)

## Notes

- The 1/3 "failures" in loop_test and recursive_test are intentional demonstrations of the error messages when annotations are missing
- `#[may_diverge]` is an escape hatch, not a proof - users must understand the implications
- Consider future integration with bounded model checking (Kani) for finite-bound verification of loops

### Loop Variant Design (4.4)

Loop variants complement loop invariants to prove termination:
- **Invariant**: Describes what's true throughout the loop (safety)
- **Variant**: Describes how much "work" remains (termination)

The variant expression must:
1. Be non-negative when the invariant holds: `invariant => variant >= 0`
2. Strictly decrease each iteration: `variant_after < variant_before`

Example:
```rust
// #[invariant(i >= 0 && i <= n)]  // Safety: i stays in bounds
// #[variant(n - i)]               // Termination: n - i decreases from n to 0
fn count_to_n(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i = i + 1;  // Variant: (n - i) becomes (n - (i+1)) = (n - i) - 1
    }
    i
}
```

Note: Loop variants require a loop invariant to verify properly. If a variant is specified without an invariant, the verifier will report a warning.

### Mutual Recursion Design (4.5)

Mutually recursive functions call each other, forming a cycle. For example:
- `is_even` calls `is_odd`
- `is_odd` calls `is_even`

To prove termination, we use the `#[mutual_recursion(...)]` annotation to mark all functions in the cycle:

```rust
// #[mutual_recursion(is_even, is_odd)]
// #[requires(n >= 0)]
// #[decreases(n)]
fn is_even(n: i32) -> bool {
    if n == 0 { true } else { is_odd(n - 1) }
}

// #[mutual_recursion(is_even, is_odd)]
// #[requires(n >= 0)]
// #[decreases(n)]
fn is_odd(n: i32) -> bool {
    if n == 0 { false } else { is_even(n - 1) }
}
```

The verifier:
1. Detects calls to ANY function in the mutual recursion group
2. Verifies that the decreases measure strictly decreases at each such call
3. Reports which function is being called in verification output

Example output:
```
--- Verifying: is_even ---
  measure non-negative: n >= 0: PROVEN
  measure decreases at bb3 (call to is_odd): n decreases: PROVEN
  Status: ALL PROVEN
```

Three-way (or N-way) mutual recursion is also supported:
```rust
// #[mutual_recursion(three_a, three_b, three_c)]
// #[decreases(n)]
fn three_a(n: i32) -> i32 { ... three_b(n - 1) ... }

// #[mutual_recursion(three_a, three_b, three_c)]
// #[decreases(n)]
fn three_b(n: i32) -> i32 { ... three_c(n - 1) ... }

// #[mutual_recursion(three_a, three_b, three_c)]
// #[decreases(n)]
fn three_c(n: i32) -> i32 { ... three_a(n - 1) ... }
```
