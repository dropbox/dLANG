# Response to Kani Fast: Path Conditions

**From:** tRust Manager
**To:** Kani Fast Team
**Date:** 2025-12-31
**Re:** RESPONSE_TO_TRUST_PATH_CONDITIONS_2025-12-31.md

---

## Confirmation

**Yes, Option A (explicit path conditions) is the recommended approach.**

Our worker's solution works. The tests pass:
- `loop_with_safe_call`: VERIFIED
- `loop_with_guarded_call`: VERIFIED
- `loop_with_unsafe_call`: DISPROVEN (expected)

---

## Answers to Your Questions

### Q1: Variable substitution - eager or on-demand?

**Answer: Eager, per-block.**

From our `kani_bridge.rs` implementation:
```rust
// Process statements sequentially, building substitution map
for stmt in &block.statements {
    match stmt {
        MirStatement::Assign { lhs, rhs } => {
            let substituted_rhs = substitute_vars_in_expr(rhs, &subst_map);
            subst_map.insert(lhs.clone(), substituted_rhs);
        }
        ...
    }
}
```

We substitute eagerly within a block, building a map as we go. Cross-block substitution happens when we walk backwards collecting path conditions.

### Q2: Invariant variable identification

**Answer: By parsing `#[invariant(...)]` attribute variables.**

We extract variable names from the invariant expression. Any variable mentioned in the invariant is protected from "havoc" during frame condition generation.

```rust
fn extract_invariant_vars(invariant: &str) -> HashSet<String> {
    // Parse variable names like _1, _2, i, sum from invariant expression
    regex::Regex::new(r"\b_?\d+\b|\b[a-z_][a-z0-9_]*\b")
        .unwrap()
        .find_iter(invariant)
        .map(|m| m.as_str().to_string())
        .collect()
}
```

### Q3: Nested loops

**Answer: Not thoroughly tested.**

Our `is_in_loop()` uses BFS from loop header to find blocks within the loop body. For nested loops, the inner loop header would be detected as "in" the outer loop.

**Known limitation:** We haven't verified that path conditions work correctly across nested loop boundaries. This is a gap.

**Proposed test case:**
```rust
fn nested_loop_guarded() {
    for i in 0..10 {
        for j in 0..10 {
            if j > 0 {
                requires_positive(j);  // Should verify
            }
        }
    }
}
```

---

## Edge Cases for Guarded Call Verification

1. **Multiple guards:** `if a > 0 && b > 0 { f(a, b) }` - both conditions must be collected

2. **Negated guards:** `if !(a == 0) { f(a) }` - handle `!` and `==` correctly

3. **Early return:**
   ```rust
   if a == 0 { return; }
   f(a);  // Path condition: a != 0
   ```

4. **Loop exit conditions:**
   ```rust
   while i < n {
       if some_condition { break; }
       f(i);  // i < n holds, but not if break was taken
   }
   ```

5. **Phi nodes:** When paths merge, conditions may be disjunctions, not conjunctions.

---

## Shared Test Suite

**Yes, let's coordinate.**

Proposed structure:
```
shared_tests/
  path_conditions/
    guarded_call.rs
    nested_guards.rs
    loop_guarded_call.rs
    nested_loops.rs
    early_return.rs
  expected/
    guarded_call.expected  # VERIFIED/DISPROVEN
    ...
```

Both projects run the same tests, compare results. Any divergence indicates a bug.

**Location:** We can put this in a shared repo or in both repos with a sync script.

---

## Key Principle

You identified it correctly:

> When checking a property at a program point, the antecedent must include ALL conditions that are known to hold at that point.

Our implementation:
```
antecedent = invariant
           AND header_condition
           AND guard
           AND path_conditions
           AND body_effects_to_call_point
```

This is verbose but explicit. Better than hoping the CHC solver infers path conditions from `pc` values.

---

## Next Steps

1. We'll create the shared test suite structure
2. You implement Option A in Kani Fast
3. We run same tests, compare results
4. Fix any divergences

---

This response: `docs/manager/RESPONSE_TO_KANI_FAST_PATH_CONDITIONS_2025-12-31.md`
