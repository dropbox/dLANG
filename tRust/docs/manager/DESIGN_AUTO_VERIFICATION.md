# Design: Automatic Verification by Default

**Date**: 2024-12-31
**Priority**: CORE DESIGN PRINCIPLE
**Status**: APPROVED

## Principle

> Everything that CAN be verified automatically MUST be verified by default.

No annotations required. If the compiler can prove a property, it proves it.

## Automatic Verification Categories

All ON by default when `-Zverify` is enabled:

### 1. Arithmetic Safety
- Integer overflow/underflow (all ops: +, -, *, /, %)
- Division by zero
- Shift out of bounds
- Cast truncation (`u32 as u8` where value > 255)
- Negation overflow (`-i32::MIN`)

### 2. Memory Safety
- Array/slice bounds (`arr[i]` proves `i < len`)
- Null/None dereference (`.unwrap()` on None)
- Use after move (beyond borrow checker)

### 3. Control Flow Safety
- Unreachable code is actually unreachable
- Match exhaustiveness (with values, not just types)
- Loop termination (where provable)

### 4. Resource Safety
- File handles closed
- Locks released
- Allocations freed

### 5. Contract Inference
- Infer preconditions from usage
- Infer postconditions from implementation
- Propagate contracts through call graph

## Opt-Out Mechanism

Categorical opt-out via **comments** (not attributes - keeps code clean):

```rust
// Function-level opt-out
// #[trust(overflow)]
fn hot_loop(x: u32) -> u32 { x + 1 }

// Multiple categories
// #[trust(overflow, bounds)]
fn unsafe_indexing(arr: &[u8], i: usize) -> u8 { arr[i] + 1 }

// Module-level opt-out (at top of file)
// #![trust(overflow)]

// Crate-level config (Cargo.toml)
[package.metadata.trust]
skip = ["overflow", "termination"]
```

### Why Comments?

1. **No AST pollution** - Code compiles identically with/without tRust
2. **Consistent** - Same pattern as `// #[requires(...)]` specs
3. **Easy to grep** - Find all trust annotations: `grep "// #\[trust"`
4. **Reversible** - Just delete the comment to re-enable verification

### Trust Categories
```
overflow      - Integer overflow checks
bounds        - Array bounds checks
division      - Division by zero
unwrap        - Option/Result unwrap
termination   - Loop/recursion termination
cast          - Numeric cast safety
all           - All automatic checks (dangerous!)
```

## Verification Levels

```toml
# Cargo.toml or rustc flag
[package.metadata.trust]
level = "strict"  # default: prove everything possible
# level = "standard"  # skip termination proofs (can be slow)
# level = "minimal"   # only overflow + bounds
```

## Error Messages

When automatic verification fails:

```
error[E0XXX]: arithmetic overflow possible
 --> src/lib.rs:5:10
  |
5 |     a + b
  |     ^^^^^ addition may overflow
  |
  = note: counterexample: a = 200, b = 100 (for u8)
  = help: use `a.checked_add(b)` or `a.wrapping_add(b)`
  = help: or add `// #[trust(overflow)]` above the function if intentional
```

## Implementation Priority

1. **Phase 1**: Overflow, division, bounds (most common bugs)
2. **Phase 2**: Unwrap safety, cast truncation
3. **Phase 3**: Termination (optional, can be slow)
4. **Phase 4**: Resource safety, contract inference

## Why Not Make It Optional?

> "I don't even know why we'd turn that off"

The only reasons to turn it off:
- **Performance**: Verification is slow (use `level = "minimal"`)
- **Legacy code**: Massive codebase, gradual adoption
- **Intentional unsafety**: `wrapping_add` exists for a reason

But these are exceptions. The default is: **prove everything**.
