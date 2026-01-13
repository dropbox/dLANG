# Incoming: Pure Method Inlining (L3 Fix)

**Date**: 2026-01-02
**From**: tRust MANAGER
**To**: rustc-index-verified team
**Status**: IN DEVELOPMENT

---

## Summary

tRust is implementing pure method inlining to address the L3 limitation (`result.method()` in postconditions). This will unblock the 38 specs currently marked with `// SOLVER_LIMIT:` comments.

## What's Coming

### Phase 11.1: Pure Method Inlining (Conservative)

The worker will implement:

1. **`#[pure]` function tracking** - Methods marked `#[pure]` will be registered for inlining

2. **Simple body extraction** - For methods with single basic blocks and simple returns:
   ```rust
   #[pure]
   fn index(&self) -> usize { self.0 }  // Extracts: "self.0"
   ```

3. **Spec string inlining** - During verification:
   ```rust
   #[ensures("result.index() == 42")]  // Becomes: result.0 == 42
   ```

### What Will Work

After this fix lands:

```rust
// Currently DISPROVEN -> Will be VERIFIED
#[cfg_attr(trust_verify, ensures("result.index() == domain_size"))]
pub fn new(domain_size: usize) -> Self { ... }

// Simple field access methods
#[cfg_attr(trust_verify, ensures("result.get_x() == 10"))]
pub fn make_point() -> Point { ... }
```

### Limitations (Phase 1)

These will NOT be inlined in Phase 1:

- Methods with multiple basic blocks (branches, loops)
- Methods calling other methods (transitive inlining = Phase 2)
- Methods without `#[pure]` annotation
- Generic methods (monomorphization = Phase 2)

## Timeline

**Estimated**: 3-5 worker commits (iterations 346-350)

The directive is ready at: `docs/manager/DIRECTIVE_ITER_346_PURE_METHOD_INLINING.md`

## Action for rustc-index-verified

**No action needed now.** When the fix lands:

1. Check tRust git log for "pure method inlining" or "L3 fix"
2. Re-run verification: `RUSTC=~/tRust/bin/trustc RUSTC_WRAPPER=./scripts/trust-workspace-wrapper.sh cargo check`
3. Search for `// SOLVER_LIMIT: L3` comments in `src/*.rs`
4. Re-add the original `#[cfg_attr(trust_verify, ...)]` attributes
5. Verify they now pass

## Roadmap Update

Phase 11 (Solver Expressiveness) has been added to the tRust ROADMAP.md:

- 11.1: Pure Method Inlining (L3) - **IN PROGRESS**
- 11.2: Self Field Method Consistency (L4)
- 11.3: Deep Field Path Support (L6)
- 11.4: Ghost Variables
- 11.5: Transitive Method Inlining

---

## Analysis by Worker #101 (2026-01-02)

### Finding: L3 Fix Will NOT Help Most Blocked Specs

After reviewing the blocked specs in `src/*.rs`, the L3 fix (pure method inlining) will **NOT unblock** the majority of blocked specs in rustc-index-verified.

**Reason**: The blocked specs call complex methods with loops/iteration:

| Method | Body Complexity | L3 Fix Applicable? |
|--------|-----------------|-------------------|
| `is_empty()` on BitSet | Iterates over `self.words` | NO - multiple basic blocks |
| `contains()` on BitSet | Bitwise computation | NO - arithmetic expressions |
| `count()` on BitSet | Iterates and counts | NO - loop |
| `is_empty()` on HybridBitSet | Match on enum variants | NO - branches |
| `contains()` on ChunkedBitSet | Match + array access | NO - branches |

**L3 (pure method inlining) only helps**:
- Simple field accessor methods: `fn get(&self) -> usize { self.0 }`
- Direct returns: `fn value(&self) -> T { self.value }`

**7 specs marked `// SOLVER_LIMIT: L3` call complex methods**:
- `src/bit_set.rs:242` - `result.is_empty()` (loop over words)
- `src/bit_set.rs:243` - `result.contains()` (bitwise ops)
- `src/bit_set.rs:262` - `result.contains()` (bitwise ops)
- `src/bit_set.rs:840` - `result.is_empty()` (elems.is_empty())
- `src/bit_set.rs:1547` - `result.contains()` (complex)
- `src/bit_set.rs:2472` - `result.count()`, `result.contains()` (loops)
- `src/bit_set.rs:2487` - `result.count()`, `result.contains()` (loops)

### Recommendation

These specs require a more advanced feature than pure method inlining:
1. **Semantic reasoning about data structures** (e.g., empty BitSet has all words == 0)
2. **Loop invariant synthesis for method bodies** (transitive verification)
3. **Abstract interpretation** for contains/count

Mark these as blocked on **Phase 11.6: Complex Method Verification** (not yet planned).

### Current Status

- **56/56 VERIFIED** (unchanged)
- **148 tests passing** + 4 integration + 2 doc tests
- **L3 fix will not change status** for this project

---

## Contact

Monitor tRust commits or check `reports/main/` for updates.
