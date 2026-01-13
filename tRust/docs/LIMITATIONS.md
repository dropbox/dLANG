# tRust Verification Limitations

**Version**: 1.0 | **Last Updated**: 2026-01-07

This document catalogs known limitations, trust boundaries, and workarounds for tRust verification. It is intended for certification purposes and external audit.

---

## Trust Boundaries

### 1. SMT Solver Correctness (PRIMARY)

**Component**: Z3/Z4 SMT solver

**Assumption**: If the solver reports UNSAT, the formula is truly unsatisfiable.

**Risk**: A bug in Z3/Z4 could cause tRust to report VERIFIED for incorrect code.

**Mitigation**:
- Z3 has been used in thousands of verification projects
- Cross-validation with multiple solvers (Z3, Z4, CVC5) planned
- Proof certificate generation (see N4.1) enables independent verification

### 2. Rust Compiler Frontend

**Component**: rustc parsing, type checking, MIR generation

**Assumption**: MIR accurately represents the source code semantics.

**Risk**: A rustc bug could produce incorrect MIR.

**Mitigation**:
- rustc is heavily tested (22,169+ test cases)
- tRust passes all rustc tests
- MIR is a well-documented, stable representation

### 3. Lean5 Proof Kernel

**Component**: Lean proof assistant

**Assumption**: Lean correctly verifies proofs.

**Risk**: A Lean kernel bug could accept invalid proofs.

**Mitigation**:
- Lean is a mature proof assistant (10+ years)
- Type-theoretic foundations are well-understood
- Small trusted kernel (~10,000 LOC)

### 4. Verification Encoding

**Component**: Rust-to-SMT encoding in tRust

**Assumption**: The encoding preserves semantics.

**Risk**: Encoding bugs could make unsound translations.

**Mitigation**:
- Encoding soundness proven in Lean (`SMT.lean`)
- Extensive test suite (259 verification tests)
- Mutation testing (100% bug detection)

---

## Language Feature Limitations

### Loops

**Limitation**: Loops without `#[invariant]` annotations cannot be verified.

**Behavior**: tRust produces error: *"loops require #[invariant] annotation for sound verification"*

**Workaround**: Add explicit loop invariants:
```rust
#[invariant("sum >= 0 && i <= n")]
while i < n { ... }
```

### Recursion

**Limitation**: Recursive functions are modeled as uninterpreted functions. Recursive call results are unconstrained.

**Behavior**: Verification may succeed incorrectly or fail to prove properties.

**Workaround**: Use iterative implementations (while loops with invariants).

### Non-linear Arithmetic

**Limitation**: Multiplication of two variables (`n * m`, `n * n`) causes solver timeout.

**Reason**: Non-linear arithmetic is undecidable in general.

**Workaround**: Use constants when possible (`n * 2` works) or delegate to Kani for bounded model checking.

### Trait Method Dispatch

**Limitation**: Dynamic trait method calls (`x.trait_method()`) are uninterpreted.

**Behavior**: Return values are unconstrained.

**Workaround**: Use direct function calls or monomorphic implementations.

### Generic Functions

**Limitation**: Generic functions like `fn foo<T>()` are not inlined during verification.

**Behavior**: Return values are unconstrained.

**Workaround**: Use monomorphic (non-generic) functions for verified code.

### Closures

**Limitation**: Closure call results are unconstrained (closure bodies not inlined).

**Behavior**: Assertions about closure return values may fail.

**Workaround**: Store results before closures, verify original values.

### Static Variables

**Limitation**: Static variable reads return unconstrained values.

**Workaround**: Use `const` for values that need verification.

---

## Collection Limitations

### Vec, HashMap, etc.

**Limitation**: Standard library collections have no semantic models.

**Behavior**: Operations like `push`, `pop`, `insert` produce unconstrained results.

**Workaround**: Use arrays or fixed-size structures for verification.

### Slices

**Limitation**: Slice operations (`&arr[..]`) and `len()` return unconstrained values.

**Workaround**: Use array length directly via const generics.

---

## Reference Limitations

### Reference-Returning Functions

**Limitation**: Functions returning `&T` or `&mut T` have unconstrained dereference values.

**Workaround**: Verify original data directly.

### Reference Parameters with Enums

**Limitation**: Functions taking enum references (`fn foo(e: &MyEnum)`) may cause "unknown" results.

**Workaround**: Use by-value parameters with `Clone`/`Copy`.

### Array Reference Parameters

**Limitation**: Array index access through references returns unconstrained values.

**Workaround**: Pass elements directly or use struct fields.

---

## Structural Limitations

### Deeply Nested Structs (3+ levels)

**Limitation**: Fields nested 3+ levels deep have unconstrained values.

**Workaround**: Flatten structures or use at most 2 levels of nesting.

### Nested Enums

**Limitation**: Enums containing other enums produce unsatisfiable CHC.

**Workaround**: Flatten enum structure or use discriminant fields.

### Inter-dependent Field Assignments

**Limitation**: Temporal ordering may not be preserved for dependent assignments.

**Workaround**: Use explicit temporaries:
```rust
let old_b = p.b;
p.a = old_b;
p.b = 10;
```

---

## Pattern Matching Limitations

### Match Guards

**Limitation**: Guards like `Some(n) if n > 0` don't properly constrain extracted values.

**Workaround**: Use explicit conditions in arm body:
```rust
Some(n) => { if n > 0 { ... } }
```

### ref/ref mut Patterns

**Limitation**: `ref` and `ref mut` patterns produce unconstrained values.

**Workaround**: Use direct pattern matching without ref.

### Nested Tuple Destructuring

**Limitation**: Inner fields may be unconstrained.

**Workaround**: Destructure one level at a time.

---

## Intrinsic Limitations

### Checked Arithmetic

**Status**: Mostly fixed in kani_fast #438

**Supported**: `checked_add`, `checked_sub`, `checked_div`, `checked_rem`, `checked_shl`, `checked_shr`

**Limited**: `checked_mul` may timeout (non-linear)

### Overflowing Arithmetic

**Limitation**: `overflowing_*` operations return unconstrained tuple fields.

**Workaround**: Use `wrapping_*` or `saturating_*` operations.

### Bit Manipulation

**Status**: Supported in BitVec mode

**Supported**: `rotate_left/right`, `count_ones`, `leading_zeros`, `trailing_zeros`, `swap_bytes`, `reverse_bits`

**Requirement**: Enable BitVec mode (`--bitvec` or `KANI_FAST_BITVEC=1`)

---

## Syntactic Limitations

### Array Repeat Syntax

**Limitation**: `[val; n]` produces unconstrained elements.

**Workaround**: Use explicit literals `[5, 5, 5]`.

### Array Index Assignment

**Limitation**: `arr[i] = value` writes are not tracked.

**Workaround**: Avoid array mutation; use struct fields or rebuild arrays.

### assert_eq!/assert_ne! Macros

**Limitation**: These macros use reference patterns internally, producing unconstrained values.

**Workaround**: Use `assert!(x == y)` or `assert!(x != y)`.

---

## External Code Limitations

### FFI (Foreign Function Interface)

**Limitation**: FFI calls are havoc'd (return unconstrained values).

**Mitigation**: Use `#[trusted]` with explicit contracts for FFI wrappers.

### Inline Assembly

**Limitation**: Not supported.

**Workaround**: Wrap in `#[trusted]` functions.

### External Crates

**Limitation**: External crate implementations are not inlined.

**Mitigation**: Provide contracts for external dependencies.

---

## Verification Limitations

### Termination

**Limitation**: tRust does not prove termination.

**Implication**: VERIFIED means partial correctness only.

### Concurrency

**Limitation**: No support for concurrent verification.

**Implication**: Thread-safety properties cannot be verified.

### I/O and Side Effects

**Limitation**: External effects are not modeled.

**Implication**: File I/O, network, etc. are havoc'd.

### Timing

**Limitation**: No execution time properties.

**Implication**: Real-time constraints cannot be verified.

---

## Workaround Summary

| Limitation | Workaround |
|------------|------------|
| Loops without invariants | Add `#[invariant(...)]` |
| Recursion | Use iterative implementation |
| Non-linear arithmetic | Use constants, or Kani |
| Trait methods | Use monomorphic calls |
| Generics | Use concrete types |
| Collections (Vec, etc.) | Use arrays/fixed structures |
| Deep nesting | Flatten to 2 levels max |
| Reference returns | Verify original data |
| assert_eq!/assert_ne! | Use assert!() |
| Array repeat [v; n] | Use explicit literals |
| FFI | Use #[trusted] with contracts |

---

## Recommendations for Verified Code

1. **Keep it simple**: Avoid generics, traits, deep nesting
2. **Be explicit**: Use loop invariants, concrete types
3. **Avoid mutation**: Prefer immutable patterns
4. **Use contracts**: Specify preconditions and postconditions
5. **Test boundaries**: Verify at module boundaries
6. **Defense in depth**: Combine tRust with testing and monitoring

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2026-01-07 | Initial release for N4.2 |

---

## References

- `deps/kani_fast/docs/SOUNDNESS_LIMITATIONS.md` - Detailed CHC limitations
- `docs/VERIFICATION_SEMANTICS.md` - What tRust proves
- `docs/FALSE_POSITIVES.md` - Known false positive/negative cases
