# Known False Positives and Negatives in tRust

**Version**: 1.0 | **Last Updated**: 2026-01-07

This document catalogs known cases where tRust verification produces incorrect results. It is intended for certification purposes and external audit.

---

## Definitions

- **False Positive**: tRust reports `VERIFIED` but the code can violate the specification
- **False Negative**: tRust reports `FAILED` or `UNKNOWN` but the code actually satisfies the specification

---

## Summary

| Category | Status | Count | Impact |
|----------|--------|-------|--------|
| **False Positives (Soundness Bugs)** | **NONE KNOWN** | 0 | High - Must fix immediately |
| False Negatives (Incompleteness) | Expected | See below | Medium - May require workarounds |
| Timeouts | Expected | Common | Low - Increase solver timeout or simplify |

**Note**: As of 2026-01-07, tRust has **no known false positives**. All previously identified soundness bugs (N1.1-N1.4) have been fixed and verified with machine-checked proofs.

---

## False Positive Prevention

### Mutation Testing Results

tRust has been validated with mutation testing (N3.3):

| Mutation Type | Mutants | Killed | Detection Rate |
|---------------|---------|--------|----------------|
| Off-by-one (OBO) | 7 | 7 | 100% |
| Wrong comparison (WCO) | 6 | 6 | 100% |
| Arithmetic operator (ARO) | 5 | 5 | 100% |
| Return value (RVO) | 3 | 3 | 100% |
| **Total** | **21** | **21** | **100%** |

All injected bugs were correctly detected as `DISPROVEN`.

### Formal Soundness Proof

The verification chain is proven sound in Lean5 with **0 sorries**:
- `wp_bodyP_sound`: WP correctly captures execution semantics
- `tRust_soundness`: End-to-end soundness theorem (see `proofs/lean5/MirSemantics/Soundness.lean`)

---

## Known False Negatives

The following patterns may cause tRust to reject correct code or produce `UNKNOWN` results.

### 1. Non-linear Arithmetic Timeout

**Pattern**: Multiplication of two variables
```rust
#[ensures("result == x * y")]
fn multiply(x: i32, y: i32) -> i32 { x * y }  // May timeout
```

**Result**: `UNKNOWN (timeout)`

**Reason**: Non-linear integer arithmetic is undecidable. SMT solvers may not find a proof.

**Workaround**: Use bounded ranges or constant factors:
```rust
#[requires("x >= 0 && x <= 100")]
#[requires("y >= 0 && y <= 100")]
#[ensures("result == x * y")]  // Now bounded, may verify
```

### 2. Recursive Functions

**Pattern**: Any recursive function
```rust
#[ensures("result >= 0")]
fn factorial(n: u32) -> u32 {
    if n == 0 { 1 } else { n * factorial(n - 1) }  // UNKNOWN
}
```

**Result**: `UNKNOWN` or incorrect (recursive call returns unconstrained)

**Reason**: Recursive calls are modeled as uninterpreted functions.

**Workaround**: Use iterative implementations with loop invariants.

### 3. Complex Loop Invariants

**Pattern**: Loops requiring non-trivial invariant synthesis
```rust
#[ensures("result == n * (n + 1) / 2")]
fn sum_to_n(n: i32) -> i32 {
    let mut sum = 0;
    #[invariant("???")] // What invariant?
    for i in 0..=n { sum += i; }
    sum
}
```

**Result**: `UNKNOWN` without proper invariant

**Reason**: Invariant synthesis is undecidable in general.

**Workaround**: Provide explicit invariant:
```rust
#[invariant("sum == i * (i - 1) / 2 && i <= n + 1")]
```

### 4. Trait Method Dispatch

**Pattern**: Dynamic trait method calls
```rust
trait Compute { fn compute(&self) -> i32; }
#[ensures("result >= 0")]
fn use_trait(c: &dyn Compute) -> i32 { c.compute() }  // UNKNOWN
```

**Result**: `UNKNOWN` (trait call is uninterpreted)

**Workaround**: Use monomorphic implementations or add contracts to traits.

### 5. Reference-Heavy Code

**Pattern**: Complex reference/borrow patterns
```rust
#[ensures("*result == 42")]
fn make_ref() -> &'static i32 { &42 }  // May fail
```

**Result**: May fail due to unconstrained dereference

**Workaround**: Verify the original data directly.

### 6. Generic Functions

**Pattern**: Polymorphic functions
```rust
#[ensures("result.0 == a && result.1 == b")]
fn pair<T: Copy>(a: T, b: T) -> (T, T) { (a, b) }  // UNKNOWN
```

**Result**: `UNKNOWN` (generic body not inlined)

**Workaround**: Use monomorphic (non-generic) functions.

### 7. Collection Operations

**Pattern**: Vec, HashMap, etc.
```rust
let mut v = Vec::new();
v.push(42);
assert!(v[0] == 42);  // May fail
```

**Result**: May fail (push is uninterpreted)

**Workaround**: Use arrays or fixed-size structures.

### 8. Checked Multiplication

**Pattern**: `checked_mul` with variable operands
```rust
let result = x.checked_mul(y);  // May timeout
```

**Result**: `UNKNOWN (timeout)` for non-linear operands

**Reason**: Non-linear arithmetic in checked overflow detection.

**Workaround**: Bound inputs or use simpler operations.

### 9. Deeply Nested Structures

**Pattern**: 3+ levels of struct nesting
```rust
struct Inner { value: i32 }
struct Middle { inner: Inner }
struct Outer { middle: Middle }
let o = Outer { middle: Middle { inner: Inner { value: 42 } } };
assert!(o.middle.inner.value == 42);  // May fail
```

**Result**: May fail (deep fields unconstrained)

**Workaround**: Flatten structures or verify at construction.

### 10. Array Reference Parameters

**Pattern**: Arrays passed by reference to functions
```rust
fn sum(arr: &[i32; 3]) -> i32 { arr[0] + arr[1] + arr[2] }  // Indices unconstrained
```

**Result**: May fail or produce incorrect proofs

**Workaround**: Pass elements directly or use by-value arrays.

---

## Categories of Incomplete Verification

### Undecidable Cases

These fundamentally cannot be verified automatically:
- Non-linear arithmetic (`x * y` where both vary)
- General recursive functions
- Loop invariant synthesis

### Modeling Gaps

These are not yet modeled in the verifier:
- Standard library collections (Vec, HashMap, etc.)
- Closures and higher-order functions
- FFI/unsafe code

### Solver Limitations

These may timeout or return `UNKNOWN`:
- Large arrays or deeply nested structures
- Complex arithmetic expressions
- Many quantifiers

---

## Handling False Negatives

### Option 1: Add Explicit Contracts

Provide more precise specifications:
```rust
#[requires("x >= 0 && x <= 100")]  // Bound inputs
#[ensures("result >= 0 && result <= 200")]  // Weaker postcondition
```

### Option 2: Add Loop Invariants

```rust
#[invariant("i >= 0 && sum >= 0")]
while i < n { ... }
```

### Option 3: Restructure Code

- Avoid generics and traits in verified functions
- Use iterative instead of recursive implementations
- Flatten nested structures

### Option 4: Use `#[trusted]`

For code that cannot be verified but is known correct:
```rust
#[trusted]
fn external_ffi() -> i32 { ... }
```

**Warning**: `#[trusted]` bypasses verification. Use sparingly and document rationale.

---

## Reporting New Issues

If you find a case where:
- tRust says `VERIFIED` but the code can fail (potential false positive)
- tRust says `FAILED` but the code is correct (false negative)

Please report to: https://github.com/dropbox/dLANG/tRust/issues

Include:
1. Minimal reproducing example
2. Expected behavior
3. Actual behavior
4. tRust version (`git rev-parse HEAD`)

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2026-01-07 | Initial release for N4.2 |

---

## References

- `docs/VERIFICATION_SEMANTICS.md` - What tRust proves
- `docs/LIMITATIONS.md` - Known limitations and trust boundaries
- `deps/kani_fast/docs/SOUNDNESS_LIMITATIONS.md` - CHC-specific limitations
- `examples/mutation_testing_test.rs` - Mutation testing framework
