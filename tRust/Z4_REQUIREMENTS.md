# Z4 Integration Requirements for tRust

**From**: tRust Verification Team
**Date**: 2026-01-01
**tRust Status**: 176 integration tests passing, Phase 10 complete

---

## Executive Summary

tRust requires a fast, Rust-native SMT solver for compile-time verification. We currently use Z3 via Rust bindings and seek to replace it with Z4 for better integration and performance.

**Primary Use Case**: Proving function contracts (preconditions/postconditions) at compile time.

---

## 1. SMT Theories Required

Based on current tRust verification needs:

| Theory | Priority | Use Case |
|--------|----------|----------|
| **QF_LIA** | Critical | Integer arithmetic for bounds, indices, lengths |
| **QF_BV** | Critical | Rust integer semantics (i8-i128, u8-u128) |
| **Core** | Critical | Boolean logic for predicates |
| **UF** | High | Function summaries, uninterpreted types |
| **Arrays** | Medium | Vec/HashMap length tracking |
| **QF_LRA** | Low | Floating-point bounds approximation |
| **FP** | Low | IEEE 754 (future) |

### Specific Requirements:

```smt2
; Example VC from tRust (clamp_positive function):
; requires(n > 0)
; ensures(result >= 1 && result <= n)

(declare-fun n () Int)
(declare-fun val () Int)
(declare-fun result () Int)

; Function semantics
(assert (= result
  (ite (< val 1) 1
    (ite (> val n) n val))))

; Check postcondition under precondition
(assert (> n 0))
(assert (not (and (>= result 1) (<= result n))))
(check-sat)
; Expected: unsat (postcondition holds)
```

---

## 2. Solving Mode

**Primary**: One-shot solving (default)
- Each function contract generates independent VCs
- Most VCs solve in <100ms

**Secondary**: Incremental push/pop
- For modular verification (callee contracts as assumptions)
- For loop invariant checking (k-induction style)

```rust
// Current tRust backend interface
pub trait ProofBackend: Send + Sync {
    fn check(&self, vc: &VerificationCondition, config: &VerifyConfig) -> VerifyResult;
    fn push(&mut self);  // Incremental
    fn pop(&mut self);   // Incremental
    fn assume(&mut self, pred: &Predicate);  // Assumption-based
}
```

**Batch Mode** (desirable):
- Check multiple VCs from same function together
- Share common declarations/assertions

---

## 3. Proof Format

**Required**: Model extraction for counterexamples

```rust
// When VC is invalid, we need concrete counterexample values
pub struct Counterexample {
    pub vc_id: VcId,
    pub assignments: Vec<(String, Value)>,  // e.g., [("x", Int(5)), ("n", Int(3))]
    pub trace: Option<Vec<TraceStep>>,
    pub explanation: String,
}
```

**Optional**: DRAT/LRAT certificates (for future proof auditing)

---

## 4. API Preference

**Preferred**: Rust crate dependency

```toml
# Cargo.toml
[dependencies]
z4 = { version = "0.x" }  # Direct Rust API
```

```rust
// Desired API (similar to current Z3 usage):
use z4::{Solver, Config, ast};

let solver = Solver::new();
let x = ast::Int::new_const("x");
let n = ast::Int::new_const("n");

solver.assert(&x.gt(&ast::Int::from_i64(0)));
solver.assert(&n.gt(&ast::Int::from_i64(0)));
solver.assert(&x.le(&n).not());  // Negate postcondition

match solver.check() {
    SatResult::Unsat => VerifyResult::Proven,
    SatResult::Sat => {
        let model = solver.get_model()?;
        VerifyResult::Counterexample(extract_values(model))
    }
    SatResult::Unknown => VerifyResult::Unknown { reason: solver.reason() }
}
```

**Acceptable**: SMT-LIB file interface (slower, already supported)

---

## 5. Benchmark Problems

### VC Characteristics

| Metric | Typical | Maximum |
|--------|---------|---------|
| Variables | 5-20 | 100+ |
| Assertions | 3-10 | 50+ |
| Quantifiers | 0-2 | 10 |
| Theory | QF_LIA | NIA+BV |

### Current Performance (Z3)

```
Simple contracts (x > 0 implies result >= 1):  1-5ms
Medium contracts (Vec length tracking):        10-50ms
Complex contracts (nested conditions):         50-200ms
Timeout threshold:                             30,000ms
```

### Representative VCs

We can provide ~50 sample VCs from our test suite for benchmarking:
- `examples/verify_test.rs` - Basic contracts
- `examples/modular_test.rs` - Cross-function reasoning
- `examples/vec_len_test.rs` - Collection length tracking

---

## 6. Integration Architecture

```
                    +-----------------+
                    |  rustc_verify   |
                    |  (verification  |
                    |   pass)         |
                    +-----------------+
                           |
                           v
                    +-----------------+
                    |    vc_ir        |
                    | (VC data types) |
                    +-----------------+
                           |
                           v
                    +-----------------+
                    |  ProofBackend   |
                    |  (trait)        |
                    +-----------------+
                      /          \
                     v            v
           +----------+     +-----------+
           | Z3Backend|     | Z4Backend |
           | (current)|     | (desired) |
           +----------+     +-----------+
```

### Current Z3 Backend Location

`backends/z4/src/lib.rs` (ironically named z4, implements Z3)

### Desired Z4 Integration

1. Add `z4` crate as dependency
2. Implement `ProofBackend` trait for Z4
3. Register in `BackendRegistry`
4. A/B test against Z3 for correctness

---

## 7. Questions for Z4 Team

1. **Integer semantics**: Does Z4 handle bitvector widths (i8, i16, i32, i64, i128)?
   - Rust integers have specific overflow semantics
   - We need wrapping, saturating, and checked arithmetic

2. **Memory footprint**: What's the typical memory usage?
   - rustc already uses 1-4GB for large crates
   - Verification should stay under 1GB additional

3. **Parallelism**: Can Z4 check multiple VCs in parallel?
   - Independent VCs from different functions
   - Would significantly speed up large crate verification

4. **Incremental mode correctness**: Is push/pop fully supported?
   - Critical for modular verification

---

## 8. Success Criteria

Z4 integration is successful when:

1. **Correctness**: All 176 tRust tests pass with Z4 backend
2. **Performance**: Average VC time <= Z3 (preferably faster)
3. **Memory**: Peak memory <= Z3
4. **API ergonomics**: Rust-native API without FFI complexity

---

## 9. Timeline

We're ready to integrate when Z4 can:
1. Handle QF_LIA + QF_BV reliably
2. Provide model extraction for counterexamples
3. Offer a Rust crate API

No specific deadline - correctness over speed.

---

## Contact

GitHub issues: https://github.com/dropbox/dLANG/tRust/issues
Tag: `z4-integration`

We look forward to integrating Z4 as tRust's primary SMT backend.
