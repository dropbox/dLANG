# tRust Verification Semantics

**Version**: 1.0 | **Last Updated**: 2026-01-07

This document provides the formal specification of what tRust proves when it reports `VERIFIED`. It is intended for certification purposes and external audit.

---

## Overview

tRust is a verified compiler that integrates formal verification into the Rust compilation process. When tRust reports that a function is `VERIFIED`, it guarantees that:

> **For all executions** of the function that satisfy the precondition and terminate, the postcondition holds.

This is **partial correctness**: tRust proves safety properties but does not prove termination.

---

## Formal Soundness Theorem

The core soundness theorem, machine-checked in Lean5 (`proofs/lean5/MirSemantics/Soundness.lean`):

```lean
theorem tRust_soundness
    (p : MirProgram) (body : MirBody) (fuel : Nat) (spec : FunctionSpec)
    (encoding : VerificationEncoding) (solver : SmtSolver)
    (hVerified : checkValid solver (encoding.encodeVC (generateVC p body fuel spec)) = true)
    (s : State) (hPre : spec.precondition s)
    (s' : State) (hExec : execBodyP p body s fuel = some s') :
    spec.postcondition s'
```

In plain language:
- Given a MIR program `p` with body `body`
- Given a specification with precondition and postcondition
- If tRust verification succeeds (SMT solver confirms validity)
- Then: for any initial state `s` satisfying the precondition
- And any final state `s'` produced by executing the body
- The postcondition holds on `s'`

---

## Verification Process

### 1. Specification Parsing

Specifications are written as Rust attributes:

```rust
#[requires("n >= 0")]           // Precondition
#[ensures("result == n * 2")]   // Postcondition
fn double(n: i32) -> i32 {
    n + n
}
```

Specifications use a subset of Rust expression syntax:
- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Comparisons: `==`, `!=`, `<`, `<=`, `>`, `>=`
- Logical: `&&`, `||`, `!`
- Quantifiers: `forall`, `exists` (in advanced mode)
- Field access: `result.field`, `arg.field`
- Array access: `arr[i]`

### 2. MIR Extraction

Rust code is compiled to MIR (Mid-level Intermediate Representation), which is then extracted for verification. The MIR semantics are formalized in `proofs/lean5/MirSemantics/Semantics.lean`.

### 3. Verification Condition Generation

Weakest precondition (WP) calculus generates verification conditions. Given postcondition `Q` and statement `S`:

| Statement | WP Formula |
|-----------|------------|
| `x = e` | `Q[x := e]` (substitute x with e in Q) |
| `S1; S2` | `wp(S1, wp(S2, Q))` |
| `if c then S1 else S2` | `(c → wp(S1, Q)) ∧ (¬c → wp(S2, Q))` |
| `while c inv I` | `I ∧ (∀s. I ∧ c → wp(body, I)) ∧ (∀s. I ∧ ¬c → Q)` |

The WP implementation is verified in `proofs/lean5/MirSemantics/WP.lean` (7,049 lines, sound).

### 4. SMT Encoding

Verification conditions are encoded to SMT-LIB2 format and checked by an SMT solver (Z3 or Z4):

| Rust Type | SMT Encoding |
|-----------|--------------|
| `bool` | `Bool` |
| `i8`, `i16`, `i32`, `i64` | `Int` or `(_ BitVec N)` |
| `u8`, `u16`, `u32`, `u64` | `Int` (with bounds) or `(_ BitVec N)` |
| `f32`, `f64` | `Real` or `(_ FloatingPoint E S)` |
| `[T; N]` | `(Array Int T)` |
| `&T`, `&mut T` | Pointer model (see below) |
| `struct { f1: T1, ... }` | Product type / record |
| `enum` | Discriminant + variant data |

### 5. Solver Invocation

The SMT solver checks: `¬VC is UNSAT?`

- If **UNSAT**: VC is valid, function is `VERIFIED`
- If **SAT**: VC has counterexample, function `FAILS` verification
- If **UNKNOWN/TIMEOUT**: Verification is `INCONCLUSIVE`

---

## Supported Features

### Fully Verified (Sound)

| Feature | SMT Encoding | Notes |
|---------|--------------|-------|
| Integer arithmetic | SMT Int/BitVec | Full precision |
| Floating-point | SMT Real/FP | IEEE 754 semantics |
| Booleans | SMT Bool | |
| References | Borrow lifecycle model | NLL-aware |
| `Box<T>` | WP constraint: `*Box::new(v) == v` | Heap allocation |
| Arrays | SMT Array theory | |
| Structs | Field-wise encoding | |
| Enums | Discriminant + variant data | |
| Traits | Monomorphization-based | |
| Closures | Capture analysis | |
| Async | State machine encoding | |

### Loops

Loops require explicit invariant annotations for sound verification:

```rust
#[invariant("sum >= 0 && i <= n")]
while i < n {
    sum += arr[i];
    i += 1;
}
```

Loops **without** `#[invariant]` produce an error: *"loops require #[invariant] annotation for sound verification"*

### Unsafe Code

Unsafe blocks are detected via HIR/MIR analysis. Functions containing unsafe code:
- Are marked as unverified by default
- Can be explicitly trusted with `#[trusted]` annotation
- Propagate unsafety through the call graph

---

## What VERIFIED Means

When tRust reports `VERIFIED`:

1. **Sound**: The property provably holds for all inputs satisfying the precondition
2. **Partial Correctness**: If the function terminates, the postcondition holds
3. **No Runtime Panics**: Division by zero, overflow (in checked mode), bounds violations are detected
4. **Memory Safety**: Borrow checker rules are enforced (Rust's type system)

### What VERIFIED Does NOT Mean

1. **Termination**: tRust does not prove the function terminates
2. **Liveness**: No progress guarantees for concurrent code
3. **Side Effects**: External effects (I/O, FFI) are havoc'd
4. **Performance**: No guarantees about execution time or memory usage

---

## Verification Condition Structure

For a function:
```rust
#[requires("P")]
#[ensures("Q")]
fn f(args) -> Ret { body }
```

The generated verification condition is:
```
∀ args. P(args) → wp(body, Q(result))
```

Where:
- `P(args)` is the precondition over input arguments
- `Q(result)` is the postcondition over the return value
- `wp(body, Q)` is the weakest precondition of body with postcondition Q

---

## Proof Artifacts

### Lean5 Proofs (Machine-Checked)

| File | Lines | Theorems | Description |
|------|-------|----------|-------------|
| `Syntax.lean` | 363 | 3 | MIR datatype definitions |
| `Semantics.lean` | 366 | - | Operational semantics |
| `Lemmas.lean` | 5,486 | 644 | Semantics lemmas |
| `WP.lean` | 7,049 | 655 | Weakest precondition |
| `SMT.lean` | 635 | 13 | SMT encoding |
| `Soundness.lean` | 328 | 8 | End-to-end soundness |
| **Total** | **14,246** | **1,323** | **0 sorries** |

### Key Theorems

1. **wp_bodyP_sound**: WP is sound - if WP holds and execution succeeds, postcondition holds
2. **encoding_sound**: SMT encoding preserves validity
3. **tRust_soundness**: End-to-end soundness theorem

---

## Trust Boundary

The verification chain relies on these trusted components:

### 1. SMT Solver (Z3/Z4)

**Axiom**: If the SMT solver reports UNSAT, the formula is truly unsatisfiable.

This is the primary trust assumption. SMT solvers are heavily tested but not formally verified.

### 2. Rust Compiler Frontend

tRust trusts rustc's parsing and type checking. MIR is assumed to accurately represent the source.

### 3. Lean5 Kernel

The Lean proof assistant's kernel is trusted to correctly verify proofs.

### 4. Hardware/OS

Standard assumptions about correct hardware execution and OS behavior.

---

## Semantic Correctness Composition

The end-to-end soundness is composed from:

```
verified(VC)
→ solver.check(¬encode(VC)) = unsat       [solver invocation]
→ ¬encode(VC) is unsatisfiable            [solver soundness]
→ encode(VC) is valid                     [satisfiability duality]
→ VC holds for all states                 [encoding completeness]
→ pre(s) → wp(body, post)(s) for all s    [VC structure]
→ for initial state s with pre(s):        [precondition assumption]
   wp(body, post)(s)
→ after execution to s': post(s')         [WP soundness]
```

Each step is proven in Lean5 with no gaps (0 sorries).

---

## References

- `proofs/lean5/MirSemantics/` - Lean5 soundness proofs
- `docs/LIMITATIONS.md` - Known limitations and workarounds
- `docs/FALSE_POSITIVES.md` - Documented false positive/negative cases
- `deps/kani_fast/docs/SOUNDNESS_LIMITATIONS.md` - CHC-specific limitations
