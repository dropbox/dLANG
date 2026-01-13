# tRust Verification Semantics Specification

**Version**: 1.0
**Date**: 2026-01-07
**Status**: Reference document for N4.2 Documentation

## Table of Contents

1. [Overview](#1-overview)
2. [MIR Intermediate Representation](#2-mir-intermediate-representation)
3. [Operational Semantics](#3-operational-semantics)
4. [Weakest Precondition Calculus](#4-weakest-precondition-calculus)
5. [Verification Condition Generation](#5-verification-condition-generation)
6. [SMT Encoding](#6-smt-encoding)
7. [Specification Language](#7-specification-language)
8. [Verification Workflow](#8-verification-workflow)
9. [Soundness Guarantees](#9-soundness-guarantees)
10. [Completeness Properties](#10-completeness-properties)
11. [Loop Handling](#11-loop-handling)
12. [Memory Model](#12-memory-model)
13. [Type System Integration](#13-type-system-integration)
14. [Limitations and Assumptions](#14-limitations-and-assumptions)
15. [Known Cases](#15-known-cases)

---

## 1. Overview

tRust is a verification-enabled fork of rustc that checks user-provided specifications against Rust code. The verification process:

1. Parses Rust source with specification annotations
2. Compiles to MIR (Mid-level Intermediate Representation)
3. Generates verification conditions (VCs) via weakest precondition
4. Encodes VCs to SMT-LIB format
5. Checks with SMT solver (Z3 or Z4)
6. Reports VERIFIED, FAILED (with counterexample), or UNKNOWN

### Soundness Statement

If tRust reports VERIFIED for a program P against specification S:
- For all initial states satisfying the precondition
- For all executions of P that terminate
- The postcondition S holds

Formally (see `proofs/lean5/MirSemantics/Soundness.lean`):

```
tRust(P, S) = VERIFIED  →  ∀ s, s'. pre(s) ∧ exec(P, s) = s' → post(s')
```

---

## 2. MIR Intermediate Representation

tRust operates on Rust's MIR, a control-flow graph representation.

### Types (`MirTy`)

```
MirTy ::= bool
        | int IntTy                     -- i8, i16, i32, i64, isize, u8, ...
        | unit
        | ref Mutability MirTy          -- &T, &mut T
        | box_ MirTy                    -- Box<T>
        | rawPtr Mutability MirTy       -- *const T, *mut T
        | array MirTy Nat               -- [T; N]
        | tuple (List MirTy)            -- (T1, T2, ...)
        | opaque String                 -- Abstract types
```

### Values

```
Value ::= bool Bool
        | int IntTy Int
        | unit
        | fn_ String                    -- Function reference
        | ref Location                  -- Reference to heap location
        | box_ Location                 -- Owned heap location
        | rawPtr (Option Location)      -- Raw pointer (nullable)
        | array (List Value)
        | tuple (List Value)
```

### Statements (`MirStmt`)

```
MirStmt ::= Nop
          | Assign Local MirRvalue
          | SetDiscriminant Local VariantIdx
          | StorageLive Local
          | StorageDead Local
          | Intrinsic String (List Local) Local
```

### Terminators (`MirTerminator`)

```
MirTerminator ::= Return
                | Goto BasicBlock
                | SwitchInt MirOperand (List (Int, BasicBlock)) BasicBlock
                | Call String (List MirOperand) Local BasicBlock (Option BasicBlock)
                | Drop Local BasicBlock (Option BasicBlock)
                | Assert MirOperand Bool BasicBlock (Option BasicBlock)
                | Unreachable
```

### Expressions/Rvalues

```
MirRvalue ::= Use MirOperand
            | BinaryOp BinOp MirOperand MirOperand
            | UnaryOp UnOp MirOperand
            | Ref Mutability Local
            | AddressOf Mutability Local
            | Aggregate AggKind (List MirOperand)
            | Discriminant Local
            | Len Local
            | Cast CastKind MirOperand MirTy

MirOperand ::= Copy Local | Move Local | Constant Constant
```

---

## 3. Operational Semantics

The operational semantics define how MIR executes. See `proofs/lean5/MirSemantics/Semantics.lean`.

### State

```
State = {
  alive : Local → Bool           -- Storage liveness
  locals : Local → Option Value  -- Local variable bindings
  heap : Heap                    -- Heap memory
}

Heap = {
  mem : Location → Option Value  -- Memory contents
  nextLoc : Location             -- Next allocation address
}
```

### Statement Execution

```
execStmt : State → MirStmt → Option State

execStmt(s, Nop) = Some s
execStmt(s, Assign l rv) =
  match evalRvalue(s, rv) with
  | Some v => Some (s with locals[l] := v)
  | None => None
execStmt(s, StorageLive l) = Some (s with alive[l] := true)
execStmt(s, StorageDead l) = Some (s with alive[l] := false, locals[l] := none)
```

### Expression Evaluation

```
evalOperand : State → MirOperand → Option Value
evalOperand(s, Copy l) = s.locals[l]
evalOperand(s, Move l) = s.locals[l]  -- Move semantics handled by borrow checker
evalOperand(s, Constant c) = evalConstant(c)
```

### Binary Operations

All arithmetic operations are total (return `Option Value`):
- Division by zero returns `None` (causes verification failure)
- Overflow behavior depends on type (wrapping for unsigned, error for signed in debug)

---

## 4. Weakest Precondition Calculus

The WP calculus computes the weakest condition under which a program satisfies a postcondition.

### Definition

```
wp : Stmt → (State → Prop) → (State → Prop)

wp(Nop, Q)(s) = Q(s)
wp(Assign l rv, Q)(s) =
  match evalRvalue(s, rv) with
  | Some v => Q(s[l := v])
  | None => True  -- Partial correctness: failure vacuously satisfies
wp(Seq s1 s2, Q) = wp(s1, wp(s2, Q))
```

### Soundness Theorem

```
theorem wp_sound:
  wp(stmt, Q)(s) ∧ execStmt(s, stmt) = Some s' → Q(s')
```

This is proven in `proofs/lean5/MirSemantics/WP.lean:45-50`.

### Total Correctness Variant

For total correctness (requiring termination):

```
wp_total(Assign l rv, Q)(s) =
  match evalRvalue(s, rv) with
  | Some v => Q(s[l := v])
  | None => False  -- Require success
```

---

## 5. Verification Condition Generation

VCs are generated by composing WP over function bodies.

### Function Verification

For a function `f` with precondition `P` and postcondition `Q`:

```
VC(f) = ∀ args. P(args) → wp(body(f), Q)(initial_state(args))
```

### VC Structure

The generated VC has the form:
```
∀ x1, x2, ... xn.
  precondition(x1, ..., xn) →
  wp_body(f, postcondition)(x1, ..., xn)
```

Where `wp_body` recursively computes WP for the entire CFG.

---

## 6. SMT Encoding

VCs are encoded to SMT-LIB for automated solving.

### Type Encoding

| Rust Type | SMT Sort |
|-----------|----------|
| `bool` | `Bool` |
| `i32`, `i64`, etc. | `Int` or `(_ BitVec n)` |
| `&T`, `Box<T>` | `Int` (heap address) |
| `[T; N]` | `(Array Int T_sort)` |
| Tuples | Datatypes or multiple variables |

### Operation Encoding

| Rust Operation | SMT |
|----------------|-----|
| `+`, `-`, `*` | `+`, `-`, `*` |
| `/`, `%` | `div`, `mod` (with zero check) |
| `==`, `<`, etc. | `=`, `<`, etc. |
| `&&`, `\|\|` | `and`, `or` |
| Array index | `(select arr idx)` |
| Array update | `(store arr idx val)` |

### Validity Checking

VC validity is checked via negation:
```
VC valid ⟺ ¬VC unsatisfiable
```

If `¬VC` is satisfiable, the satisfying assignment is a counterexample.

---

## 7. Specification Language

tRust uses attribute macros for specifications:

### Preconditions

```rust
#[requires("x > 0")]
fn positive_arg(x: i32) { ... }
```

### Postconditions

```rust
#[ensures("result >= x")]
fn non_decreasing(x: i32) -> i32 { ... }
```

### Loop Invariants

```rust
fn sum(n: u32) -> u32 {
    let mut total = 0;
    let mut i = 0;
    #[invariant("total == i * (i - 1) / 2")]
    #[invariant("i <= n")]
    while i < n {
        total += i;
        i += 1;
    }
    total
}
```

### Quantifiers

```rust
#[ensures("forall i: usize. i < result.len() => result[i] > 0")]
fn all_positive() -> Vec<i32> { ... }
```

---

## 8. Verification Workflow

### Compilation Integration

1. **Parse phase**: Extract specifications from attributes
2. **Type check phase**: Validate specification syntax
3. **MIR lowering**: Standard rustc MIR generation
4. **VC generation**: Apply WP calculus to MIR
5. **SMT encoding**: Convert VC to SMT-LIB
6. **Solving**: Invoke Z3/Z4
7. **Reporting**: Format results with source locations

### Incremental Verification

- VCs are cached per function
- Re-verification on function body change
- Specification changes invalidate cached VCs

---

## 9. Soundness Guarantees

### What is Guaranteed

If tRust reports VERIFIED:

1. **Partial correctness**: Every terminating execution satisfies the postcondition
2. **Precondition respect**: Postcondition only guaranteed when precondition holds
3. **Specification satisfaction**: The actual code matches the specification

### What is NOT Guaranteed

1. **Termination**: Verification is partial correctness by default
2. **Concurrency**: Single-threaded semantics only
3. **Compilation correctness**: tRust trusts rustc for code generation

### Trust Boundary

The soundness proof assumes:
1. SMT solver correctness (Z3/Z4)
2. Correct rustc compilation
3. Correct specification parsing

---

## 10. Completeness Properties

### Relative Completeness

tRust is relatively complete: if a program satisfies its specification, tRust will verify it, assuming:
1. The specification is expressible in the logic
2. Sufficient loop invariants are provided
3. The SMT solver decides the VC (no timeout)

### Incompleteness Sources

1. **SMT timeouts**: Complex VCs may not be decidable in practice
2. **Missing invariants**: Loops require user-provided invariants
3. **Abstraction limits**: Some properties aren't expressible

---

## 11. Loop Handling

### Invariant Requirements

All loops MUST have `#[invariant(...)]` annotations. Without invariants:
- Verification returns UNKNOWN
- Error message indicates missing invariant

### Invariant Verification

For a loop with invariant `I`:
1. **Establishment**: Prove `I` holds on loop entry
2. **Preservation**: Prove `I ∧ condition → wp(body, I)`
3. **Postcondition**: Prove `I ∧ ¬condition → post`

### Termination

Termination is NOT verified by default. For total correctness:
- Use `#[variant(...)]` to specify a decreasing measure
- tRust checks the measure decreases on each iteration

---

## 12. Memory Model

### Heap Semantics

- `Box::new(v)`: Allocates fresh location, stores `v`, returns box
- `*box`: Reads from the box's location
- `drop(box)`: Deallocates the location

### Reference Semantics

- `&x`: Creates reference to `x`'s storage
- `&mut x`: Creates mutable reference (exclusive access)
- `*ref`: Reads/writes through reference

### Alias Analysis

tRust relies on Rust's borrow checker for alias information:
- `&mut` references are exclusive
- Multiple `&` references may exist but are read-only
- No aliasing between `&mut` and any other reference

---

## 13. Type System Integration

### Borrow Lifecycle Tracking

tRust tracks:
- `BorrowBegin(local, kind)`: Reference creation
- `BorrowEnd(local)`: Reference invalidation
- `Reborrow(new, old)`: Nested borrowing

### NLL Integration

Non-Lexical Lifetimes (NLL) information from rustc is used to:
- Determine when references are live
- Validate borrowing patterns in specifications
- Generate correct aliasing constraints

### Unsafe Code

Unsafe blocks are handled conservatively:
- `#[trusted]` annotation: Skip verification, assume specification
- Without `#[trusted]`: Havoc affected state (conservative)

---

## 14. Limitations and Assumptions

### Language Subset

**Fully supported:**
- Integer arithmetic (all sizes)
- Booleans
- References and borrowing
- `Box<T>` heap allocation
- Arrays and slices
- Structs and tuples
- Enums and pattern matching
- Functions and closures
- Traits (via monomorphization)

**Partially supported:**
- Floating point (SMT FP theory, some precision limits)
- Raw pointers (conservative, may cause unknown)
- `unsafe` blocks (require `#[trusted]`)

**Not supported:**
- Concurrency (`std::thread`, atomics)
- `async`/`await` (state machine encoding exists but limited)
- FFI (foreign functions are havoc'd)
- Dynamic allocation beyond `Box` (custom allocators)

### Assumptions

1. **SMT solver correctness**: Z3/Z4 assumed bug-free
2. **Rustc correctness**: MIR generation assumed correct
3. **Single-threaded execution**: No concurrent interference
4. **Bounded resources**: Fuel parameter limits recursion depth
5. **IEEE 754 compliance**: Float semantics per standard

### Known Precision Limits

1. **Integer overflow**: Debug mode panics, release wraps (configurable)
2. **Float precision**: SMT FP theory may differ from hardware
3. **Array bounds**: Checked at verification time, not runtime

---

## 15. Known Cases

### Known False Positives

Cases where tRust may report FAILED incorrectly:

1. **Complex arithmetic**: Non-linear integer arithmetic may timeout
2. **Large arrays**: Concrete array operations may be slow
3. **Bit manipulation**: Some bitvector patterns are hard for SMT

Mitigation: Use `#[trusted]` for verified-elsewhere functions.

### Known False Negatives

Cases where bugs may escape verification:

1. **Missing invariants**: Loops without invariants skip verification
2. **FFI**: Foreign calls are assumed to satisfy any specification
3. **Unsafe + trusted**: `#[trusted]` unsafe blocks are not checked
4. **Concurrency**: Data races are not detected

**There are NO known soundness bugs** as of this version. All false negatives arise from explicit trust (`#[trusted]`) or unsupported features (FFI, concurrency).

### Soundness Audit Trail

All verification results include:
- Source location (file, line, column)
- VC identifier
- Solver used and result
- Counterexample (if FAILED)
- Optional proof certificate (Lean5 format)

---

## References

1. Lean5 soundness proofs: `proofs/lean5/MirSemantics/`
2. WP calculus implementation: `compiler/rustc_vc/`
3. SMT encoding: `vc_ir/src/smt.rs`
4. Roadmap: `docs/design/NUCLEAR_GRADE_ROADMAP.md`
5. Audit package: `proofs/lean5/AUDIT_README.md`
