# tRust vs CompCert vs CakeML: Verified Compiler Comparison

**Date**: 2026-01-07
**Purpose**: Compare tRust's verification approach with established verified compilers for external audit context.

## Executive Summary

| Aspect | tRust | CompCert | CakeML |
|--------|-------|----------|--------|
| **Source Language** | Rust | C subset | ML subset |
| **Target** | Verification (VCs) | Machine code | Machine code |
| **Proof System** | Lean 4 | Coq | HOL4 |
| **Proof Lines** | 14,246 | ~100,000 | ~500,000 |
| **Main Theorem** | Soundness | Preservation | Semantic Preservation |
| **Trust Boundary** | SMT solver | Assembler, linker | Assembly semantics |
| **Production Use** | Verification-only | Airbus A380, etc. | Less deployed |

## What Each Compiler Verifies

### CompCert (Xavier Leroy, INRIA, 2006-present)

**Theorem**: Semantic preservation - compiled code behaves identically to source.

```
∀ program P, behavior B.
  source_semantics(P) = B →
  target_semantics(compile(P)) = B
```

**Scope**:
- Translates C (large subset) to assembly (ARM, x86, RISC-V, PowerPC)
- Preserves observable behavior: I/O, termination, non-termination
- Does NOT verify the C program itself (only compilation correctness)

**Trust Boundary**:
- Assembler (GNU as or LLVM)
- Linker
- OS/hardware behavior
- Unverified front-end parsing

### CakeML (Magnus Myreen et al., 2014-present)

**Theorem**: End-to-end semantic preservation to machine code.

```
∀ program P.
  semantics(P) refines machine_semantics(compile(P))
```

**Scope**:
- Translates ML (Standard ML subset) to machine code
- Includes verified garbage collector
- Verified in-logic compiler (bootstrap)
- Produces actual executables, not assembly text

**Trust Boundary**:
- Hardware instruction semantics (formalized in HOL4)
- Verified assembler (machine code generation)

### tRust

**Theorem**: Verification soundness - if verification passes, specification holds.

```
∀ program P, specification S.
  tRust(P, S) = VERIFIED →
  ∀ execution E of P. E |= S
```

**Scope**:
- Verifies Rust code against user-provided specifications
- Does NOT translate code (uses rustc for compilation)
- Verifies: functional correctness, memory safety (beyond Rust's guarantees), overflow absence

**Trust Boundary**:
- SMT solver (Z3, Z4)
- rustc itself (compilation correctness)

## Verification Approach Comparison

### CompCert Approach

1. **Structure**: Simulation proofs between IR languages
2. **Technique**: Forward simulation, refinement
3. **Key insight**: Break compiler into ~15 passes, prove each preserves semantics
4. **Limitation**: C semantics are complex (undefined behavior)

```
C → Clight → Csharpminor → Cminor → CminorSel → RTL →
  LTL → Linear → Mach → Asm
```

Each arrow has a simulation proof.

### CakeML Approach

1. **Structure**: Whole-program refinement to machine semantics
2. **Technique**: Verified proof-producing translation
3. **Key insight**: Compiler IS a proof; outputs certificate
4. **Limitation**: ML only, large proof development

```
source_semantics(P) REFINES machine_semantics(asm)
```

Single end-to-end theorem, no intermediate IRs exposed.

### tRust Approach

1. **Structure**: Weakest precondition calculus over MIR
2. **Technique**: VC generation + SMT solving
3. **Key insight**: Leverage Rust's type system + MIR clarity
4. **Limitation**: Trusts SMT solver, does not verify compilation

```
P ⊢ {pre} body {post}  ⟺  SMT ⊢ encode(wp(body, post) ∧ pre)
```

## Detailed Comparison

### Verification Depth

| Aspect | CompCert | CakeML | tRust |
|--------|----------|--------|-------|
| Source semantics | Formalized | Formalized | Formalized (MIR) |
| IR semantics | All passes | N/A | MIR only |
| Target semantics | Assembly | Machine code | N/A |
| Register allocation | Verified | Verified | N/A (uses rustc) |
| Instruction selection | Verified | Verified | N/A |
| Memory management | Partial | GC verified | Relies on Rust |

### Proof Complexity

| Metric | CompCert | CakeML | tRust |
|--------|----------|--------|-------|
| Total proof LOC | ~100,000 | ~500,000 | 14,246 |
| Person-years | ~15+ | ~20+ | <1 (AI-assisted) |
| Axioms | ~10 | ~5 | 1 |
| sorry/admit | 0 | 0 | 0 |

### Language Coverage

| Feature | CompCert | CakeML | tRust |
|---------|----------|--------|-------|
| Integer arithmetic | Full C | ML ints | Rust integers |
| Floating point | IEEE 754 | N/A | IEEE 754 (SMT FP) |
| Pointers | C pointers | N/A | References, Box |
| Memory safety | Partial | GC | Rust borrow checker + VC |
| Concurrency | No | No | No (single-threaded) |
| Functions | C funcs | ML funcs | Rust fns + traits |

### Trust Boundary Comparison

**CompCert trusts**:
- ~1000 LOC of unverified Coq (extraction)
- GNU assembler
- Linker
- OS system calls
- Hardware

**CakeML trusts**:
- ~200 LOC of HOL4 infrastructure
- Hardware instruction semantics (formalized)
- OS (less than CompCert due to verified bootstrap)

**tRust trusts**:
- SMT solver (Z3/Z4)
- rustc (compilation)
- Lean 4 kernel (~5000 LOC, formally verified type theory)

## Soundness Theorem Comparison

### CompCert's Theorem

```coq
Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  forward_simulation (Clight.semantics1 p) (Asm.semantics tp).
```

**Strength**: Complete preservation of all observable behaviors.
**Weakness**: Source program may have undefined behavior.

### CakeML's Theorem

```hol
 compile_prog config prog = SOME code ⇒
   implements (machine_sem code) (source_sem prog)
```

**Strength**: End-to-end to machine code, includes GC.
**Weakness**: ML subset only, large development.

### tRust's Theorem

```lean
theorem tRust_soundness :
  checkValid solver (encoding.encodeVC (generateVC p body fuel spec)) = true →
  spec.precondition s →
  execBodyP p body s fuel = some s' →
  spec.postcondition s'
```

**Strength**: Verifies user specifications, not just preservation.
**Weakness**: Trusts SMT solver, does not verify compilation.

## Use Case Comparison

### When to Use CompCert

- Safety-critical embedded C code
- Avionics, automotive, medical devices
- Need proven-correct machine code generation
- Source code is C

### When to Use CakeML

- Need full verified stack from source to machine
- ML/functional programming acceptable
- Research or extremely high-assurance contexts
- Self-hosting verified compiler needed

### When to Use tRust

- Rust codebase requiring specification verification
- Memory safety proofs beyond Rust's type system
- Functional correctness verification
- Overflow/panic freedom proofs
- Rapid verification iteration (SMT is fast)

## Synergy: Combining Approaches

For maximum assurance, combine approaches:

1. **Write in Rust** (memory safety by construction)
2. **Verify with tRust** (functional correctness, overflow freedom)
3. **Future**: Verified Rust → LLVM-IR compiler (like CompCert for C)

tRust addresses a gap: Rust's type system guarantees memory safety, but not functional correctness. tRust adds the functional correctness layer.

## Limitations Unique to Each

### CompCert Limitations
- C subset (no longjmp, variable-length arrays, etc.)
- Does not verify source program correctness
- Unverified assembler/linker in trust base

### CakeML Limitations
- ML only (no imperative code, limited FFI)
- Large proof maintenance burden
- Less industrial deployment

### tRust Limitations
- Trusts SMT solver (mitigated by certificate generation)
- Trusts rustc compilation
- Single-threaded semantics only
- Loops require explicit invariants

## Maturity and Deployment

| System | First Release | Industry Use | Certifications |
|--------|---------------|--------------|----------------|
| CompCert | 2006 | Airbus, others | DO-178C qual |
| CakeML | 2014 | Research | None known |
| tRust | 2026 | Internal | In progress |

## Conclusion

tRust occupies a unique position in the verified compiler landscape:

1. **Not a compiler** in the traditional sense - it verifies, not compiles
2. **Higher-level assurance** - proves specifications, not just preservation
3. **Smaller proof** - leverages SMT for automation
4. **Rust-native** - benefits from Rust's existing safety guarantees

For nuclear-grade assurance, the recommended approach is defense-in-depth:
- Rust's type system (memory safety)
- tRust verification (functional correctness)
- Traditional testing (coverage)
- Runtime monitoring (fail-safe)
- Hardware interlocks (physical safety)

No single tool, including CompCert, CakeML, or tRust, is sufficient alone for life-critical systems.

## References

1. Leroy, X. (2009). "Formal verification of a realistic compiler." CACM.
2. Kumar, R., et al. (2014). "CakeML: A Verified Implementation of ML." POPL.
3. tRust soundness proofs: `proofs/lean5/MirSemantics/Soundness.lean`
4. CompCert website: https://compcert.org/
5. CakeML website: https://cakeml.org/
