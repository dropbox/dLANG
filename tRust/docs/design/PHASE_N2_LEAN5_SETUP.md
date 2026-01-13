# Phase N2: Lean5 Formal Soundness - Setup Guide

**Date**: 2026-01-05
**Prerequisites**: Phase N1 Complete
**Estimated Effort**: 50-100 AI commits

---

## Overview

Phase N2 establishes machine-checked proofs that tRust's verification is sound. The goal is to prove:

```
Theorem tRust_soundness:
  forall program P, spec S.
    tRust(P, S) = VERIFIED ->
    forall execution E of P. E |= S
```

This requires formalizing MIR semantics and VC generation in Lean5, then proving the translation is sound.

---

## Prerequisites

### 1. Install Lean5 and Elan

Elan is the Lean version manager (similar to rustup for Rust):

```bash
# Install elan
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Verify installation
source ~/.profile  # or restart shell
lean --version     # Should show Lean 4.x

# Optionally install VS Code extension
code --install-extension leanprover.lean4
```

### 2. Install Mathlib4 (for tactics)

The Lean5 proofs use Mathlib for tactics like `omega`, `simp`, `linarith`:

```bash
# Create a Lake project (if needed)
lake new tRust_soundness
cd tRust_soundness

# Add Mathlib dependency to lakefile.lean
# require mathlib from git "https://github.com/leanprover-community/mathlib4"

# Download and build
lake update
lake build
```

### 3. Verify Infrastructure

Run the existing Lean5 tests in kani_fast:

```bash
cd deps/kani_fast/crates/kani-fast-lean5
cargo test
```

The tests should pass even without Lean installed (they skip Lean-dependent tests).

---

## Existing Infrastructure

The `kani-fast-lean5` crate provides:

| Component | Location | Purpose |
|-----------|----------|---------|
| `Lean5Backend` | `backend.rs` | Lean compiler integration |
| `ProofCertificate` | `certificate.rs` | Proof artifact generation |
| `ProofObligation` | `obligation.rs` | Proof goal structure |
| `translate_invariant` | `translate.rs` | CHC to Lean5 translation |
| `generate_tactics` | `tactics.rs` | Tactic proof generation |
| `parse_smt_formula` | `smt_parser.rs` | SMT to Lean5 AST conversion |

### Key API

```rust
use kani_fast_lean5::{
    Lean5Backend, Lean5Config,
    ProofCertificate, certificate_from_chc,
    ProofObligation, translate_invariant,
};

// Check if Lean is available
if Lean5Backend::is_available() {
    let backend = Lean5Backend::new(Lean5Config::new())?;

    // Verify a certificate
    let result = backend.check_source(&lean_source)?;
    println!("Success: {}, Sorry count: {}", result.success, result.sorry_count);
}
```

---

## Phase N2 Tasks

### N2.1: Formalize MIR Semantics (20-30 commits)

Create Lean5 definitions for:

1. **MIR data structures** (`MirSemantics.lean`):
   - `Place`, `Operand`, `Rvalue`
   - `Statement`, `Terminator`, `BasicBlock`
   - `Function`, `Body`

2. **Operational semantics** (`MirExecution.lean`):
   - Small-step semantics: `step : State -> State`
   - Big-step semantics: `eval : Expr -> Value`
   - Memory model: `Heap`, `Stack`

3. **Reference**: RustBelt project formalization

### N2.2: Formalize VC Generation (15-25 commits)

Prove correctness of:

1. **Weakest precondition** (`WPSoundness.lean`):
   - `wp_correct : forall stmt pre post. wp stmt post pre -> {pre} stmt {post}`

2. **Loop invariants** (`LoopSoundness.lean`):
   - `loop_inv_sound : forall inv body. invariant_holds inv body -> loop_correct body`

3. **Function contracts** (`ContractSoundness.lean`):
   - `contract_sound : forall f pre post. f.requires pre -> f.ensures post -> call_correct f`

### N2.3: Formalize SMT Interface (10-15 commits)

Prove:

1. **Encoding soundness** (`EncodingSoundness.lean`):
   - `encode_correct : forall vc. smt_sat (encode vc) -> vc_holds vc`

2. **Theory handling** (`TheorySoundness.lean`):
   - Integer/bitvector encoding
   - Array encoding
   - Trust boundary: SMT solver assumed correct

### N2.4: End-to-End Theorem (5-10 commits)

Combine all pieces:

```lean
-- The main soundness theorem
theorem tRust_soundness :
  forall (P : Program) (S : Spec),
    tRust_verifies P S ->
    forall (E : Execution), executes P E -> satisfies E S :=
  by
    intro P S h_verify E h_exec
    have h_vc := vc_generation_sound P S
    have h_enc := encoding_sound (vc_of P S)
    have h_smt := smt_solver_correct
    -- Connect the pieces...
    sorry -- To be completed
```

---

## Getting Started

1. **Install Lean5** (see Prerequisites above)

2. **Create initial Lean project structure**:
   ```bash
   mkdir -p lean5_proofs/TRust
   cd lean5_proofs
   lake init TRust
   ```

3. **Start with MIR formalization** (N2.1):
   - Begin with simple constructs: assignments, arithmetic
   - Add control flow: branches, loops
   - Add memory: references, heap

4. **Write tests alongside proofs**:
   - Each theorem should have concrete test cases
   - Use `#check`, `#eval`, `example` for validation

---

## Success Criteria

Phase N2 is complete when:

- [ ] MIR semantics formalized in Lean5
- [ ] WP calculus proven sound
- [ ] Loop invariant handling proven sound
- [ ] SMT encoding proven equisatisfiable
- [ ] End-to-end soundness theorem with no `sorry`
- [ ] All proofs type-check in Lean 4.x

---

## Resources

- **RustBelt**: https://plv.mpi-sws.org/rustbelt/ (Rust formalization in Coq)
- **Mathlib4**: https://leanprover-community.github.io/mathlib4_docs/
- **Lean4 Manual**: https://leanprover.github.io/lean4/doc/
- **kani-fast-lean5**: `deps/kani_fast/crates/kani-fast-lean5/`

---

## Notes for AI Workers

- Each N2.x task is largely independent; can be parallelized
- Start with skeleton proofs using `sorry`, then fill in
- Test locally with `lake build` before committing
- Lean errors can be cryptic; use `#check` liberally
- Reference existing tests in `kani-fast-lean5/src/` for patterns
