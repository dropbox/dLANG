# Lean proofs (Phase N2)

This directory contains Lean/Lake proofs for Phase N2 (formal soundness).

## Build

```bash
cd proofs/lean5
lake build
```

## Layout

- `MirSemantics.lean`: Umbrella module
- `MirSemantics/Syntax.lean`: Core MIR datatypes (N2.1)
- `MirSemantics/Semantics.lean`: Evaluators + executable semantics (N2.1)
- `MirSemantics/Lemmas.lean`: Semantics lemmas (N2.1)
- `MirSemantics/WP.lean`: WP/WLP definitions + proofs (N2.2)
- `MirSemantics/SMT.lean`: SMT interface formalization (N2.3)
- `MirSemantics/Soundness.lean`: End-to-end soundness theorem (N2.4)

## Status

- **Sorries**: 0
- **Total lines**: 14,246
- **Theorems/lemmas**: 1,323

## Phase Progress

- [x] N2.1: MIR Semantics formalization
- [x] N2.2: WP/VC generation formalization
- [x] N2.3: SMT interface formalization
- [x] N2.4: End-to-end soundness theorem

## Trust Boundary

The soundness proof depends on:

1. **SMT solver correctness** (axiom `smt_solver_correct` in SMT.lean)
   - If solver says UNSAT, formula is truly unsatisfiable
   - If solver says SAT, formula is truly satisfiable

2. **Encoding soundness** (provided by `VerificationEncoding` structure)
   - Must be proven for each concrete encoding strategy

3. **Technical axioms** for partial function behavior (execFromBlockP, etc.)
   - Could be eliminated with more complete definitional reasoning
