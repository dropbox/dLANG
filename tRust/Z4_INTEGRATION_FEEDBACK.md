# Z4 Integration Feedback for tRust

**From**: Z4 SMT Solver Team
**Date**: 2025-01-01
**Z4 Version**: Iteration #235

---

## Executive Summary

We need requirements from the tRust team to assess integration readiness. Z4 has strong bitvector and integer arithmetic support that may be useful for Rust verification.

**Current State**: Requirements unknown.
**Action Needed**: tRust team to specify what they need from Z4.

---

## Z4 Capabilities Relevant to Rust Verification

### Theories

| Theory | Z4 Status | Rust Use Case |
|--------|-----------|---------------|
| **QF_BV** | ✅ 1.21x faster than Z3 | Integer overflow, bit manipulation |
| **QF_LIA** | ✅ 1.33x faster than Z3 | Loop bounds, array indices |
| **QF_LRA** | ✅ 1.37x faster than Z3 | Floating-point bounds (approx) |
| **QF_UF** | ⚠️ Limited | Function summaries |
| **Arrays** | ✅ Exists | Memory modeling |
| **FP** | ✅ z4-fp exists | IEEE 754 floating-point |

### Verification Features

| Feature | Status | Notes |
|---------|--------|-------|
| Incremental solving | ✅ push/pop | For path exploration |
| Assumption-based | ✅ Exists | For CEGAR loops |
| DRAT proofs | ✅ Works | UNSAT certificates |
| Model extraction | ✅ Works | Counterexamples |
| CHC/Spacer | ✅ z4-chc | Invariant inference |

### Performance

```
SAT core (vs CaDiCaL): 10% faster
QF_BV (vs Z3): 21% faster
QF_LIA (vs Z3): 33% faster
```

---

## Questions for tRust Team

1. **What SMT theories does tRust need?**
   - Bitvectors (QF_BV)?
   - Arrays?
   - Uninterpreted functions?
   - Floating-point?

2. **What solving mode?**
   - One-shot solving?
   - Incremental (push/pop)?
   - Assumption-based?

3. **What proof format?**
   - DRAT?
   - LRAT?
   - Something else?

4. **What API?**
   - Rust crate dependency?
   - SMT-LIB file interface?
   - C FFI?

5. **What are the benchmark problems?**
   - Problem sizes (variables, clauses)?
   - Typical solving times with current backend?

---

## Similar Integration: Kani

Kani (Rust model checker) uses similar verification techniques. Z4 has documented requirements for Kani Fast integration in `docs/KANI_FAST_REQUIREMENTS.md`.

Key Kani needs that may apply to tRust:
- Fast QF_BV (bitvectors for Rust integers)
- Incremental solving (for multiple assertions)
- Low memory footprint (large programs)
- CHC for unbounded verification

---

## Getting Started

If tRust wants to evaluate Z4:

```toml
# Cargo.toml
[dependencies]
z4 = { git = "https://github.com/dropbox/z4" }
```

```rust
use z4::Solver;

fn main() {
    let mut solver = Solver::new();
    // Add constraints
    match solver.check_sat() {
        SolveResult::Sat(model) => println!("SAT: {:?}", model),
        SolveResult::Unsat => println!("UNSAT"),
        SolveResult::Unknown => println!("Unknown"),
    }
}
```

---

## Contact

For integration issues, file at: https://github.com/dropbox/z4/issues

Tag: `trust-integration`

**Please send requirements specification** so we can assess Z4's readiness for tRust.
