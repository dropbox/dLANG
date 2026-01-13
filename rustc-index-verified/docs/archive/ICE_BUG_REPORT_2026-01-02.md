# ICE Bug Report: Stolen MIR Body

**Date**: 2026-01-02
**Reporter**: rustc-index-verified MANAGER
**Severity**: Low (does not block verification output)

---

## Summary

trustc panics with "attempted to read from stolen value: rustc_middle::mir::Body" after completing verification and printing all results.

## Reproduction

```bash
cd ~/tRust/deps/rustc-index-verified
RUSTC=~/tRust/bin/trustc RUSTC_WRAPPER=./scripts/trust-workspace-wrapper.sh cargo check
```

Or directly (note: `tests/solver_limitations.rs` is an integration test, so it must be compiled as a `lib` crate):
```bash
~/tRust/bin/trustc tests/solver_limitations.rs --edition 2021 --cfg trust_verify --emit=metadata --crate-type=lib
```

## Error Output

```
thread 'rustc' panicked at compiler/rustc_verify/src/lib.rs:678:81:
attempted to read from stolen value: rustc_middle::mir::Body
stack backtrace:
   ...
  11: <rustc_data_structures::steal::Steal<rustc_middle::mir::Body>>::borrow
      at compiler/rustc_data_structures/src/steal.rs:38:13
  12: rustc_verify::verify_crate
      at compiler/rustc_verify/src/lib.rs:678:24
  13: rustc_interface::passes::run_required_analyses::{closure#3}
      at compiler/rustc_interface/src/passes.rs:892:13
```

## Analysis

The verification code in `rustc_verify/src/lib.rs:678` attempts to borrow MIR bodies after they have been "stolen" by a previous compiler pass. The `Steal<T>` wrapper is used by rustc to ensure single-ownership of expensive data structures, and attempting to access stolen data causes a panic.

**Location**: `compiler/rustc_verify/src/lib.rs:678`

**Root Cause**: The verification pass runs too late in the compilation pipeline, after MIR bodies have been consumed by codegen or another pass.

## Suggested Fix

One of:

1. **Run verification earlier** - Before MIR is stolen (e.g., during analysis phase before codegen)
2. **Clone MIR before stealing** - Take a copy before the body is consumed
3. **Use optimized_mir query** - Query for MIR bodies through the query system which may reconstruct them

## Impact

- **Does NOT block verification**: All VERIFIED/DISPROVEN results are printed before the panic
- **Blocks clean exit**: Cargo reports failure even when verification succeeds
- **Confusing**: Users may think verification failed when it succeeded

## Workaround

Check the output for VERIFIED/DISPROVEN results before the panic. The panic occurs after verification completes.

---

## Status Update (Worker #128)

As of 2026-01-02, this ICE was **not reproducible** in this repo:

- `RUSTC=~/tRust/bin/trustc RUSTC_WRAPPER=./scripts/trust-workspace-wrapper.sh cargo check` exits 0 with "Verification pass complete." and no panic.
- `~/tRust/bin/trustc tests/solver_limitations.rs --edition 2021 --cfg trust_verify --emit=metadata --crate-type=lib` exits 0 with no panic.

If the ICE still occurs elsewhere, re-check whether it depends on a specific compilation mode (e.g., `--output-format=json`, different crate types, or a particular crate graph / MIR pass ordering).

---

**Related**: This is separate from the solver limitations (L1-L6) documented in tests/solver_limitations.rs.
