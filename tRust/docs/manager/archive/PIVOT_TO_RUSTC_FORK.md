# PIVOT: Build the REAL tRust (rustc Fork)

**Date**: 2024-12-31
**Priority**: CRITICAL - We've been building the wrong thing
**Status**: IMMEDIATE PIVOT REQUIRED

## What We Built (Wrong)

```
cargo-trust (separate tool) → rustc_private → Z3
```

This is exactly what the architecture docs said NOT to build:
> "This is NOT another Kani/Creusot/Prusti"

We built another Kani. We already HAVE Kani (and Kani Fast).

## What We Should Build (The Vision)

```
tRust (rustc fork)
    └── rustc_verify (new compiler pass)
            └── calls Kani Fast (library)
                    └── uses Z4, Lean5, TLA2, CROWN
```

The proof tools go IN THE COMPILER where they have maximum information.

## The Ecosystem (All Being Built in Rust)

| Tool | Repo | Purpose |
|------|------|---------|
| **Z4** | ~/z4 | SMT solver (Z3 in Rust) |
| **Kani Fast** | kani_fast | Verification engine (BMC + k-ind + CHC) |
| **Lean5** | TBD | Theorem prover (Lean 4 in Rust) |
| **TLA2** | tla2 | Temporal logic (TLA+ in Rust) |
| **CROWN** | ~/gamma-crown | Neural network verification |

These are dependencies. tRust INTEGRATES them into rustc.

## The Real Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                           tRust (rustc fork)                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  rustc_parse    → Parse #[requires], #[ensures] NATIVELY            │
│       ↓                                                             │
│  rustc_ast      → AST includes spec expressions                     │
│       ↓                                                             │
│  rustc_hir      → HIR carries specifications                        │
│       ↓                                                             │
│  rustc_mir_build → MIR preserves spec info                          │
│       ↓                                                             │
│  rustc_verify   → NEW CRATE: calls Kani Fast                        │
│       ↓                                                             │
│  Codegen        → Only if verified (or trust_level = assumed)       │
│                                                                     │
└───────────────────────────────────┬─────────────────────────────────┘
                                    │
                                    │ library call
                                    ▼
┌─────────────────────────────────────────────────────────────────────┐
│                        Kani Fast (library)                          │
├─────────────────────────────────────────────────────────────────────┤
│  BMC → K-Induction → CHC/Z4 → AI Synthesis → Lean5 Generation       │
└─────────────────────────────────────────────────────────────────────┘
```

## Immediate Tasks

### Task 1: Set Up Rustc Fork Build

The upstream rustc is already cloned at `upstream/rustc/`. We need to:

1. Configure the build system
2. Successfully build rustc from source
3. Verify it works

```bash
cd upstream/rustc
./x.py build --stage 1 library
```

### Task 2: Add rustc_verify Crate

Create the new compiler crate:

```
upstream/rustc/compiler/rustc_verify/
├── Cargo.toml
├── src/
│   ├── lib.rs           # Main pass
│   ├── specs.rs         # Spec extraction from HIR
│   └── kani_bridge.rs   # Kani Fast integration
```

### Task 3: Wire Into Compilation Pipeline

Modify `rustc_interface` to run verification after borrow checking:

```rust
// In rustc_interface/src/passes.rs
fn analysis(tcx: TyCtxt<'_>) {
    // ... existing passes ...

    // NEW: Verification pass
    if tcx.sess.opts.unstable_opts.verify {
        rustc_verify::verify_crate(tcx);
    }
}
```

### Task 4: Integrate Kani Fast

Use Kani Fast's library API (already stable per status doc):

```rust
use kani_fast::engine::{VerificationEngine, MirInput, VerificationConfig};

pub fn verify_function(tcx: TyCtxt, body: &Body, specs: &FunctionSpecs) -> Result<(), VerificationError> {
    let config = VerificationConfig::from_session(&tcx.sess);
    let engine = VerificationEngine::new(&config);

    let input = MirInput::from_rustc(tcx, body, specs);

    match engine.verify(input).await {
        EngineResult::Proven { .. } => Ok(()),
        EngineResult::Disproven { counterexample, .. } => {
            tcx.sess.emit_err(VerificationFailed { counterexample });
            Err(VerificationError)
        }
        EngineResult::Unknown { .. } => {
            tcx.sess.warn("verification inconclusive");
            Ok(())
        }
    }
}
```

## What cargo-trust Was Good For

The work wasn't wasted:
- **Spec parsing** → Port to rustc_verify
- **WP calculus** → Compare with Kani Fast approach
- **Test cases** → Integration tests for rustc_verify

But cargo-trust itself is scaffolding. The real work is rustc modification.

## Build Prerequisites

```bash
# Install rustc build dependencies
xcode-select --install
brew install cmake ninja python3

# Check rustc build
cd upstream/rustc
./x.py check
```

## Success Criteria

```bash
# Build tRust compiler
$ cd upstream/rustc
$ ./x.py build --stage 1

# Verify a simple program
$ ./build/host/stage1/bin/rustc --verify examples/hello_verified.rs
Verifying clamp_positive...
  requires(n > 0): assumed
  ensures(result >= 1): proven
  ensures(result <= n): proven

# Verification error = compiler error
$ ./build/host/stage1/bin/rustc --verify examples/broken.rs
error[E0XXX]: verification failed
 --> examples/broken.rs:5:1
  |
5 | fn broken(n: i32) -> i32 { n }
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ postcondition `result > n` not satisfied
  |
  = note: counterexample: n = 1, result = 1
  = help: consider adding `#[requires(n > result)]`
```

## DO NOT

- Do not add more features to cargo-trust
- Do not use Z3 directly (use Kani Fast which uses Z4)
- Do not build another separate tool
- Do not skip the rustc build setup

## Timeline

1. **Iteration N+1**: Get rustc building from upstream/rustc
2. **Iteration N+2**: Add empty rustc_verify crate
3. **Iteration N+3**: Parse specs from attributes
4. **Iteration N+4**: Integrate Kani Fast

## References

- Kani Fast API: docs/external/KANI_FAST_STATUS_2025-12-30.md
- Architecture: docs/ARCHITECTURE_INTENT.md
- Integration: docs/KANI_FAST_INTEGRATION.md
