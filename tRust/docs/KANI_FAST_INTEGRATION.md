# Kani Fast Integration for tRust

**Date**: 2024-12-29
**Status**: Architecture Specification
**Canonical Source**: [kani_fast/docs/TRUST_INTEGRATION.md](https://github.com/dropbox/kani_fast/blob/main/docs/TRUST_INTEGRATION.md)

## Overview

tRust uses Kani Fast as its verification engine. This document specifies how tRust integrates Kani Fast as a library.

```
┌─────────────────────────────────────────────────────────────────────┐
│                           tRust                                     │
│                    (rustc fork - the compiler)                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Parse → HIR → MIR → Borrow Check → ┌──────────────┐ → Codegen     │
│                                     │ VERIFICATION │                │
│                                     │    PASS      │                │
│                                     └──────┬───────┘                │
│                                            │                        │
└────────────────────────────────────────────┼────────────────────────┘
                                             │ calls as library
                                             ▼
┌─────────────────────────────────────────────────────────────────────┐
│                        Kani Fast                                    │
│                  (verification engine library)                      │
├─────────────────────────────────────────────────────────────────────┤
│  MIR input → BMC → K-ind → CHC → AI Synth → Lean5 Gen              │
│                         ↓                                           │
│                        Z4                                           │
└─────────────────────────────────────────────────────────────────────┘
```

## Why This Architecture

### Separation of Concerns

| tRust (Compiler) | Kani Fast (Engine) |
|------------------|-------------------|
| Spec parsing (`#[requires]`, `#[ensures]`) | Verification algorithms |
| HIR/MIR extensions | Z4/Lean5 backend management |
| Compiler error emission | Counterexample extraction |
| Incremental compilation tracking | Clause database caching |
| IDE/rust-analyzer integration | AI invariant synthesis |
| Trust level enforcement | Proof generation |

### Benefits

1. **Parallel Development**: tRust can track upstream rustc while Kani Fast improves algorithms
2. **Independent Testing**: Kani Fast benchmarks without full compiler
3. **Standalone Usage**: `cargo kani-fast verify` works without tRust
4. **Clear API Boundary**: Kani Fast is a library with stable interface

## tRust Integration Points

### 1. New Compiler Pass: `rustc_verification`

Location: `compiler/rustc_verification/`

```rust
// compiler/rustc_verification/src/lib.rs

use kani_fast::{VerificationEngine, MirInput, VerificationResult};

pub fn verification_pass<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    specs: &FunctionSpecs,
) -> Result<(), VerificationError> {
    let config = VerificationConfig::from_session(tcx.sess);
    let engine = VerificationEngine::new(&config);

    let input = MirInput::from_rustc(tcx, body, specs);

    match engine.verify(input) {
        VerificationResult::Proven { .. } => Ok(()),
        VerificationResult::Disproven { counterexample, .. } => {
            Err(emit_counterexample_error(tcx, counterexample))
        }
        VerificationResult::Unknown { suggested_action, .. } => {
            handle_unknown(tcx, suggested_action)
        }
    }
}
```

### 2. Spec Attribute Parsing

tRust extends the attribute parser:

```rust
// Already specified in tRust ROADMAP.md Phase 1.2
#[requires(x > 0)]
#[ensures(result >= 0)]
#[invariant(self.len > 0)]
#[decreases(n)]
```

These are parsed by tRust and passed to Kani Fast as `FunctionSpecs`.

### 3. Error Emission

Convert Kani Fast results to rustc diagnostics:

```rust
fn emit_counterexample_error(
    tcx: TyCtxt,
    ce: StructuredCounterexample,
) -> VerificationError {
    let mut diag = tcx.sess.struct_err("verification failed");

    diag.span_label(ce.location, ce.message);

    if let Some(inputs) = ce.inputs {
        diag.note(format!("counterexample: {}", inputs));
    }

    for suggestion in ce.suggestions {
        diag.help(suggestion);
    }

    diag.emit()
}
```

### 4. Incremental Compilation Integration

tRust's incremental compilation tracks:
- Which functions changed (need re-verification)
- Kani Fast's clause database (for reuse)

```rust
// In tRust's incremental compilation
pub struct VerificationCache {
    /// Kani Fast's learned clauses
    kani_state: kani_fast::IncrementalState,

    /// Hash of verified function bodies
    verified: HashMap<DefId, Fingerprint>,
}

impl VerificationCache {
    pub fn needs_verification(&self, def_id: DefId, body: &Body) -> bool {
        let current_hash = body.fingerprint();
        self.verified.get(&def_id) != Some(&current_hash)
    }
}
```

### 5. Trust Level Enforcement

```rust
// tRust enforces trust levels before calling Kani Fast

match crate_trust_level {
    TrustLevel::Verified => {
        // Must verify everything
        verify_all_functions()?;
    }
    TrustLevel::Assumed => {
        // Skip verification (legacy code)
    }
    TrustLevel::Audited => {
        // Verify only functions with explicit specs
        verify_annotated_functions()?;
    }
}
```

## Kani Fast Escalation Pipeline

When tRust calls `engine.verify()`, Kani Fast internally escalates:

```
1. BMC (bounded, fast)
   ↓ needs unbounded
2. K-Induction (unbounded for simple loops)
   ↓ can't find k
3. CHC/Z4 Spacer (finds invariants automatically)
   ↓ timeout
4. AI Invariant Synthesis (LLM suggests invariant)
   ↓ still fails
5. Lean5 Proof Generation (synthesize theorem prover proof)
   ↓ can't generate
6. Return Unknown with suggested action
```

tRust doesn't need to know about this pipeline - it just calls `verify()` and gets a result.

## Configuration

### Cargo.toml

```toml
# In tRust's compiler/rustc_verification/Cargo.toml
[dependencies]
kani-fast = { git = "https://github.com/dropbox/kani_fast" }
```

### Compiler Flags

```
-Z verification-timeout=<seconds>     # Per-function timeout
-Z verification-strictness=<level>    # strict|best-effort|opt-in
-Z verification-ai-synthesis          # Enable AI invariant synthesis
-Z verification-lean5                 # Enable Lean5 proof generation
-Z verification-threads=<n>           # Parallelism for portfolio
```

### Environment Variables

```bash
TRUST_VERIFICATION_TIMEOUT=60
TRUST_VERIFICATION_CACHE_DIR=~/.trust/verification_cache
TRUST_Z4_PATH=/path/to/z4
TRUST_LEAN5_PATH=/path/to/lean5
```

## Timeline

| tRust Phase | Kani Fast Dependency | Target |
|-------------|---------------------|--------|
| Phase 2.2: Z4 Backend | Kani Fast with Z4 | Basic verification |
| Phase 2.3: Verification Pass | Kani Fast library API | Integration |
| Phase 4.3: Kani Integration | Kani Fast BMC + k-ind | Full bounded/unbounded |
| Phase 8: Lean5 Integration | Kani Fast Lean5 gen | Complex proofs |

## Testing the Integration

### Unit Tests

```rust
#[test]
fn test_simple_verification() {
    let mir = parse_mir("fn foo(x: i32) { assert!(x > 0); }");
    let specs = FunctionSpecs::requires("x > 0");

    let result = verify_function(&mir, &specs, &default_config());
    assert!(matches!(result, VerificationResult::Proven { .. }));
}
```

### Integration Tests

```bash
# In tRust repo
$ cargo test -p rustc_verification

# Full compiler test
$ ./x.py test --stage 1 compiler/rustc_verify
```

### Benchmark

```bash
# Verify real crate
$ trust build --release path/to/crate

# Compare to regular rustc
$ rustc build --release path/to/crate
```

## Related Projects

| Project | Repo | Role |
|---------|------|------|
| **Kani Fast** | [github.com/dropbox/kani_fast](https://github.com/dropbox/kani_fast) | Verification engine (this integrates) |
| **Z4** | [github.com/dropbox/z4](https://github.com/dropbox/z4) | SAT/SMT backend for Kani Fast |
| **Lean5** | [github.com/dropbox/lean5](https://github.com/dropbox/lean5) | Theorem prover backend |
| **TLA2** | [github.com/dropbox/tla2](https://github.com/dropbox/tla2) | Temporal logic (Phase 6) |
| **DashProve** | [github.com/dropbox/dashprove](https://github.com/dropbox/dashprove) | Unified verification platform |

## See Also

- **Canonical integration spec**: [kani_fast/docs/TRUST_INTEGRATION.md](https://github.com/dropbox/kani_fast/blob/main/docs/TRUST_INTEGRATION.md)
- **tRust roadmap**: [ROADMAP.md](../ROADMAP.md)
- **Z4 requirements**: [z4/docs/KANI_FAST_REQUIREMENTS.md](https://github.com/dropbox/z4/blob/main/docs/KANI_FAST_REQUIREMENTS.md)
