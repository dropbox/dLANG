# tRust Contracts vs Upstream Contracts

## Overview

tRust supports two contract systems that will be merged:

1. **tRust verification** (`trust_macros`): Compile-time verification via SMT solver
2. **Upstream contracts** (`#![feature(contracts)]`): Runtime contracts (now re-enabled)

## Current Status: All Phases Complete

As of iteration #947, **all 6 phases** of the contracts merger are complete:
1. Re-enabled upstream contracts (#942)
2. Hooked into contract expansion with marker attributes (#943)
3. Created ContractsVerify MIR pass (#944)
4. Wired up Z4 SMT solver verification (#945)
5. Implemented runtime check elision for proven contracts (#946)
6. Added `-Zcontracts` control flags (#947)

### What This Means

- `#![feature(contracts)]` compiles in tRust
- `core::contracts::requires` and `core::contracts::ensures` are available
- Contracts are verified at compile time via Z4 SMT solver
- Proven contracts have their runtime checks elided (zero overhead)
- Unproven contracts fall back to runtime checking
- tRust's `trust_macros` attributes continue to work unchanged

### Using Both Systems

Both contract systems now work together:

```rust
// tRust compile-time verification (trust_macros crate)
use trust_macros::{requires, ensures};

#[requires(x > 0)]
#[ensures(result >= 0)]
fn sqrt(x: f64) -> f64 { /* verified at compile time */ }

// Upstream runtime contracts (explicit import)
#![feature(contracts)]
use core::contracts::{requires as contract_requires, ensures as contract_ensures};

#[contract_requires(x > 0)]
fn runtime_checked(x: i32) -> i32 { /* checked at runtime */ }
```

## Merger Design

The full merger (Phases 2-6) will integrate both systems:

| tRust Result | Action | Runtime Cost |
|--------------|--------|--------------|
| **PROVEN** | Elide runtime check | Zero |
| **UNKNOWN** | Keep runtime check | Runtime assertion |
| **DISPROVEN** | Compiler error | N/A |

See `docs/CONTRACTS_MERGER_DESIGN.md` for the complete design.

## Why tRust's Approach is Superior

1. **Bugs caught earlier**: tRust catches contract violations at compile time
2. **Zero runtime overhead**: Proven contracts have no runtime checks
3. **Formal guarantees**: Mathematical proof that contracts are satisfied
4. **Fallback safety**: Unknown contracts still have runtime checks

## Technical Details

### Phase 1 Changes (iteration #942)

The upstream contracts feature was re-enabled by uncommenting:
- Feature declaration in `rustc_feature/src/unstable.rs`
- Contracts module and registration in `rustc_builtin_macros/src/lib.rs`
- Contracts module in `library/core/src/lib.rs`
- Builtin macros in `library/core/src/macros/mod.rs`

### Phase 2 Changes (iteration #943)

Contract expansions now include marker attributes for tRust verification:
- Added `make_trust_marker_tokens()` helper in `contracts.rs`
- Modified `expand_requires_tts()` to emit marker attributes
- Modified `expand_ensures_tts()` to emit marker attributes
- Marker format: `#[cfg_attr(trust_verify, trust_upstream_contract(kind = "...", expr = "..."))]`

### Control Flags (Phase 6)

Use `-Z` flags to control contract verification behavior:

| Flag | Behavior |
|------|----------|
| `-Zcontracts=verify` | Prove and elide (default) |
| `-Zcontracts=check` | Upstream behavior (runtime only) |
| `-Zcontracts=strict` | Error if any contract unproven |
| `-Zcontracts=off` | Disable all contract checking |
| `-Zcontracts-report=FILE` | Write verification report to FILE |
| `-Zcontracts-timeout=MS` | Z4 timeout per contract (default: 1000) |
