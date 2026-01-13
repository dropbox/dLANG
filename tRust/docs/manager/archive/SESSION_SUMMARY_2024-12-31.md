# Session Summary: 2024-12-31

## Major Accomplishments

### 1. tRust Pivot Completed
- Killed cargo-trust worker (was building wrong thing)
- Created `rustc_verify` crate in `upstream/rustc/compiler/`
- Added `-Zverify` flag to compiler
- **Stage 1 compiler builds and works**
- Verification pass runs after borrow checking
- Worker now on correct path (commits #44-#46)

### 2. Design Decisions Locked In

**Automatic Verification by Default:**
- Everything provable is proven (no opt-in)
- Opt-out via comments: `// #[trust(overflow)]`
- Phases: overflow/bounds → unwrap → termination → resources

**Tool Ownership:**
| Feature | Owner |
|---------|-------|
| Abstract Interpretation | Kani Fast |
| Typestate Analysis | Kani Fast |
| Concurrency | TLA2 |
| Floating Point | Z4 |

### 3. Directives Sent

| Repo | Directive | Status |
|------|-----------|--------|
| kani_fast | Abstract Interpretation | ✓ Pushed |
| kani_fast | Typestate Analysis | ✓ Pushed |
| tla2 | Rust Concurrency Verifier | ✓ Pushed |
| z4 | Floating Point Theory | ✓ Pushed |

## Ecosystem Architecture

```
                         tRust (rustc fork)
                         ├── rustc_verify pass
                         │
          ┌──────────────┼──────────────┬──────────────┐
          ▼              ▼              ▼              ▼
      Kani Fast        TLA2            Z4           Lean5
    ┌─────┴─────┐   (concurrency)  (SMT solver)  (proofs)
    │           │
    │  Engines: │
    │  - BMC    │
    │  - K-Ind  │
    │  - CHC ───┼──► Z4
    │  - AI Synth
    │  - Abstract Interp (NEW)
    │  - Typestate (NEW)
    │
    └───────────┘
```

## Current Worker Status

- **tRust worker:** Iteration ~2, building on rustc fork
- **Last commit:** #46 - Verify -Zverify flag works end-to-end
- **Stage 1 compiler:** Built at `upstream/rustc/build/host/stage1/bin/rustc`

## Key Files

- `docs/manager/PIVOT_TO_RUSTC_FORK.md` - Original pivot directive
- `docs/manager/DESIGN_AUTO_VERIFICATION.md` - Auto-verify design
- `docs/manager/WORKER_DIRECTIVE_RUSTC_FORK.md` - Worker instructions
- `upstream/rustc/compiler/rustc_verify/` - Verification pass

## Next Steps

1. **tRust:** Integrate Kani Fast library into rustc_verify
2. **Kani Fast:** Implement Abstract Interpretation + Typestate
3. **TLA2:** Build extraction from Rust MIR
4. **Z4:** Add FP theory

## Design Principles

1. **Verification by default** - If provable, prove it
2. **Comments for specs** - `// #[requires(...)]` not attributes
3. **Round-trip to source** - Errors map back to Rust code
4. **All Rust** - No C++/OCaml dependencies in verification stack
5. **Library APIs** - tRust calls tools, not vice versa

## Repos

| Repo | URL | Purpose |
|------|-----|---------|
| tRust | dropbox/dLANG/tRust | rustc fork with verification |
| Kani Fast | dropbox/kani_fast | Verification engine |
| Z4 | dropbox/z4 | SMT solver in Rust |
| TLA2 | dropbox/tla2 | Concurrency verification |
| Lean5 | TBD | Theorem prover in Rust |
| CROWN | ~/gamma-crown | NN verification |
