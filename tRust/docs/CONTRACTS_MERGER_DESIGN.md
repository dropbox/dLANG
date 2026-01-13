# tRust + Upstream Contracts Merger Design

**Date**: 2026-01-04
**Author**: MANAGER
**Status**: COMPLETE - All phases implemented

**Progress**:
- [x] **Phase 1** (iteration #942): Re-enable upstream contracts
- [x] **Phase 2** (iteration #943): Hook into contract expansion (marker attributes)
- [x] **Phase 3** (iteration #944): Create ContractsVerify MIR pass
- [x] **Phase 4** (iteration #945): Wire up Z4 SMT solver
- [x] **Phase 5** (iteration #946): Implement runtime check elision
- [x] **Phase 6** (iteration #947): Add control flags

---

## Executive Summary

tRust will **enhance** upstream's `#[feature(contracts)]` rather than replace it. When tRust can prove a contract at compile time, the runtime check is elided. When it can't, upstream's runtime check remains as a fallback.

**Result**: Same syntax as upstream, better guarantees, full compatibility.

---

## Current State (Problem)

```
Upstream rustc:
  #[requires(x > 0)]  →  Runtime assertion (panic if violated)

tRust (current):
  #[requires(x > 0)]  →  Compile-time proof (compiler error if unproven)

Conflict: Same attribute name, different behavior
Current hack: Disable upstream contracts entirely
```

**This is unsustainable.** tRust diverges from Rust, breaking compatibility.

---

## Target State (Solution)

```
tRust (merged):
  #[requires(x > 0)]
       ↓
  tRust verification pass
       ↓
  ┌────────────────┬────────────────┐
  │                │                │
  PROVEN         UNKNOWN         DISPROVEN
  │                │                │
  ↓                ↓                ↓
  Elide runtime   Keep runtime    Compiler error
  check           check           with counterexample
```

### Behavior Matrix

| tRust Result | Action | Runtime Cost | User Experience |
|--------------|--------|--------------|-----------------|
| **PROVEN** | Remove runtime check | Zero | Silent success |
| **UNKNOWN** | Keep upstream check | Runtime assertion | Works like upstream |
| **DISPROVEN** | Compiler error | N/A | Error + counterexample |

---

## Architecture

### Phase 1: Contract Interception

```
┌─────────────────────────────────────────────────────────────┐
│                      rustc pipeline                          │
│                                                              │
│  Parse → HIR → MIR → [tRust Verification Pass] → Codegen    │
│                              ↓                               │
│                    ┌─────────────────┐                       │
│                    │ Contract Check  │                       │
│                    │                 │                       │
│                    │ 1. Extract VCs  │                       │
│                    │ 2. Query Z4     │                       │
│                    │ 3. Annotate MIR │                       │
│                    └─────────────────┘                       │
│                              ↓                               │
│                    ┌─────────────────┐                       │
│                    │ MIR Transform   │                       │
│                    │                 │                       │
│                    │ If PROVEN:      │                       │
│                    │   Remove check  │                       │
│                    │ If UNKNOWN:     │                       │
│                    │   Keep check    │                       │
│                    └─────────────────┘                       │
└─────────────────────────────────────────────────────────────┘
```

### Phase 2: Runtime Check Elision

Upstream's contracts generate MIR like:
```rust
// Generated for #[requires(x > 0)]
if !contract_check_requires(x > 0) {
    panic!("precondition violated");
}
```

tRust's verification pass will:
1. Identify these contract check blocks
2. Query Z4 to prove the condition
3. If proven, replace with `assume(x > 0)` (zero-cost)
4. If unknown, leave the runtime check intact

### Phase 3: Proof Certificates

When tRust proves a contract, emit a certificate:
```rust
// In generated code or metadata
#[trust_proven(
    contract = "requires(x > 0)",
    prover = "Z4",
    proof_hash = "sha256:abc123..."
)]
```

This enables:
- Verification that proofs are fresh
- Caching across builds
- Audit trails

---

## Implementation Plan

### Step 1: Re-enable Upstream Contracts ✓ (iteration #942)

Revert the changes that disabled upstream contracts:
- `rustc_feature/src/unstable.rs`: Uncomment contracts feature
- `rustc_builtin_macros/src/lib.rs`: Uncomment contracts registration
- `library/core/src/contracts.rs`: Restore if removed

Verify: `#![feature(contracts)]` compiles again

### Step 2: Hook Into Contract Expansion ✓ (iteration #943)

Upstream's contract attributes expand to runtime checks. tRust intercepts this to add marker attributes.

Location: `upstream/rustc/compiler/rustc_builtin_macros/src/contracts.rs`

**Implementation**:
- Added `make_trust_marker_tokens()` helper function
- Modified `expand_requires_tts()` to prepend marker attributes
- Modified `expand_ensures_tts()` to prepend marker attributes

**Generated markers**:
```rust
#[doc(hidden)]
#[cfg_attr(trust_verify, trust_upstream_contract(kind = "requires", expr = "x > 0"))]
fn foo() contract_requires || { x > 0 } { ... }
```

The `cfg_attr` is only activated when `trust_verify` cfg is set, allowing the marker to be stripped in normal builds.

### Step 3: Create Contract Verification Pass ✓ (iteration #944)

New MIR pass in `compiler/rustc_mir_transform/src/contracts_verify.rs`.

**Implementation**:
- Created `ContractsVerify` MIR pass with `is_enabled()` controlled by `TRUST_CONTRACTS_VERIFY=1`
- Implemented `find_contract_checks()` to identify `contract_check_requires` and `contract_check_ensures` intrinsic calls
- Created `is_contract_intrinsic()` helper using lang item checking
- Added `ContractVerifyResult` enum with `Proven`, `Unknown`, and `Disproven` variants
- Placeholder `verify_contract()` returns `Unknown` (Z4 wiring is Phase 4)
- Added hooks for `register_proven_contract()`, `emit_unknown_warning()`, `emit_contract_violation_error()`
- Strict mode support via `TRUST_CONTRACTS_STRICT=1` for warnings on unknown contracts

**Result structure**:
```rust
pub struct ContractsVerify;

impl MirPass for ContractsVerify {
    fn run_pass(&self, tcx: TyCtxt, body: &mut Body) {
        let contract_checks = find_contract_checks(tcx, body);
        for check in &contract_checks {
            match verify_contract(tcx, def_id, check) {
                ContractVerifyResult::Proven { reason } => {
                    register_proven_contract(def_id, check, &reason);
                }
                ContractVerifyResult::Unknown { reason } => {
                    // Keep runtime check
                }
                ContractVerifyResult::Disproven { counterexample } => {
                    emit_contract_violation_error(tcx, check, &counterexample);
                }
            }
        }
    }
}
```

### Step 4: Wire Up Z4 Verification ✓ (iteration #945)

Implemented full Z4 SMT solver integration in `contracts_verify.rs`:

**Implementation**:
- Added `extract_closure_def_id()` to extract closure DefId from contract check arguments
- Added `extract_closure_from_type()` helper for various closure type kinds (Closure, FnDef, CoroutineClosure)
- Implemented `extract_predicate_from_mir()` to walk closure MIR and extract boolean predicates
- Implemented `rvalue_to_predicate()`, `operand_to_string()`, `place_to_string()`, `constant_to_string()` for MIR-to-string conversion
- Added `verify_predicate_with_smt()` that:
  - Handles trivial cases (`true` → Proven, `false` → Disproven)
  - Generates SMT-LIB query via `rustc_verify::specs::temporal_predicate_to_smt()`
  - Calls `rustc_verify::kani_bridge::run_smt_query()` to verify via Z4/Z3
  - Maps UNSAT → Proven (negation unsatisfiable = contract always holds)
  - Maps SAT → Disproven with counterexample
  - Maps UNKNOWN → Unknown with reason

**The `verify_contract` function now**:

```rust
fn verify_contract(tcx: TyCtxt, def_id: DefId, check: &ContractCheckInfo) -> ContractVerifyResult {
    // 1. Extract closure DefId from check
    let closure_def_id = check.closure_def_id?;

    // 2. Get closure MIR body
    let closure_body = tcx.optimized_mir(closure_def_id.as_local()?);

    // 3. Extract predicate string from MIR
    let predicate = extract_predicate_from_mir(tcx, closure_body)?;

    // 4. Verify via SMT
    verify_predicate_with_smt(&predicate)  // Uses Z4/Z3 via run_smt_query
}
```

**Added unit tests**:
- `test_is_predicate_expression_boolean`
- `test_is_predicate_expression_comparison`
- `test_is_predicate_expression_negation`
- `test_binop_to_string_comparisons`
- `test_binop_to_string_arithmetic`
- `test_verify_predicate_true`
- `test_verify_predicate_false`

### Step 5: Handle Elision

When a contract is proven, transform:
```rust
// Before (upstream generated)
if !requires_condition {
    panic!("precondition violated");
}

// After (tRust proven)
// Contract elided - no runtime check
// Optionally: core::intrinsics::assume(requires_condition);
```

**Implementation (iteration #946)**:
- Added `SafeOpKind::ContractCheck` to `rustc_verify::mir_optimization` with registration/query APIs.
- `ContractsVerify` registers proven contract check sites in the `SafeOperationRegistry`.
- New `ContractsElide` MIR pass removes `contract_check_requires` / `contract_check_ensures` calls
  at proven-safe locations (and preserves the return value for `ensures`).

### Step 6: Verification Reporting

**Critical**: When contracts can't be proven, emit detailed diagnostics to help improve the solver.

```
warning: contract could not be proven at compile time
  --> src/lib.rs:15:1
   |
15 | #[requires(x > 0 && y > 0)]
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^ this contract will be checked at runtime
   |
   = note: Z4 returned UNKNOWN after 500ms
   = note: unproven subexpression: `y > 0`
   = note: reason: `y` has no constraints in calling context
   = help: add bounds to parameter `y` or use #[trusted] if intentional
   = note: runtime fallback will panic if contract violated
```

**Verification Report File** (`-Zcontracts-report=path`):

```json
{
  "contracts": [
    {
      "file": "src/lib.rs",
      "line": 15,
      "function": "multiply",
      "contract_type": "requires",
      "expression": "x > 0 && y > 0",
      "result": "UNKNOWN",
      "time_ms": 500,
      "reason": "insufficient_constraints",
      "unproven_subexpr": "y > 0",
      "suggestions": ["add_parameter_bounds", "add_caller_requires"]
    },
    {
      "file": "src/lib.rs",
      "line": 28,
      "function": "divide",
      "contract_type": "requires",
      "expression": "divisor != 0",
      "result": "PROVEN",
      "time_ms": 12
    }
  ],
  "summary": {
    "total": 45,
    "proven": 42,
    "unknown": 2,
    "disproven": 1,
    "coverage": "93.3%"
  }
}
```

This enables:
1. **Solver improvement**: Identify patterns Z4 struggles with
2. **User guidance**: Tell users exactly why proofs fail
3. **Metrics tracking**: Monitor verification coverage over time
4. **Prioritization**: Focus solver work on most common unknown cases

### Step 7: Verification Levels

Add `-Z` flags for user control:

| Flag | Behavior |
|------|----------|
| `-Zcontracts=verify` | Prove and elide (default) |
| `-Zcontracts=check` | Upstream behavior (runtime only) |
| `-Zcontracts=strict` | Error if any contract unproven |
| `-Zcontracts=off` | Disable all contract checking |
| `-Zcontracts-report=FILE` | Write verification report to FILE |
| `-Zcontracts-timeout=MS` | Z4 timeout per contract (default: 1000) |

---

## Compatibility Guarantees

### With Upstream Rust

| Scenario | tRust Behavior | Upstream Behavior |
|----------|----------------|-------------------|
| Contract proven | Silent, no runtime check | Runtime check |
| Contract unknown | Runtime check | Runtime check |
| Contract violated | Compiler error | Runtime panic |
| No `-Zverify` | Same as upstream | Same |

**Key guarantee**: Code that compiles with upstream `#[feature(contracts)]` will compile with tRust (possibly with additional compile-time errors for provably wrong contracts).

### Migration Path

1. Existing tRust code using `#[requires]`/`#[ensures]` continues to work
2. New code can use `#![feature(contracts)]` with full compatibility
3. tRust-specific verification is opt-in enhancement, not breaking change

---

## Testing Strategy

### Unit Tests
- Contract proven → no runtime check in MIR
- Contract unknown → runtime check preserved
- Contract disproven → compiler error emitted

### Integration Tests
- Upstream contract tests pass (11 that were failing)
- tRust verification tests pass (259/259)
- Mixed code (upstream + tRust) compiles correctly

### Compatibility Tests
- Compile top crates that use `#[feature(contracts)]`
- Verify same runtime behavior as upstream when proofs fail

---

## Success Criteria

1. `#![feature(contracts)]` works in tRust
2. All 11 previously failing contract tests pass
3. Proven contracts have zero runtime overhead
4. Unproven contracts fall back to runtime checks
5. tRust verification tests still pass (259/259)
6. No language divergence from upstream Rust

---

## Timeline Estimate

| Phase | Commits | Description |
|-------|---------|-------------|
| 1 | 2-3 | Re-enable upstream contracts |
| 2 | 3-5 | Hook contract expansion |
| 3 | 5-8 | Create verification pass |
| 4 | 2-3 | Wire up Z4 |
| 5 | 2-3 | Implement elision |
| 6 | 2-3 | Add control flags |
| **Total** | **16-25** | Full implementation |

---

## Risks and Mitigations

| Risk | Mitigation |
|------|------------|
| Z4 too slow for large contracts | Caching, timeout with fallback to unknown |
| Upstream contracts API changes | Track upstream, adapt as needed |
| Edge cases in elision | Comprehensive test suite |
| User confusion | Clear documentation, error messages |

---

## Conclusion

This merger makes tRust a **strict superset** of upstream Rust's contracts:
- Same syntax
- Same behavior when proofs fail
- Better behavior when proofs succeed (zero overhead)
- Additional safety (compile-time errors for wrong contracts)

No language divergence. Full compatibility. Superior guarantees.
