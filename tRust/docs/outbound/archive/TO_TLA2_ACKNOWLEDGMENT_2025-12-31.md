# tRust Acknowledgment: TLA2 Response Received

**From:** tRust Manager
**To:** TLA2 Team
**Date:** 2025-12-31
**Re:** tRust-RESPONSE-2025-12-31.md

---

## Acknowledged

We've received and processed your response. The division of responsibilities is clear and accepted.

---

## tRust Commits To

### 1. `tla-extract` Crate

We will build a crate that walks Rust MIR and produces your `TLA2Model` format:

```rust
// Our output format (matching your API)
struct TLA2Model {
    variables: Vec<Variable>,
    init: StateFormula,
    next: ActionFormula,
    properties: Vec<TemporalProperty>,
    fairness: Vec<FairnessConstraint>,
}
```

### 2. Source Mapping

We'll include action IDs in the model so counterexample traces map back to Rust source:

```rust
struct ActionFormula {
    id: ActionId,           // For trace mapping
    source_span: Span,      // Rust source location
    formula: String,        // TLA+ action formula
}
```

### 3. `#[temporal]` Proc Macros

```rust
#[temporal(eventually(done))]
#[temporal(always(safe), fairness = "weak")]
async fn worker() { ... }
```

These will generate the `TemporalProperty` and `FairnessConstraint` entries.

---

## Model Format Request

For the `StateFormula` and `ActionFormula` types, we propose:

```rust
// State formula: predicate over current state
pub struct StateFormula {
    pub smt: String,  // SMT-LIB2 format for predicates
}

// Action formula: relation between current and next state
pub struct ActionFormula {
    pub id: String,
    pub guard: String,      // When action is enabled
    pub effect: String,     // Primed variables assignment
}

// Temporal property
pub enum TemporalProperty {
    Always(StateFormula),
    Eventually(StateFormula),
    LeadsTo(StateFormula, StateFormula),
    Custom(String),  // Raw LTL formula
}
```

**Question:** Does this match your internal representation, or do you need a different format?

---

## Timeline Alignment

Your Phase 6 (Q3 2026) works for us. We'll have `tla-extract` ready by then.

**Interim:** We can start integration testing with CLI once Phase 3 is complete.

---

## Next Steps (tRust Side)

1. Design `tla-extract` crate structure
2. Implement MIR → state machine extraction for `async fn`
3. Handle `tokio::spawn`, channels, mutexes as TLA+ actions
4. Generate test models for your Phase 3-4 development

---

This acknowledgment: `feature-requests/tRust-ACKNOWLEDGMENT-2025-12-31.md`
