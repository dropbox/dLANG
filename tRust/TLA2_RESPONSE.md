# TLA2 Response to tRust Feature Request

**From:** TLA2 Team (git@github.com:dropbox/tla2.git)
**To:** tRust Team
**Date:** 2025-12-31

---

## Executive Summary

We've reviewed your feature request and integrated it into our roadmap as **Phase 6: tRust Integration**. This document provides:

1. Answers to your 5 questions
2. API specification for integration
3. Architecture decisions
4. Timeline and dependencies
5. What we need from you

**Bottom line**: TLA2 will provide a **programmatic Rust API** for model checking temporal properties. tRust handles MIR extraction and source mapping. We handle the verification engine.

---

## Answers to Your Questions

### Q1: Can you extract state machines from async Rust automatically? Or need annotations?

**Answer: tRust extracts, TLA2 checks.**

State machine extraction from MIR is **tRust's responsibility**. This is the correct division:

- **tRust** has access to rustc internals, MIR, and source spans
- **TLA2** is a verification engine that doesn't depend on rustc

You build `tla-extract` crate that walks MIR and produces:
```rust
pub struct StateMachine {
    pub states: Vec<State>,
    pub init: StateId,
    pub transitions: Vec<Transition>,
    pub variables: Vec<Variable>,
}

pub struct Transition {
    pub from: StateId,
    pub to: StateId,
    pub guard: Expr,        // TLA2 expression
    pub action: Action,     // Variable assignments
    pub action_id: ActionId, // For source mapping back to Rust
}
```

TLA2 model-checks this. On violation, we return `ActionId` values that you map back to Rust spans.

### Q2: How do you handle `tokio::select!`—true nondeterminism or scheduled?

**Answer: True nondeterminism.**

TLA2 models **true nondeterminism**. This is the correct semantics for distributed systems verification. In TLA+ terms:

```tla
\* tokio::select! becomes:
Next == SelectBranch1 \/ SelectBranch2 \/ SelectBranch3
```

The model checker explores ALL interleavings. If ANY interleaving violates a property, we report it. This is more conservative than any scheduler—if TLA2 says it's safe, it's safe under any scheduling.

**Rationale**: Distributed systems must work under adversarial scheduling. Testing with a specific scheduler gives false confidence. True nondeterminism catches bugs that only appear under specific (rare) schedules.

### Q3: Fairness: weak fairness or strong fairness by default?

**Answer: No fairness by default. Explicit opt-in.**

This matches TLC's semantics and is the safest default:

```rust
// No fairness - allows infinite stuttering
#[temporal(eventually(done))]
async fn process() { ... }
// ↑ This will FAIL if any path can stutter forever

// With fairness - progress guaranteed
#[temporal(eventually(done), fairness = "weak")]
async fn process() { ... }
// ↑ This requires process_action to eventually run if continuously enabled
```

**Weak fairness (WF)**: If an action is continuously enabled, it eventually happens.
**Strong fairness (SF)**: If an action is repeatedly enabled (even with gaps), it eventually happens.

For tRust integration:
```rust
pub enum Fairness {
    None,              // Default - stuttering allowed
    Weak(ActionId),    // WF_vars(Action)
    Strong(ActionId),  // SF_vars(Action)
}
```

### Q4: Can TLA2 run incrementally? (Re-check only changed functions)

**Answer: Not yet. Planned for Phase 4.**

**Current state**: Full re-check on every run. Fast enough for small-medium specs:
- 500K states in 5 seconds (8 workers)
- 50K states in <1 second

**Planned (Phase 4 - 10,000x Performance)**:
- Incremental state space caching
- Only re-explore from changed transitions
- Compositional verification (check modules independently)

**Workaround for now**: Use bounded checking during development:
```rust
TLA2Config {
    max_depth: 100,      // Quick check
    max_states: 10_000,  // Bound exploration
    ..Default::default()
}
```

### Q5: Integration: library call or separate process?

**Answer: Library call preferred. CLI fallback available.**

**Library API (preferred)**:
```rust
use tla2_check::{Model, Config, check, CheckResult};

let model = Model::new()
    .with_state_machine(state_machine)
    .with_property(Property::Eventually(predicate))
    .with_fairness(Fairness::Weak(action_id));

let config = Config {
    workers: 8,
    max_states: 1_000_000,
    timeout: Duration::from_secs(60),
};

match check(&model, &config) {
    CheckResult::Verified { states, time } => {
        // Property holds for all reachable states
    }
    CheckResult::Violation { trace, property } => {
        // trace contains ActionIds for source mapping
    }
    CheckResult::Timeout { states, suggestion } => {
        // suggestion: "Try reducing max_nodes from 5 to 3"
    }
}
```

**CLI fallback** (for process isolation):
```bash
$ tla2 check --format=json model.json > result.json
```

Library is faster (no serialization). CLI allows sandboxing if needed.

---

## API Specification

### Input: TemporalVC

```rust
/// Verification condition for temporal properties
pub struct TemporalVC {
    /// Unique identifier for this VC
    pub id: VCId,

    /// State machine extracted from async code
    pub state_machine: StateMachine,

    /// Temporal properties to verify
    pub properties: Vec<TemporalProperty>,

    /// Fairness constraints
    pub fairness: Vec<Fairness>,

    /// Failure model (optional)
    pub fault_model: Option<FaultModel>,

    /// Bounds for model checking
    pub bounds: Bounds,
}

pub struct StateMachine {
    pub variables: Vec<Variable>,
    pub init: Predicate,
    pub next: Vec<Transition>,
}

pub struct Transition {
    pub name: String,
    pub guard: Predicate,
    pub assignments: Vec<Assignment>,
    pub action_id: ActionId,  // For source mapping
}

pub enum TemporalProperty {
    Always(Predicate),           // []P
    Eventually(Predicate),       // <>P
    LeadsTo(Predicate, Predicate), // P ~> Q
    Until(Predicate, Predicate),   // P U Q
}

pub struct FaultModel {
    pub node_crashes: Option<u32>,      // Max simultaneous crashes
    pub network_partitions: bool,
    pub message_loss: Option<f64>,      // Probability
    pub message_reorder: bool,
    pub message_duplicate: bool,
}

pub struct Bounds {
    pub max_nodes: usize,
    pub max_steps: usize,
    pub max_states: usize,
    pub timeout: Duration,
}
```

### Output: TLA2Result

```rust
pub enum TLA2Result {
    /// Property verified for all reachable states
    Verified {
        states_explored: u64,
        distinct_states: u64,
        time: Duration,
        max_depth: u32,
    },

    /// Property violated - counterexample found
    Violation {
        property: String,
        trace: CounterexampleTrace,
        time: Duration,
    },

    /// Timeout before completion
    Timeout {
        states_explored: u64,
        coverage_estimate: f64,  // 0.0-1.0
        suggestion: String,
    },

    /// Model error (not a property violation)
    Error {
        message: String,
        location: Option<ActionId>,
    },
}

pub struct CounterexampleTrace {
    /// Sequence of states leading to violation
    pub states: Vec<State>,

    /// Actions taken between states (for source mapping)
    pub actions: Vec<ActionId>,

    /// For liveness: prefix + lasso structure
    pub lasso: Option<LassoInfo>,
}

pub struct LassoInfo {
    pub prefix_len: usize,  // States before the loop
    pub loop_start: usize,  // Where the loop begins
}
```

### Source Mapping Contract

TLA2 returns `ActionId` values that tRust provided in the `Transition` structs. tRust is responsible for mapping these back to Rust source spans.

```rust
// tRust side
struct SourceMapping {
    action_id_to_span: HashMap<ActionId, Span>,
}

impl SourceMapping {
    fn format_trace(&self, trace: &CounterexampleTrace) -> String {
        let mut output = String::new();
        for (i, action_id) in trace.actions.iter().enumerate() {
            let span = self.action_id_to_span.get(action_id);
            writeln!(output, "Step {}: {} at {:?}", i, action_id, span);
        }
        output
    }
}
```

---

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                         tRust Compiler                          │
│                                                                 │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────────────┐ │
│  │   rustc     │───►│ tla-extract │───►│     tla2_check      │ │
│  │   (MIR)     │    │ (Your crate)│    │   (Our library)     │ │
│  └─────────────┘    └─────────────┘    └──────────┬──────────┘ │
│                            │                       │            │
│                            │                       ▼            │
│                            │              ┌───────────────┐     │
│                            │              │  TLA2Result   │     │
│                            │              └───────┬───────┘     │
│                            │                      │             │
│                            ▼                      ▼             │
│                     ┌────────────────────────────────────┐      │
│                     │         tla-report                 │      │
│                     │  (ActionId → Span → rustc error)   │      │
│                     └────────────────────────────────────┘      │
└─────────────────────────────────────────────────────────────────┘
```

**Division of responsibility:**

| Component | Owner | Description |
|-----------|-------|-------------|
| MIR access | tRust | rustc internals |
| State machine extraction | tRust | `tla-extract` crate |
| Source span tracking | tRust | ActionId → Span mapping |
| Model checking engine | TLA2 | `tla2_check` library |
| Temporal logic | TLA2 | LTL/CTL formulas |
| Counterexample generation | TLA2 | Trace with ActionIds |
| Error formatting | tRust | rustc diagnostic integration |

---

## Failure Model Support

We will support the failure models you requested:

### Node Crash (Fail-Stop)
```rust
FaultModel {
    node_crashes: Some(2),  // Up to 2 nodes can crash
    ..Default::default()
}
```

Internally modeled as:
```tla
\* Node can crash at any time
NodeCrash(n) ==
    /\ alive[n]
    /\ alive' = [alive EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<other_vars>>
```

### Network Partition
```rust
FaultModel {
    network_partitions: true,
    ..Default::default()
}
```

Modeled as partitioning the node set into disjoint groups.

### Message Faults
```rust
FaultModel {
    message_loss: Some(0.01),     // 1% loss
    message_reorder: true,
    message_duplicate: true,
    ..Default::default()
}
```

Modeled by making the network a set (allows reorder/duplicate) with nondeterministic drop.

---

## Performance Targets

We commit to these targets:

| Scenario | Target | Current |
|----------|--------|---------|
| 3 nodes, 100 steps | < 10s | ~2s |
| 5 nodes, 100 steps | < 60s | ~30s |
| 5 nodes, 1000 steps | < 10min | TBD |
| With symmetry | 10x speedup | 5x (partial) |

**Current performance**:
- 500K states in 5s (8 workers, safety only)
- Liveness checking: 120x faster than TLC on bcastFolklore

**Planned optimizations**:
- DPOR (10-1000x reduction in states)
- Full symmetry reduction
- SIMD fingerprinting

---

## What We Need From You

### 1. StateMachine Format Specification

We need you to define the exact structure of `StateMachine` you'll produce from MIR. Key questions:

- How do you represent async state (futures, poll states)?
- How do you handle generic functions with multiple instantiations?
- Do you inline function calls or model them as atomic?

### 2. Test Cases

Please provide test cases from your vision:

1. **Simple deadlock** - Two mutexes, wrong order
2. **Async race** - Channel send/recv timing
3. **Distributed consensus** - Raft leader election

We'll validate TLA2 produces correct results on these.

### 3. Performance Benchmarks

What are realistic sizes for your workloads?

- Typical number of states?
- Typical number of processes/threads?
- Typical depth of traces?

This helps us prioritize optimizations.

---

## Timeline

| Phase | TLA2 Deliverable | Estimated |
|-------|------------------|-----------|
| Phase 1-2 | Fix correctness bugs, test coverage | Current |
| Phase 3 | Programmatic API (library call) | Q1 2026 |
| Phase 4 | 10,000x performance | Q2 2026 |
| Phase 6 | Full tRust integration | Q3 2026 |

**We can prioritize the programmatic API earlier if you need it sooner.** File an issue at https://github.com/dropbox/tla2/issues with label `tRust-integration`.

---

## Current Status (Honest Assessment)

### Working
- Safety checking (64 specs validated)
- Basic liveness ([], <>, ~>)
- Fairness (WF_, SF_)
- Sequential performance (12% faster than TLC)

### Known Issues (Being Fixed)
- **False positive liveness** on some specs (MCLiveInternalMemory)
- **Quantified leads-to** (\A x: P ~> Q) not supported
- **Test coverage** inadequate (only 2/56 liveness specs tested)

### Blocked
- Performance optimization blocked until correctness proven
- tRust integration blocked until API stabilizes

**We won't ship broken software.** Correctness comes first.

---

## Contact

- TLA2 issues: https://github.com/dropbox/tla2/issues
- Label tRust requests: `tRust-integration`
- This response: `TLA2_RESPONSE.md`

---

## Appendix: Insights from Lean5

We reviewed the lean5 project and will adopt these patterns:

1. **Batch checking API** - Check multiple properties in one call
2. **Structured JSON output** - AI-friendly result format
3. **Performance benchmarks** - Explicit targets with measurements
4. **Testing strategy** - Round-trip tests, property tests, oracle comparison (TLC)

These align well with tRust's needs for AI agent integration.
