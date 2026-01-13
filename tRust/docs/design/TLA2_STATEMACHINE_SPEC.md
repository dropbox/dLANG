# TLA2 StateMachine Format Specification

**Version**: 1.0.0
**Date**: 2026-01-03
**Status**: Draft for TLA2 team review

This document specifies the StateMachine format that tRust will produce from MIR analysis for TLA2 model checking integration. It addresses the questions raised in TLA2_RESPONSE.md.

---

## Overview

tRust extracts state machines from async Rust code and provides them to TLA2 for temporal property verification. This document defines:

1. The StateMachine data structure format
2. How async state is represented (futures, poll states)
3. How generic functions are handled
4. Whether function calls are inlined or atomic
5. The ActionId source mapping contract

---

## StateMachine Format

### Core Types

```rust
/// State machine for TLA2 model checking.
/// Produced by tRust's tla-extract component from MIR analysis.
pub struct StateMachine {
    /// Unique name identifying this state machine
    pub name: String,

    /// State variables that comprise the machine's state
    pub variables: Vec<Variable>,

    /// Initial state predicate
    pub init: Predicate,

    /// Available transitions (actions)
    pub transitions: Vec<Transition>,

    /// Initial state index
    pub initial_state: StateId,

    /// Terminal state indices
    pub terminal_states: Vec<StateId>,

    /// Source mapping for diagnostics
    pub source_map: SourceMap,
}

/// A state variable tracked by the state machine
pub struct Variable {
    /// Variable name (corresponds to captured Rust variable)
    pub name: String,

    /// Variable type
    pub ty: VarType,

    /// Optional type invariant (always-true predicate)
    pub invariant: Option<Predicate>,

    /// Initial value expression
    pub initial_value: Option<Expr>,
}

/// Variable types supported in state machines
pub enum VarType {
    Bool,
    Int { bits: u8, signed: bool },
    Enum { name: String, variants: Vec<String> },
    Tuple(Vec<VarType>),
    Array { elem: Box<VarType>, len: usize },
    Set(Box<VarType>),
    Map { key: Box<VarType>, value: Box<VarType> },
    /// Opaque type (modeled as uninterpreted)
    Opaque(String),
}

/// A transition (action) in the state machine
pub struct Transition {
    /// Unique identifier for source mapping
    pub action_id: ActionId,

    /// Human-readable name
    pub name: String,

    /// Source state (None = enabled from any state)
    pub from: Option<StateId>,

    /// Target state (None = stays in same state)
    pub to: Option<StateId>,

    /// Guard condition (when is this transition enabled)
    pub guard: Predicate,

    /// State variable assignments
    pub assignments: Vec<Assignment>,

    /// Is this a yield/await point transition?
    pub is_yield: bool,

    /// Is this a poll/resume transition?
    pub is_poll: bool,
}

/// An assignment to a state variable
pub struct Assignment {
    /// Variable being assigned
    pub variable: String,

    /// New value expression
    pub value: Expr,
}

/// Unique identifier for source location mapping
#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub struct ActionId(pub u64);

/// Source location mapping
pub struct SourceMap {
    /// Maps ActionIds to Rust source spans
    pub action_spans: HashMap<ActionId, SourceSpan>,

    /// Maps StateIds to Rust source spans
    pub state_spans: HashMap<StateId, SourceSpan>,

    /// Maps variable names to their declaration spans
    pub variable_spans: HashMap<String, SourceSpan>,
}

pub struct SourceSpan {
    /// File path (relative to crate root)
    pub file: String,

    /// Start line (1-indexed)
    pub line_start: u32,

    /// Start column (1-indexed)
    pub col_start: u32,

    /// End line (1-indexed)
    pub line_end: u32,

    /// End column (1-indexed)
    pub col_end: u32,
}
```

### Predicate and Expression Types

```rust
/// A boolean predicate over state variables
pub enum Predicate {
    /// Boolean literal
    Bool(bool),

    /// State variable reference
    Var(String),

    /// Comparison
    Compare {
        left: Box<Expr>,
        op: CompareOp,
        right: Box<Expr>,
    },

    /// Logical not
    Not(Box<Predicate>),

    /// Logical and
    And(Vec<Predicate>),

    /// Logical or
    Or(Vec<Predicate>),

    /// Implication
    Implies(Box<Predicate>, Box<Predicate>),

    /// Set membership
    In { elem: Box<Expr>, set: Box<Expr> },

    /// Universal quantifier
    ForAll { var: String, domain: Box<Expr>, body: Box<Predicate> },

    /// Existential quantifier
    Exists { var: String, domain: Box<Expr>, body: Box<Predicate> },
}

pub enum CompareOp {
    Eq, Ne, Lt, Le, Gt, Ge,
}

/// An expression over state variables
pub enum Expr {
    /// Integer literal
    Int(i64),

    /// Boolean literal
    Bool(bool),

    /// Variable reference
    Var(String),

    /// Primed variable (next-state value)
    Prime(String),

    /// Arithmetic
    BinOp { left: Box<Expr>, op: BinOp, right: Box<Expr> },

    /// Unary operations
    UnaryOp { op: UnaryOp, arg: Box<Expr> },

    /// Conditional expression
    If { cond: Box<Predicate>, then_: Box<Expr>, else_: Box<Expr> },

    /// Tuple construction
    Tuple(Vec<Expr>),

    /// Tuple projection
    Project { tuple: Box<Expr>, index: usize },

    /// Set literal
    SetLit(Vec<Expr>),

    /// Set comprehension
    SetComp { var: String, domain: Box<Expr>, filter: Box<Predicate> },

    /// Function application (for opaque functions)
    Apply { func: String, args: Vec<Expr> },
}

pub enum BinOp {
    Add, Sub, Mul, Div, Mod,
    BitAnd, BitOr, BitXor,
    Shl, Shr,
}

pub enum UnaryOp {
    Neg, Not, BitNot,
}
```

---

## Async State Representation

### How Async Functions Are Modeled

Rust async functions are state machines. The compiler transforms:

```rust
async fn fetch_and_process(url: &str) -> Result<Data, Error> {
    let response = fetch(url).await;  // Yield point 1
    let parsed = parse(response).await; // Yield point 2
    Ok(process(parsed))
}
```

Into a state machine with states corresponding to suspension points:

```
States:
  S0: Start (initial)
  S1: Suspended at fetch().await
  S2: Suspended at parse().await
  S3: End (terminal)

Variables:
  - response: Option<Response>
  - parsed: Option<Parsed>
  - poll_state: {Pending, Ready}

Transitions:
  T0: S0 -> S1 [start_fetch]
      guard: true
      effect: poll_state := Pending

  T1: S1 -> S1 [poll_fetch_pending]
      guard: poll_state == Pending
      effect: (no change, retry)

  T2: S1 -> S2 [poll_fetch_ready]
      guard: poll_state == Ready
      effect: response := Some(result), poll_state := Pending

  T3: S2 -> S2 [poll_parse_pending]
      guard: poll_state == Pending
      effect: (no change, retry)

  T4: S2 -> S3 [poll_parse_ready]
      guard: poll_state == Ready
      effect: parsed := Some(result)
```

### Poll States

Each await point has an associated poll state:

```rust
pub enum PollState {
    /// Future not yet polled
    NotStarted,
    /// Future polled but returned Pending
    Pending,
    /// Future returned Ready with value
    Ready,
}
```

In the state machine, we track:
- Which yield point is current (implicit in state)
- The poll state for that yield point
- The result value (when Ready)

### Captured Variables

Variables that live across yield points become state variables:

```rust
async fn example() {
    let x = compute();      // x captured
    something().await;      // yield point
    use(x);                 // x used after yield
}
```

The extraction identifies `x` as a captured variable and includes it in the state machine's variables.

---

## Generic Function Handling

### Monomorphization

Generic functions are monomorphized (instantiated for each concrete type):

```rust
async fn process<T: Process>(item: T) -> T::Output {
    item.process().await
}

// Called as:
process::<UserData>(data);
process::<Config>(config);
```

Produces separate state machines:
- `process<UserData>`
- `process<Config>`

### Naming Convention

Monomorphized names follow Rust's convention:
```
function_name<Type1, Type2>
```

Example names:
- `HashMap::insert<String, i32>`
- `Option::map<i32, bool>`
- `process<UserData>`

### Type Parameters in Transitions

Transition guards and effects may reference type-specific operations:

```rust
// For process<UserData>
Transition {
    name: "call_process",
    guard: Predicate::Bool(true),
    assignments: vec![
        Assignment {
            variable: "result",
            // Opaque call to monomorphized method
            value: Expr::Apply {
                func: "UserData::process".to_string(),
                args: vec![Expr::Var("item".to_string())],
            },
        },
    ],
    ...
}
```

---

## Function Call Handling

### Atomic vs Inlined

**Default: Function calls are atomic.**

tRust models function calls as single transitions that invoke opaque functions:

```rust
fn caller() {
    let result = callee(arg);
}
```

Produces:
```
Transition {
    name: "call_callee",
    assignments: vec![
        Assignment {
            variable: "result",
            value: Expr::Apply { func: "callee", args: vec![Expr::Var("arg")] },
        },
    ],
}
```

### Why Atomic?

1. **State space control**: Inlining explodes state space
2. **Compositionality**: Functions verified separately
3. **Performance**: TLA2 checks smaller models faster

### Inlining Exceptions

Inlining occurs for:

1. **Closures passed to combinators**:
   ```rust
   items.iter().filter(|x| x > 0)
   ```
   The closure is inlined since it's part of the control flow.

2. **#[inline(always)] marked functions** (future enhancement)

3. **Explicitly annotated functions**:
   ```rust
   #[tla_inline]  // Future attribute
   fn small_helper() { ... }
   ```

### Async Function Calls

Async calls create yield points and are NOT atomic:

```rust
async fn caller() {
    let result = callee().await;  // Creates yield point
}
```

The `callee().await` creates:
- Transition to start the call
- Poll transitions while pending
- Transition when ready

---

## ActionId Source Mapping Contract

### Purpose

When TLA2 finds a property violation, it returns a trace of `ActionId` values. tRust maps these back to Rust source locations for user-friendly error messages.

### Contract

1. **tRust provides**: Every `Transition` has a unique `ActionId`
2. **TLA2 returns**: Violation traces as `Vec<ActionId>`
3. **tRust formats**: Maps `ActionId` to `SourceSpan` for diagnostics

### Example Usage

```rust
// TLA2 returns:
let violation = TLA2Result::Violation {
    property: "always(no_deadlock)".to_string(),
    trace: CounterexampleTrace {
        states: vec![...],
        actions: vec![ActionId(42), ActionId(17), ActionId(99)],
        ...
    },
};

// tRust maps:
impl SourceMap {
    fn format_trace(&self, trace: &CounterexampleTrace) -> String {
        let mut out = String::new();
        for (i, action_id) in trace.actions.iter().enumerate() {
            if let Some(span) = self.action_spans.get(action_id) {
                writeln!(out, "Step {}: {}:{}:{}",
                    i, span.file, span.line_start, span.col_start);
            }
        }
        out
    }
}
```

### ActionId Allocation

ActionIds are allocated during MIR traversal:

```rust
impl StateMachineExtractor {
    fn next_action_id(&mut self) -> ActionId {
        let id = ActionId(self.action_counter);
        self.action_counter += 1;
        id
    }

    fn extract_transition(&mut self, mir_block: &BasicBlock) -> Transition {
        let action_id = self.next_action_id();
        self.source_map.action_spans.insert(
            action_id,
            mir_block.source_info.span.into(),
        );
        Transition {
            action_id,
            ...
        }
    }
}
```

---

## Mapping from tRust Types

### Current tRust Types -> TLA2 Types

| tRust (vc_ir) | TLA2 StateMachine |
|---------------|-------------------|
| `AsyncStateMachine` | `StateMachine` |
| `AsyncState` | Implicit in `StateId` |
| `AsyncTransition` | `Transition` |
| `CapturedVariable` | `Variable` |
| `StateUpdate` | `Assignment` |
| `SourceSpan` | `SourceSpan` |

### Conversion Implementation

```rust
impl From<AsyncStateMachine> for StateMachine {
    fn from(asm: AsyncStateMachine) -> Self {
        let variables = asm.captured_variables.iter().map(|cv| Variable {
            name: cv.name.clone(),
            ty: convert_vc_type(&cv.ty),
            invariant: None,
            initial_value: None,
        }).collect();

        let transitions = asm.transitions.iter().enumerate().map(|(i, t)| {
            Transition {
                action_id: ActionId(i as u64),
                name: format!("t{}", i),
                from: Some(StateId(t.from)),
                to: Some(StateId(t.to)),
                guard: t.guard.clone().map(convert_predicate)
                    .unwrap_or(Predicate::Bool(true)),
                assignments: t.effect.iter().map(|su| Assignment {
                    variable: su.variable.clone(),
                    value: convert_expr(&su.value),
                }).collect(),
                is_yield: t.is_yield,
                is_poll: t.is_poll,
            }
        }).collect();

        StateMachine {
            name: asm.name,
            variables,
            init: Predicate::Bool(true), // Refined during extraction
            transitions,
            initial_state: StateId(asm.initial),
            terminal_states: asm.finals.iter().map(|&i| StateId(i)).collect(),
            source_map: SourceMap::default(), // Populated during extraction
        }
    }
}
```

---

## Integration Timeline

### Phase 1: Current (Q1 2026)
- This specification document
- tRust provides `AsyncStateMachine` types
- Manual conversion for prototyping

### Phase 2: TLA2 API Ready (Q2-Q3 2026)
- tRust implements `tla-extract` crate
- Automatic conversion from MIR to `StateMachine`
- Integration with `-Zverify` flag

### Phase 3: Full Integration (Q4 2026)
- Counterexample traces mapped to rustc diagnostics
- Temporal properties in verification reports
- IDE integration for hover/diagnostics

---

## Open Questions for TLA2 Team

1. **Set operations**: Should we use TLA2's set operations or model sets as arrays?
2. **Recursion**: How to handle recursive async functions?
3. **Channels**: Should `mpsc::channel` be modeled as built-in or user-defined?
4. **Timeouts**: How to model `tokio::time::timeout`?

---

## References

- TLA2_RESPONSE.md - TLA2 team's API specification
- vc_ir/src/temporal.rs - Current tRust temporal types
- rustc_vc/src/async_state_machine.rs - Current state machine extractor
- TLA2_FEATURE_REQUEST.md - Original tRust requirements
