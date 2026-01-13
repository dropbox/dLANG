//! Temporal Logic Operators
//!
//! Support for TLA+ style temporal properties for distributed systems
//! and concurrent code verification.

use crate::{Expr, Predicate};
use serde::{Deserialize, Serialize};
use std::fmt::Write;

/// A temporal logic formula
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TemporalFormula {
    /// State predicate (holds in current state)
    State(Predicate),

    /// Always (box): []P - P holds in all states
    Always(Box<TemporalFormula>),

    /// Eventually (diamond): <>P - P holds in some future state
    Eventually(Box<TemporalFormula>),

    /// Next: X P - P holds in the next state
    Next(Box<TemporalFormula>),

    /// Until: P U Q - P holds until Q becomes true
    Until(Box<TemporalFormula>, Box<TemporalFormula>),

    /// Weak until: P W Q - P holds until Q, or P holds forever
    WeakUntil(Box<TemporalFormula>, Box<TemporalFormula>),

    /// Release: P R Q - Q holds until P releases it (dual of until)
    Release(Box<TemporalFormula>, Box<TemporalFormula>),

    /// Leads to: P ~> Q - if P then eventually Q
    LeadsTo(Box<TemporalFormula>, Box<TemporalFormula>),

    /// Temporal negation
    Not(Box<TemporalFormula>),

    /// Temporal conjunction
    And(Vec<TemporalFormula>),

    /// Temporal disjunction
    Or(Vec<TemporalFormula>),

    /// Temporal implication
    Implies(Box<TemporalFormula>, Box<TemporalFormula>),

    /// Fairness: weak fairness (WF) - if continuously enabled, eventually taken
    WeakFairness {
        action: String,
        condition: Predicate,
    },

    /// Strong fairness (SF) - if infinitely often enabled, eventually taken
    StrongFairness {
        action: String,
        condition: Predicate,
    },

    /// Stuttering equivalence: allows stuttering steps
    StutteringEquiv(Box<TemporalFormula>),
}

impl TemporalFormula {
    // Convenience constructors

    #[must_use]
    pub const fn state(p: Predicate) -> Self {
        Self::State(p)
    }

    #[must_use]
    pub fn always(f: Self) -> Self {
        Self::Always(Box::new(f))
    }

    #[must_use]
    pub fn eventually(f: Self) -> Self {
        Self::Eventually(Box::new(f))
    }

    #[must_use]
    pub fn next(f: Self) -> Self {
        Self::Next(Box::new(f))
    }

    #[must_use]
    pub fn until(p: Self, q: Self) -> Self {
        Self::Until(Box::new(p), Box::new(q))
    }

    #[must_use]
    pub fn leads_to(p: Self, q: Self) -> Self {
        Self::LeadsTo(Box::new(p), Box::new(q))
    }

    /// []<>P - P holds infinitely often
    #[must_use]
    pub fn infinitely_often(p: Self) -> Self {
        Self::Always(Box::new(Self::Eventually(Box::new(p))))
    }

    /// <>[]P - P eventually holds forever
    #[must_use]
    pub fn eventually_always(p: Self) -> Self {
        Self::Eventually(Box::new(Self::Always(Box::new(p))))
    }
}

/// A distributed protocol specification (TLA+ style)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolSpec {
    /// Protocol name
    pub name: String,

    /// State variables
    pub variables: Vec<StateVariable>,

    /// Initial state predicate
    pub init: Predicate,

    /// Next-state relation (disjunction of actions)
    pub next: Vec<Action>,

    /// Safety properties (invariants)
    pub safety: Vec<TemporalFormula>,

    /// Liveness properties
    pub liveness: Vec<TemporalFormula>,

    /// Fairness conditions
    pub fairness: Vec<FairnessCondition>,
}

/// A state variable in a protocol
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateVariable {
    pub name: String,
    pub ty: crate::VcType,
    /// Optional type invariant
    pub type_invariant: Option<Predicate>,
}

/// An action in a protocol (corresponds to a state transition)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Action {
    pub name: String,
    /// Enabling condition
    pub enabled: Predicate,
    /// Effect: how variables change
    pub effect: Vec<(String, Expr)>,
}

/// Fairness condition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FairnessCondition {
    /// Weak fairness for an action
    Weak(String),
    /// Strong fairness for an action
    Strong(String),
}

/// Model checking configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelCheckConfig {
    /// Maximum trace length
    pub max_depth: usize,
    /// State space bound (for bounded model checking)
    pub state_bound: Option<usize>,
    /// Symmetry reduction
    pub symmetry: Vec<SymmetryGroup>,
    /// Number of workers for parallel exploration
    pub workers: usize,
}

/// Symmetry group for state space reduction
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymmetryGroup {
    pub name: String,
    pub elements: Vec<String>,
}

// ============================================
// Async State Machine Extraction (Phase 6.1)
// ============================================

/// An async state machine extracted from Rust async code.
///
/// Rust async functions are compiled to state machines by the compiler.
/// This type represents the logical state machine for verification purposes,
/// capturing the states (suspension points) and transitions between them.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AsyncStateMachine {
    /// Name of the async function
    pub name: String,
    /// States in the state machine (including Start and End)
    pub states: Vec<AsyncState>,
    /// Transitions between states
    pub transitions: Vec<AsyncTransition>,
    /// Initial state index (always 0, pointing to Start)
    pub initial: usize,
    /// Final state indices (states that return a value)
    pub finals: Vec<usize>,
    /// Yield points (.await expressions)
    pub yield_points: Vec<AsyncYieldPoint>,
    /// Local variables that persist across yield points
    pub captured_variables: Vec<CapturedVariable>,
}

/// A state in an async state machine.
///
/// States correspond to suspension points in the async function.
/// The compiler transforms async functions into generators where
/// each .await creates a new suspension point.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AsyncState {
    /// Unique state identifier
    pub id: usize,
    /// Human-readable name (e.g., "Start", "AfterFetch", "End")
    pub name: String,
    /// Kind of state
    pub kind: AsyncStateKind,
    /// Invariants that hold in this state
    pub invariants: Vec<Predicate>,
    /// Source location where this state originates
    pub source_span: Option<crate::SourceSpan>,
}

/// The kind of async state
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AsyncStateKind {
    /// Initial state before any execution
    Start,
    /// State after a yield/await point
    Suspended,
    /// State where execution can resume
    Resumable,
    /// Final state (function returned)
    End,
    /// Panicked state (unwinding)
    Panicked,
}

/// A transition between states in an async state machine.
///
/// Transitions represent the code executed between suspension points.
/// Each transition has a guard condition and an effect on captured state.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AsyncTransition {
    /// Source state index
    pub from: usize,
    /// Target state index
    pub to: usize,
    /// Guard condition (when can this transition fire)
    pub guard: Option<Predicate>,
    /// Effect of the transition (what changes)
    pub effect: Vec<StateUpdate>,
    /// Is this a poll/resume transition?
    pub is_poll: bool,
    /// Is this a yield/await transition?
    pub is_yield: bool,
    /// Source location of the transition
    pub source_span: Option<crate::SourceSpan>,
}

/// An update to a state variable during a transition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateUpdate {
    /// Variable being updated
    pub variable: String,
    /// New value expression
    pub value: Expr,
}

/// A yield point (`.await` expression) in async code.
///
/// Yield points are where the async function suspends and returns
/// control to the executor. The state of all captured variables
/// is preserved across the yield point.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AsyncYieldPoint {
    /// Index of this yield point
    pub index: usize,
    /// State before yielding
    pub pre_state: usize,
    /// State after resuming
    pub post_state: usize,
    /// The future being awaited (if identifiable)
    pub awaited_future: Option<String>,
    /// Type of the awaited future
    pub future_type: Option<String>,
    /// Source span of the .await expression
    pub source_span: Option<crate::SourceSpan>,
}

/// A variable captured across yield points.
///
/// When an async function yields, local variables that are used
/// after the yield point must be stored in the state machine's state.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CapturedVariable {
    /// Variable name
    pub name: String,
    /// Variable type
    pub ty: crate::VcType,
    /// Yield points where this variable is live
    pub live_across: Vec<usize>,
    /// Is this variable mutable?
    pub is_mutable: bool,
}

impl AsyncStateMachine {
    /// Create a new empty async state machine
    #[must_use]
    pub fn new(name: &str) -> Self {
        let start_state = AsyncState {
            id: 0,
            name: "Start".to_string(),
            kind: AsyncStateKind::Start,
            invariants: vec![],
            source_span: None,
        };
        Self {
            name: name.to_string(),
            states: vec![start_state],
            transitions: vec![],
            initial: 0,
            finals: vec![],
            yield_points: vec![],
            captured_variables: vec![],
        }
    }

    /// Add a new state and return its index
    pub fn add_state(&mut self, name: &str, kind: AsyncStateKind) -> usize {
        let id = self.states.len();
        self.states.push(AsyncState {
            id,
            name: name.to_string(),
            kind,
            invariants: vec![],
            source_span: None,
        });
        if kind == AsyncStateKind::End {
            self.finals.push(id);
        }
        id
    }

    /// Add a transition between states
    pub fn add_transition(&mut self, from: usize, to: usize) -> &mut AsyncTransition {
        let transition = AsyncTransition {
            from,
            to,
            guard: None,
            effect: vec![],
            is_poll: false,
            is_yield: false,
            source_span: None,
        };
        self.transitions.push(transition);
        self.transitions
            .last_mut()
            .expect("transitions cannot be empty after push")
    }

    /// Add a yield point (.await)
    pub fn add_yield_point(&mut self, pre_state: usize, post_state: usize) -> usize {
        let index = self.yield_points.len();
        self.yield_points.push(AsyncYieldPoint {
            index,
            pre_state,
            post_state,
            awaited_future: None,
            future_type: None,
            source_span: None,
        });
        index
    }

    /// Add a captured variable
    pub fn add_captured_variable(&mut self, name: &str, ty: crate::VcType, is_mutable: bool) {
        self.captured_variables.push(CapturedVariable {
            name: name.to_string(),
            ty,
            live_across: vec![],
            is_mutable,
        });
    }

    /// Get all states reachable from a given state
    #[must_use]
    pub fn reachable_from(&self, state: usize) -> Vec<usize> {
        let mut visited = vec![false; self.states.len()];
        let mut result = Vec::new();
        let mut stack = vec![state];

        while let Some(s) = stack.pop() {
            if visited[s] {
                continue;
            }
            visited[s] = true;
            result.push(s);

            for t in &self.transitions {
                if t.from == s && !visited[t.to] {
                    stack.push(t.to);
                }
            }
        }
        result
    }

    /// Check if all final states are reachable from the initial state
    #[must_use]
    pub fn can_terminate(&self) -> bool {
        let reachable = self.reachable_from(self.initial);
        self.finals.iter().any(|f| reachable.contains(f))
    }

    /// Find potential deadlock states (non-final states with no outgoing transitions)
    #[must_use]
    pub fn find_deadlocks(&self) -> Vec<usize> {
        let mut deadlocks = Vec::new();
        for state in &self.states {
            if state.kind != AsyncStateKind::End && state.kind != AsyncStateKind::Panicked {
                let has_outgoing = self.transitions.iter().any(|t| t.from == state.id);
                if !has_outgoing {
                    deadlocks.push(state.id);
                }
            }
        }
        deadlocks
    }

    /// Get the number of yield points (complexity metric)
    #[must_use]
    pub const fn yield_count(&self) -> usize {
        self.yield_points.len()
    }

    /// Check if the state machine is sequential (no branches)
    #[must_use]
    pub fn is_sequential(&self) -> bool {
        for state in &self.states {
            let outgoing: Vec<_> = self
                .transitions
                .iter()
                .filter(|t| t.from == state.id)
                .collect();
            if outgoing.len() > 1 {
                return false;
            }
        }
        true
    }
}

impl AsyncState {
    /// Create a new state with the given name and kind
    #[must_use]
    pub fn new(id: usize, name: &str, kind: AsyncStateKind) -> Self {
        Self {
            id,
            name: name.to_string(),
            kind,
            invariants: vec![],
            source_span: None,
        }
    }

    /// Add an invariant to this state
    #[must_use]
    pub fn with_invariant(mut self, inv: Predicate) -> Self {
        self.invariants.push(inv);
        self
    }

    /// Set the source span
    #[must_use]
    pub fn with_span(mut self, span: crate::SourceSpan) -> Self {
        self.source_span = Some(span);
        self
    }
}

impl AsyncTransition {
    /// Set the guard condition
    #[must_use]
    pub fn with_guard(mut self, guard: Predicate) -> Self {
        self.guard = Some(guard);
        self
    }

    /// Add a state update effect
    #[must_use]
    pub fn with_effect(mut self, variable: &str, value: Expr) -> Self {
        self.effect.push(StateUpdate {
            variable: variable.to_string(),
            value,
        });
        self
    }

    /// Mark as a yield transition
    #[must_use]
    pub const fn as_yield(mut self) -> Self {
        self.is_yield = true;
        self
    }

    /// Mark as a poll transition
    #[must_use]
    pub const fn as_poll(mut self) -> Self {
        self.is_poll = true;
        self
    }
}

// ============================================
// Deadlock Freedom Proofs (Phase 6.2)
// ============================================

/// Result of a deadlock freedom proof attempt.
///
/// A deadlock occurs when a system reaches a state where no progress is possible.
/// In an async state machine, this means a non-final state with no enabled transitions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DeadlockProofResult {
    /// Proven deadlock-free: no reachable state is a deadlock state
    Proven {
        /// SMT check result (typically "unsat" meaning no counterexample exists)
        smt_result: String,
        /// Time taken in milliseconds
        time_ms: u64,
    },
    /// Disproven: found a path to a deadlock state
    Disproven {
        /// The deadlock witness (path to deadlock)
        witness: DeadlockWitness,
    },
    /// Unknown: could not decide (timeout, resource limit, etc.)
    Unknown {
        /// Reason the proof could not be completed
        reason: String,
    },
}

/// A witness demonstrating a potential deadlock.
///
/// This is a counterexample showing how the system can reach a deadlock state.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadlockWitness {
    /// Name of the state machine with the deadlock
    pub state_machine: String,
    /// The deadlock state (index into state machine's states)
    pub deadlock_state: usize,
    /// Name of the deadlock state
    pub deadlock_state_name: String,
    /// Path from initial state to deadlock state (sequence of state indices)
    pub path: Vec<usize>,
    /// Transition labels along the path
    pub transition_labels: Vec<String>,
    /// Source span of the deadlock state (if available)
    pub source_span: Option<crate::SourceSpan>,
}

/// A proof obligation for deadlock freedom.
///
/// Contains the SMT-LIB encoding that, when checked for satisfiability,
/// determines if a deadlock is possible.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadlockProofObligation {
    /// Name of the state machine being checked
    pub state_machine: String,
    /// SMT-LIB declarations (constants, functions)
    pub declarations: Vec<String>,
    /// SMT-LIB assertions for the state machine structure
    pub structure_assertions: Vec<String>,
    /// The main deadlock formula (satisfiable iff deadlock is possible)
    pub deadlock_formula: String,
    /// Human-readable description
    pub description: String,
}

impl DeadlockProofObligation {
    /// Create a new empty obligation
    #[must_use]
    pub fn new(state_machine: &str) -> Self {
        Self {
            state_machine: state_machine.to_string(),
            declarations: Vec::new(),
            structure_assertions: Vec::new(),
            deadlock_formula: String::new(),
            description: format!("Deadlock freedom for {state_machine}"),
        }
    }

    /// Generate SMT-LIB script from this obligation
    #[must_use]
    pub fn to_smtlib(&self) -> String {
        let mut script = String::new();
        script.push_str("; Deadlock freedom proof obligation\n");
        let _ = writeln!(script, "; {}", self.description);
        script.push_str("(set-logic QF_LIA)\n\n");

        script.push_str("; Declarations\n");
        for decl in &self.declarations {
            script.push_str(decl);
            script.push('\n');
        }

        script.push_str("\n; Structure assertions\n");
        for assertion in &self.structure_assertions {
            let _ = writeln!(script, "(assert {assertion})");
        }

        script.push_str("\n; Deadlock formula (sat means deadlock is possible)\n");
        let _ = writeln!(script, "(assert {})", self.deadlock_formula);

        script.push_str("\n(check-sat)\n");
        script.push_str("(get-model)\n");

        script
    }

    /// Add a declaration
    pub fn add_declaration(&mut self, decl: &str) {
        self.declarations.push(decl.to_string());
    }

    /// Add a structure assertion
    pub fn add_structure_assertion(&mut self, assertion: &str) {
        self.structure_assertions.push(assertion.to_string());
    }

    /// Set the deadlock formula
    pub fn set_deadlock_formula(&mut self, formula: &str) {
        self.deadlock_formula = formula.to_string();
    }
}

impl DeadlockWitness {
    /// Create a witness from a state machine and deadlock state
    #[must_use]
    pub fn new(sm: &AsyncStateMachine, deadlock_state: usize) -> Self {
        let state_name = sm
            .states
            .get(deadlock_state)
            .map_or_else(|| format!("state_{deadlock_state}"), |s| s.name.clone());

        // Find a simple path to the deadlock state using BFS
        let path = Self::find_path_to(sm, deadlock_state);
        let transition_labels = Self::path_to_labels(sm, &path);

        Self {
            state_machine: sm.name.clone(),
            deadlock_state,
            deadlock_state_name: state_name,
            path,
            transition_labels,
            source_span: sm
                .states
                .get(deadlock_state)
                .and_then(|s| s.source_span.clone()),
        }
    }

    /// Find a path from initial state to target using BFS
    fn find_path_to(sm: &AsyncStateMachine, target: usize) -> Vec<usize> {
        use std::collections::VecDeque;

        let mut visited = vec![false; sm.states.len()];
        let mut parent = vec![None; sm.states.len()];
        let mut queue = VecDeque::new();

        queue.push_back(sm.initial);
        visited[sm.initial] = true;

        while let Some(current) = queue.pop_front() {
            if current == target {
                // Reconstruct path
                let mut path = Vec::new();
                let mut node = Some(target);
                while let Some(n) = node {
                    path.push(n);
                    node = parent[n];
                }
                path.reverse();
                return path;
            }

            for t in &sm.transitions {
                if t.from == current && !visited[t.to] {
                    visited[t.to] = true;
                    parent[t.to] = Some(current);
                    queue.push_back(t.to);
                }
            }
        }

        // No path found, return just the target
        vec![target]
    }

    /// Convert path to transition labels
    fn path_to_labels(sm: &AsyncStateMachine, path: &[usize]) -> Vec<String> {
        let mut labels = Vec::new();
        for window in path.windows(2) {
            let from = window[0];
            let to = window[1];

            // Find the transition
            if let Some(t) = sm.transitions.iter().find(|t| t.from == from && t.to == to) {
                let label = if t.is_yield {
                    format!("{from} --yield--> {to}")
                } else if t.is_poll {
                    format!("{from} --poll--> {to}")
                } else {
                    format!("{from} --> {to}")
                };
                labels.push(label);
            } else {
                labels.push(format!("{from} -> {to}"));
            }
        }
        labels
    }

    /// Format the witness as a human-readable string
    #[must_use]
    pub fn to_string_formatted(&self) -> String {
        let mut s = String::new();
        let _ = writeln!(
            s,
            "Deadlock found in state machine '{}'",
            self.state_machine
        );
        let _ = writeln!(
            s,
            "Deadlock state: {} ({})",
            self.deadlock_state, self.deadlock_state_name
        );

        if !self.path.is_empty() {
            s.push_str("Path to deadlock:\n");
            for (i, &state) in self.path.iter().enumerate() {
                if i < self.transition_labels.len() {
                    let _ = writeln!(s, "  [{}] {}", state, self.transition_labels[i]);
                } else {
                    let _ = writeln!(s, "  [{state}] (deadlock)");
                }
            }
        }

        s
    }
}

impl DeadlockProofResult {
    /// Check if the proof succeeded (system is deadlock-free)
    #[must_use]
    pub const fn is_proven(&self) -> bool {
        matches!(self, Self::Proven { .. })
    }

    /// Check if the proof found a deadlock
    #[must_use]
    pub const fn is_disproven(&self) -> bool {
        matches!(self, Self::Disproven { .. })
    }

    /// Check if the proof could not be completed
    #[must_use]
    pub const fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown { .. })
    }

    /// Get the witness if disproven
    #[must_use]
    pub const fn witness(&self) -> Option<&DeadlockWitness> {
        match self {
            Self::Disproven { witness } => Some(witness),
            _ => None,
        }
    }
}

/// Generate a deadlock freedom proof obligation from an async state machine.
///
/// The generated SMT formula is satisfiable iff there exists a reachable
/// deadlock state (a non-final state with no enabled outgoing transitions).
#[must_use]
pub fn generate_deadlock_obligation(sm: &AsyncStateMachine) -> DeadlockProofObligation {
    let mut obligation = DeadlockProofObligation::new(&sm.name);

    // Declare state variables (Bool for each state)
    for (i, state) in sm.states.iter().enumerate() {
        obligation.add_declaration(&format!(
            "(declare-const reachable_{} Bool) ; {}",
            i, state.name
        ));
        obligation.add_declaration(&format!(
            "(declare-const is_final_{} Bool) ; {} is final?",
            i, state.name
        ));
        obligation.add_declaration(&format!(
            "(declare-const has_outgoing_{} Bool) ; {} has outgoing transition?",
            i, state.name
        ));
    }

    // Initial state is reachable
    obligation.add_structure_assertion(&format!("reachable_{}", sm.initial));

    // Define is_final for each state
    for (i, state) in sm.states.iter().enumerate() {
        let is_final = state.kind == AsyncStateKind::End || state.kind == AsyncStateKind::Panicked;
        obligation.add_structure_assertion(&format!("(= is_final_{i} {is_final})"));
    }

    // Define has_outgoing for each state
    for (i, _state) in sm.states.iter().enumerate() {
        let has_outgoing = sm.transitions.iter().any(|t| t.from == i);
        obligation.add_structure_assertion(&format!("(= has_outgoing_{i} {has_outgoing})"));
    }

    // Reachability: if state i is reachable and there's a transition i->j, then j is reachable
    for t in &sm.transitions {
        obligation
            .add_structure_assertion(&format!("(=> reachable_{} reachable_{})", t.from, t.to));
    }

    // Deadlock formula: exists a reachable non-final state with no outgoing transitions
    // (or reachable_0 and not is_final_0 and not has_outgoing_0)
    // (or reachable_1 and not is_final_1 and not has_outgoing_1)
    // ...
    let deadlock_clauses: Vec<String> = sm
        .states
        .iter()
        .enumerate()
        .map(|(i, _)| format!("(and reachable_{i} (not is_final_{i}) (not has_outgoing_{i}))"))
        .collect();

    if deadlock_clauses.is_empty() {
        obligation.set_deadlock_formula("false");
    } else if deadlock_clauses.len() == 1 {
        obligation.set_deadlock_formula(&deadlock_clauses[0]);
    } else {
        obligation.set_deadlock_formula(&format!("(or {})", deadlock_clauses.join(" ")));
    }

    obligation.description = format!(
        "Deadlock freedom for '{}' ({} states, {} transitions)",
        sm.name,
        sm.states.len(),
        sm.transitions.len()
    );

    obligation
}

/// Quick syntactic check for deadlock freedom (without SMT).
///
/// Returns Some(witness) if a deadlock is found syntactically,
/// None if no deadlock detected (does NOT prove absence).
#[must_use]
pub fn check_deadlock_syntactic(sm: &AsyncStateMachine) -> Option<DeadlockWitness> {
    let deadlocks = sm.find_deadlocks();
    if deadlocks.is_empty() {
        return None;
    }

    // Return witness for first deadlock state that is reachable
    let reachable = sm.reachable_from(sm.initial);
    for &deadlock_state in &deadlocks {
        if reachable.contains(&deadlock_state) {
            return Some(DeadlockWitness::new(sm, deadlock_state));
        }
    }

    None
}

// ============================================
// Liveness Proof Types
// ============================================

/// Types of liveness properties that can be verified
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum LivenessProperty {
    /// Termination: eventually reaches a final state from any reachable state
    Termination,

    /// Response: if P holds, then Q eventually holds (P ~> Q)
    Response {
        /// The trigger predicate (P)
        trigger: String,
        /// The goal predicate (Q)
        goal: String,
    },

    /// Progress: from any state, can always make progress (no infinite stalls)
    Progress,

    /// Eventually reaches a specific named state
    Reachability {
        /// The target state to eventually reach
        target_state: String,
    },

    /// Fairness: enabled actions are eventually taken
    Fairness {
        /// The action that must eventually execute when enabled
        action: String,
    },

    /// Starvation freedom: all requests are eventually served
    StarvationFreedom,
}

impl LivenessProperty {
    /// Create a termination property
    #[must_use]
    pub const fn termination() -> Self {
        Self::Termination
    }

    /// Create a response property (P ~> Q)
    #[must_use]
    pub fn response(trigger: &str, goal: &str) -> Self {
        Self::Response {
            trigger: trigger.to_string(),
            goal: goal.to_string(),
        }
    }

    /// Create a progress property
    #[must_use]
    pub const fn progress() -> Self {
        Self::Progress
    }

    /// Create a reachability property
    #[must_use]
    pub fn reachability(target: &str) -> Self {
        Self::Reachability {
            target_state: target.to_string(),
        }
    }

    /// Create a fairness property
    #[must_use]
    pub fn fairness(action: &str) -> Self {
        Self::Fairness {
            action: action.to_string(),
        }
    }

    /// Create a starvation freedom property
    #[must_use]
    pub const fn starvation_freedom() -> Self {
        Self::StarvationFreedom
    }

    /// Get a short description of this property
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::Termination => "termination".to_string(),
            Self::Response { trigger, goal } => {
                format!("response: {trigger} ~> {goal}")
            }
            Self::Progress => "progress".to_string(),
            Self::Reachability { target_state } => {
                format!("reachability: <>{target_state}")
            }
            Self::Fairness { action } => {
                format!("fairness: WF({action})")
            }
            Self::StarvationFreedom => "starvation freedom".to_string(),
        }
    }
}

/// Result of a liveness proof attempt
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LivenessProofResult {
    /// The liveness property holds
    Proven {
        /// Which property was proven
        property: LivenessProperty,
        /// Human-readable explanation
        reason: String,
    },

    /// The liveness property does not hold
    Disproven {
        /// Which property was disproven
        property: LivenessProperty,
        /// Witness showing the violation
        witness: LivenessWitness,
    },

    /// Could not determine if the property holds
    Unknown {
        /// Which property was checked
        property: LivenessProperty,
        /// Why the result is unknown
        reason: String,
    },
}

impl LivenessProofResult {
    /// Check if the result is proven
    #[must_use]
    pub const fn is_proven(&self) -> bool {
        matches!(self, Self::Proven { .. })
    }

    /// Check if the result is disproven
    #[must_use]
    pub const fn is_disproven(&self) -> bool {
        matches!(self, Self::Disproven { .. })
    }

    /// Check if the result is unknown
    #[must_use]
    pub const fn is_unknown(&self) -> bool {
        matches!(self, Self::Unknown { .. })
    }

    /// Get the property that was checked
    #[must_use]
    pub const fn property(&self) -> &LivenessProperty {
        match self {
            Self::Proven { property, .. }
            | Self::Disproven { property, .. }
            | Self::Unknown { property, .. } => property,
        }
    }

    /// Get the witness if disproven
    #[must_use]
    pub const fn witness(&self) -> Option<&LivenessWitness> {
        match self {
            Self::Disproven { witness, .. } => Some(witness),
            _ => None,
        }
    }
}

/// Witness for a liveness violation
///
/// Shows an infinite execution path (represented as a lasso: stem + cycle)
/// that never satisfies the liveness property.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LivenessWitness {
    /// The property that was violated
    pub property: LivenessProperty,

    /// The stem: finite path from initial state to the cycle entry
    pub stem: Vec<usize>,

    /// The cycle: infinite loop that never satisfies the property
    pub cycle: Vec<usize>,

    /// Human-readable labels for the stem states
    pub stem_labels: Vec<String>,

    /// Human-readable labels for the cycle states
    pub cycle_labels: Vec<String>,

    /// Description of why this violates the property
    pub explanation: String,
}

impl LivenessWitness {
    /// Create a new liveness witness
    #[must_use]
    pub fn new(
        property: LivenessProperty,
        sm: &AsyncStateMachine,
        stem: Vec<usize>,
        cycle: Vec<usize>,
    ) -> Self {
        let stem_labels: Vec<String> = stem
            .iter()
            .map(|&s| {
                sm.states
                    .get(s)
                    .map_or_else(|| format!("state_{s}"), |st| st.name.clone())
            })
            .collect();

        let cycle_labels: Vec<String> = cycle
            .iter()
            .map(|&s| {
                sm.states
                    .get(s)
                    .map_or_else(|| format!("state_{s}"), |st| st.name.clone())
            })
            .collect();

        let explanation = Self::generate_explanation(&property, &stem_labels, &cycle_labels);

        Self {
            property,
            stem,
            cycle,
            stem_labels,
            cycle_labels,
            explanation,
        }
    }

    fn generate_explanation(
        property: &LivenessProperty,
        stem_labels: &[String],
        cycle_labels: &[String],
    ) -> String {
        let stem_str = stem_labels.join(" -> ");
        let cycle_str = cycle_labels.join(" -> ");

        match property {
            LivenessProperty::Termination => {
                format!(
                    "Termination violated: path {stem_str} enters cycle {cycle_str} without reaching final state"
                )
            }
            LivenessProperty::Response { trigger, goal } => {
                format!(
                    "Response violated: after {trigger}, path {stem_str} enters cycle {cycle_str} without {goal}"
                )
            }
            LivenessProperty::Progress => {
                format!("Progress violated: path {stem_str} enters infinite cycle {cycle_str}")
            }
            LivenessProperty::Reachability { target_state } => {
                format!(
                    "Reachability violated: path {stem_str} enters cycle {cycle_str} without reaching {target_state}"
                )
            }
            LivenessProperty::Fairness { action } => {
                format!(
                    "Fairness violated: {action} is enabled but never executed in cycle {cycle_str} (after {stem_str})"
                )
            }
            LivenessProperty::StarvationFreedom => {
                format!(
                    "Starvation: path {stem_str} enters cycle {cycle_str} with pending requests"
                )
            }
        }
    }

    /// Format the witness for display
    #[must_use]
    pub fn to_string_formatted(&self) -> String {
        let mut result = String::new();
        let _ = writeln!(
            result,
            "Liveness Violation: {}",
            self.property.description()
        );
        let _ = writeln!(result, "Stem: {}", self.stem_labels.join(" -> "));
        let _ = writeln!(
            result,
            "Cycle: {} -> (repeat)",
            self.cycle_labels.join(" -> ")
        );
        let _ = writeln!(result, "Explanation: {}", self.explanation);
        result
    }
}

/// SMT proof obligation for liveness properties
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LivenessProofObligation {
    /// Name of the state machine
    pub state_machine: String,

    /// The property being verified
    pub property: LivenessProperty,

    /// SMT-LIB declarations for state machine structure
    pub declarations: Vec<String>,

    /// SMT-LIB assertions for state machine structure
    pub structure_assertions: Vec<String>,

    /// SMT-LIB formula for the liveness property
    pub liveness_formula: String,

    /// Human-readable description
    pub description: String,
}

impl LivenessProofObligation {
    /// Create a new liveness proof obligation
    #[must_use]
    pub fn new(state_machine: &str, property: LivenessProperty) -> Self {
        Self {
            state_machine: state_machine.to_string(),
            property,
            declarations: Vec::new(),
            structure_assertions: Vec::new(),
            liveness_formula: String::new(),
            description: String::new(),
        }
    }

    /// Add a declaration
    pub fn add_declaration(&mut self, decl: &str) {
        self.declarations.push(decl.to_string());
    }

    /// Add a structure assertion
    pub fn add_structure_assertion(&mut self, assertion: &str) {
        self.structure_assertions.push(assertion.to_string());
    }

    /// Set the liveness formula
    pub fn set_liveness_formula(&mut self, formula: &str) {
        self.liveness_formula = formula.to_string();
    }

    /// Convert to SMT-LIB format
    #[must_use]
    pub fn to_smtlib(&self) -> String {
        let mut result = String::new();

        result.push_str("; Liveness proof obligation\n");
        let _ = writeln!(result, "; State machine: {}", self.state_machine);
        let _ = writeln!(result, "; Property: {}", self.property.description());
        result.push('\n');

        // Declarations
        for decl in &self.declarations {
            result.push_str(decl);
            result.push('\n');
        }
        result.push('\n');

        // Structure assertions
        for assertion in &self.structure_assertions {
            let _ = writeln!(result, "(assert {assertion})");
        }
        result.push('\n');

        // Liveness formula
        if !self.liveness_formula.is_empty() {
            result.push_str("; Liveness property (negated for refutation)\n");
            let _ = writeln!(result, "(assert (not {}))", self.liveness_formula);
            result.push('\n');
        }

        result.push_str("(check-sat)\n");
        result.push_str("(get-model)\n");

        result
    }
}

/// Generate SMT proof obligation for a liveness property
#[must_use]
pub fn generate_liveness_obligation(
    sm: &AsyncStateMachine,
    property: LivenessProperty,
) -> LivenessProofObligation {
    let mut obligation = LivenessProofObligation::new(&sm.name, property.clone());

    // Declare state reachability and cycle detection variables
    for (i, state) in sm.states.iter().enumerate() {
        // Reachability from initial
        obligation.add_declaration(&format!(
            "(declare-const reachable_{} Bool) ; {}",
            i, state.name
        ));
        // In cycle detection
        obligation.add_declaration(&format!(
            "(declare-const in_cycle_{} Bool) ; {} is in a cycle",
            i, state.name
        ));
        // Can reach final from this state
        obligation.add_declaration(&format!(
            "(declare-const can_reach_final_{} Bool) ; can reach final from {}",
            i, state.name
        ));
    }

    // Mark initial state as reachable
    obligation.add_structure_assertion(&format!("reachable_{}", sm.initial));

    // Define transition reachability
    for trans in &sm.transitions {
        obligation.add_structure_assertion(&format!(
            "(=> reachable_{} reachable_{})",
            trans.from, trans.to
        ));
    }

    // Define can_reach_final for final states
    for &final_state in &sm.finals {
        obligation.add_structure_assertion(&format!("can_reach_final_{final_state}"));
    }

    // Define can_reach_final through transitions
    for trans in &sm.transitions {
        obligation.add_structure_assertion(&format!(
            "(=> can_reach_final_{} can_reach_final_{})",
            trans.to, trans.from
        ));
    }

    // Generate property-specific formula
    let formula = match &property {
        LivenessProperty::Termination => {
            // Every reachable state can eventually reach a final state
            let state_formulas: Vec<String> = (0..sm.states.len())
                .map(|i| format!("(=> reachable_{i} can_reach_final_{i})"))
                .collect();
            format!("(and {})", state_formulas.join(" "))
        }
        LivenessProperty::Response { trigger, goal } => {
            // If trigger state reachable, goal state is eventually reachable
            let trigger_idx = sm
                .states
                .iter()
                .position(|s| s.name == *trigger)
                .unwrap_or(0);
            let goal_idx = sm.states.iter().position(|s| s.name == *goal).unwrap_or(0);
            format!("(=> reachable_{trigger_idx} can_reach_final_{goal_idx})")
        }
        LivenessProperty::Progress => {
            // No state in a cycle without outgoing transitions
            let state_formulas: Vec<String> = (0..sm.states.len())
                .map(|i| {
                    let has_outgoing = sm.transitions.iter().any(|t| t.from == i);
                    if has_outgoing {
                        "true".to_string()
                    } else {
                        format!("(not (and reachable_{i} in_cycle_{i}))")
                    }
                })
                .collect();
            format!("(and {})", state_formulas.join(" "))
        }
        LivenessProperty::Reachability { target_state } => {
            // Target state is reachable from initial
            let target_idx = sm
                .states
                .iter()
                .position(|s| s.name == *target_state)
                .unwrap_or(0);
            format!("reachable_{target_idx}")
        }
        LivenessProperty::Fairness { action } => {
            // Find the state with matching action name and assert it can make progress
            let action_state_idx = sm.states.iter().position(|s| s.name == *action);
            if let Some(idx) = action_state_idx {
                // Fairness: if the action state is reachable, it can reach a final state
                format!("(=> reachable_{idx} can_reach_final_{idx})")
            } else {
                // Action not found as a state, property vacuously holds
                "true".to_string()
            }
        }
        LivenessProperty::StarvationFreedom => {
            // All reachable states can make progress to final
            let state_formulas: Vec<String> = (0..sm.states.len())
                .map(|i| format!("(=> reachable_{i} can_reach_final_{i})"))
                .collect();
            format!("(and {})", state_formulas.join(" "))
        }
    };

    obligation.set_liveness_formula(&formula);
    obligation.description = format!(
        "Liveness ({}) for '{}' ({} states, {} transitions)",
        property.description(),
        sm.name,
        sm.states.len(),
        sm.transitions.len()
    );

    obligation
}

/// Quick syntactic check for liveness properties (without SMT).
///
/// Returns Some(witness) if a violation is found syntactically,
/// None if no violation detected (does NOT prove the property holds).
#[must_use]
pub fn check_liveness_syntactic(
    sm: &AsyncStateMachine,
    property: &LivenessProperty,
) -> Option<LivenessWitness> {
    match property {
        LivenessProperty::Termination => check_termination_syntactic(sm),
        LivenessProperty::Response { trigger, goal } => check_response_syntactic(sm, trigger, goal),
        LivenessProperty::Progress => check_progress_syntactic(sm),
        LivenessProperty::Reachability { target_state } => {
            check_reachability_syntactic(sm, target_state)
        }
        LivenessProperty::Fairness { .. } | LivenessProperty::StarvationFreedom => {
            // These require more complex analysis
            None
        }
    }
}

/// Check termination syntactically: find cycles that don't reach final states
fn check_termination_syntactic(sm: &AsyncStateMachine) -> Option<LivenessWitness> {
    // Find all cycles reachable from initial
    let reachable = sm.reachable_from(sm.initial);

    // Check if any reachable state is in a cycle that doesn't include a final state
    for &state in &reachable {
        if let Some((_stem, cycle)) = find_cycle_from(sm, state) {
            // Check if cycle includes a final state
            let cycle_has_final = cycle.iter().any(|&s| sm.finals.contains(&s));
            if !cycle_has_final {
                // Build stem from initial to the cycle entry
                let full_stem = build_path_from_initial(sm, state);
                return Some(LivenessWitness::new(
                    LivenessProperty::Termination,
                    sm,
                    full_stem,
                    cycle,
                ));
            }
        }
    }
    None
}

/// Check response property syntactically
fn check_response_syntactic(
    sm: &AsyncStateMachine,
    trigger: &str,
    goal: &str,
) -> Option<LivenessWitness> {
    // Find trigger and goal states
    let trigger_idx = sm.states.iter().position(|s| s.name == trigger)?;
    let goal_idx = sm.states.iter().position(|s| s.name == goal)?;

    // Check if trigger is reachable
    let reachable_from_initial = sm.reachable_from(sm.initial);
    if !reachable_from_initial.contains(&trigger_idx) {
        return None; // Trigger not reachable, property vacuously holds
    }

    // Check if goal is reachable from trigger
    let reachable_from_trigger = sm.reachable_from(trigger_idx);
    if reachable_from_trigger.contains(&goal_idx) {
        return None; // Goal is reachable from trigger
    }

    // Goal not reachable - find a cycle from trigger that doesn't reach goal
    if let Some((_stem, cycle)) = find_cycle_from(sm, trigger_idx) {
        let full_stem = build_path_from_initial(sm, trigger_idx);
        return Some(LivenessWitness::new(
            LivenessProperty::response(trigger, goal),
            sm,
            full_stem,
            cycle,
        ));
    }

    None
}

/// Check progress property syntactically
fn check_progress_syntactic(sm: &AsyncStateMachine) -> Option<LivenessWitness> {
    // Progress violated if there's a reachable state with no outgoing transitions
    // that is also not a final state (deadlock = no progress)
    let reachable = sm.reachable_from(sm.initial);

    for &state in &reachable {
        let has_outgoing = sm.transitions.iter().any(|t| t.from == state);
        let is_final = sm.finals.contains(&state);

        if !has_outgoing && !is_final {
            // Found a non-final state with no outgoing - deadlock
            let stem = build_path_from_initial(sm, state);
            return Some(LivenessWitness::new(
                LivenessProperty::Progress,
                sm,
                stem,
                vec![state], // Degenerate cycle: stuck at this state
            ));
        }
    }

    None
}

/// Check reachability property syntactically
fn check_reachability_syntactic(
    sm: &AsyncStateMachine,
    target_state: &str,
) -> Option<LivenessWitness> {
    // Find target state
    let target_idx = sm.states.iter().position(|s| s.name == target_state)?;

    // Check if target is reachable from initial
    let reachable = sm.reachable_from(sm.initial);
    if reachable.contains(&target_idx) {
        return None; // Target is reachable
    }

    // Target not reachable - find a cycle that shows we can't reach it
    // Find any reachable cycle
    for &state in &reachable {
        if let Some((_, cycle)) = find_cycle_from(sm, state) {
            let stem = build_path_from_initial(sm, state);
            return Some(LivenessWitness::new(
                LivenessProperty::reachability(target_state),
                sm,
                stem,
                cycle,
            ));
        }
    }

    // No cycle found but target unreachable - use empty cycle
    let stem: Vec<usize> = (0..=sm.initial).collect();
    Some(LivenessWitness::new(
        LivenessProperty::reachability(target_state),
        sm,
        stem,
        vec![],
    ))
}

/// Find a cycle reachable from a given state
fn find_cycle_from(sm: &AsyncStateMachine, start: usize) -> Option<(Vec<usize>, Vec<usize>)> {
    fn dfs(
        sm: &AsyncStateMachine,
        current: usize,
        visited: &mut std::collections::HashSet<usize>,
        path: &mut Vec<usize>,
        path_set: &mut std::collections::HashSet<usize>,
    ) -> Option<(Vec<usize>, Vec<usize>)> {
        if path_set.contains(&current) {
            // Found cycle - extract it
            let cycle_start = path
                .iter()
                .position(|&s| s == current)
                .expect("current must be in path since path_set contains it");
            let cycle = path[cycle_start..].to_vec();
            let stem = path[..cycle_start].to_vec();
            return Some((stem, cycle));
        }

        if visited.contains(&current) {
            return None;
        }

        visited.insert(current);
        path.push(current);
        path_set.insert(current);

        for trans in &sm.transitions {
            if trans.from == current {
                if let Some(result) = dfs(sm, trans.to, visited, path, path_set) {
                    return Some(result);
                }
            }
        }

        path.pop();
        path_set.remove(&current);
        None
    }

    let mut visited = std::collections::HashSet::new();
    let mut path = Vec::new();
    let mut path_set = std::collections::HashSet::new();

    dfs(sm, start, &mut visited, &mut path, &mut path_set)
}

/// Build a path from initial state to target state
fn build_path_from_initial(sm: &AsyncStateMachine, target: usize) -> Vec<usize> {
    if target == sm.initial {
        return vec![sm.initial];
    }

    // BFS to find shortest path
    let mut queue = std::collections::VecDeque::new();
    let mut parent = std::collections::HashMap::new();
    let mut visited = std::collections::HashSet::new();

    queue.push_back(sm.initial);
    visited.insert(sm.initial);

    while let Some(current) = queue.pop_front() {
        if current == target {
            // Reconstruct path
            let mut path = vec![target];
            let mut node = target;
            while let Some(&p) = parent.get(&node) {
                path.push(p);
                node = p;
            }
            path.reverse();
            return path;
        }

        for trans in &sm.transitions {
            if trans.from == current && !visited.contains(&trans.to) {
                visited.insert(trans.to);
                parent.insert(trans.to, current);
                queue.push_back(trans.to);
            }
        }
    }

    // No path found
    vec![sm.initial]
}

// ============================================
// Protocol Module Definitions (Phase 6.3)
// ============================================

/// A protocol module parsed from `#[protocol]` attributed Rust module.
///
/// Protocol modules allow defining distributed protocols in Rust syntax,
/// similar to TLA+ specifications. The module contains:
/// - State variable declarations
/// - Init predicate (initialization)
/// - Next-state actions (transitions)
/// - Safety properties (invariants)
/// - Liveness properties
/// - Fairness conditions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolModule {
    /// Module name (from `mod name {}`)
    pub name: String,

    /// Protocol definition extracted from the module
    pub protocol: ProtocolSpec,

    /// Source file path
    pub source_path: Option<String>,

    /// Source span of the module
    pub source_span: Option<crate::SourceSpan>,

    /// Parties/roles in a multi-party protocol
    pub parties: Vec<ProtocolParty>,

    /// Inter-party message types
    pub messages: Vec<ProtocolMessage>,

    /// Model checking configuration
    pub model_check_config: Option<ModelCheckConfig>,
}

impl ProtocolModule {
    /// Create a new protocol module
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            protocol: ProtocolSpec {
                name: String::new(),
                variables: Vec::new(),
                init: Predicate::Bool(true),
                next: Vec::new(),
                safety: Vec::new(),
                liveness: Vec::new(),
                fairness: Vec::new(),
            },
            source_path: None,
            source_span: None,
            parties: Vec::new(),
            messages: Vec::new(),
            model_check_config: None,
        }
    }

    /// Set the protocol name
    #[must_use]
    pub fn with_protocol_name(mut self, name: impl Into<String>) -> Self {
        self.protocol.name = name.into();
        self
    }

    /// Add a state variable
    pub fn add_variable(&mut self, var: StateVariable) {
        self.protocol.variables.push(var);
    }

    /// Set the init predicate
    pub fn set_init(&mut self, init: Predicate) {
        self.protocol.init = init;
    }

    /// Add an action (next-state transition)
    pub fn add_action(&mut self, action: Action) {
        self.protocol.next.push(action);
    }

    /// Add a safety property
    pub fn add_safety(&mut self, formula: TemporalFormula) {
        self.protocol.safety.push(formula);
    }

    /// Add a liveness property
    pub fn add_liveness(&mut self, formula: TemporalFormula) {
        self.protocol.liveness.push(formula);
    }

    /// Add a fairness condition
    pub fn add_fairness(&mut self, fairness: FairnessCondition) {
        self.protocol.fairness.push(fairness);
    }

    /// Add a party for multi-party protocols
    pub fn add_party(&mut self, party: ProtocolParty) {
        self.parties.push(party);
    }

    /// Add a message type
    pub fn add_message(&mut self, message: ProtocolMessage) {
        self.messages.push(message);
    }

    /// Check if this is a multi-party protocol
    #[must_use]
    pub const fn is_multi_party(&self) -> bool {
        self.parties.len() > 1
    }

    /// Get the number of state variables
    #[must_use]
    pub const fn variable_count(&self) -> usize {
        self.protocol.variables.len()
    }

    /// Get the number of actions
    #[must_use]
    pub const fn action_count(&self) -> usize {
        self.protocol.next.len()
    }

    /// Get the number of safety properties
    #[must_use]
    pub const fn safety_count(&self) -> usize {
        self.protocol.safety.len()
    }

    /// Get the number of liveness properties
    #[must_use]
    pub const fn liveness_count(&self) -> usize {
        self.protocol.liveness.len()
    }

    /// Validate the protocol module
    pub fn validate(&self) -> Result<(), ProtocolValidationError> {
        // Check name is not empty
        if self.name.is_empty() {
            return Err(ProtocolValidationError::EmptyName);
        }

        // Check for duplicate variable names
        let mut var_names = std::collections::HashSet::new();
        for var in &self.protocol.variables {
            if !var_names.insert(&var.name) {
                return Err(ProtocolValidationError::DuplicateVariable(var.name.clone()));
            }
        }

        // Check for duplicate action names
        let mut action_names = std::collections::HashSet::new();
        for action in &self.protocol.next {
            if !action_names.insert(&action.name) {
                return Err(ProtocolValidationError::DuplicateAction(
                    action.name.clone(),
                ));
            }
        }

        // Validate parties for multi-party protocols
        if self.is_multi_party() {
            let mut party_names = std::collections::HashSet::new();
            for party in &self.parties {
                if !party_names.insert(&party.name) {
                    return Err(ProtocolValidationError::DuplicateParty(party.name.clone()));
                }
            }

            // Check that messages reference valid parties
            for msg in &self.messages {
                if !party_names.contains(&msg.sender) {
                    return Err(ProtocolValidationError::UnknownParty(msg.sender.clone()));
                }
                if !party_names.contains(&msg.receiver) {
                    return Err(ProtocolValidationError::UnknownParty(msg.receiver.clone()));
                }
            }
        }

        Ok(())
    }

    /// Convert to a ProtocolSpec
    #[must_use]
    pub fn to_spec(&self) -> ProtocolSpec {
        self.protocol.clone()
    }
}

/// A party/role in a multi-party protocol
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolParty {
    /// Party name (e.g., "Client", "Server", "Leader")
    pub name: String,

    /// Local state variables for this party
    pub local_variables: Vec<StateVariable>,

    /// Actions this party can perform
    pub actions: Vec<String>,

    /// Properties specific to this party
    pub local_properties: Vec<TemporalFormula>,
}

impl ProtocolParty {
    /// Create a new party
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            local_variables: Vec::new(),
            actions: Vec::new(),
            local_properties: Vec::new(),
        }
    }

    /// Add a local variable
    pub fn add_variable(&mut self, var: StateVariable) {
        self.local_variables.push(var);
    }

    /// Add an action this party can perform
    pub fn add_action(&mut self, action: impl Into<String>) {
        self.actions.push(action.into());
    }

    /// Add a local property
    pub fn add_property(&mut self, formula: TemporalFormula) {
        self.local_properties.push(formula);
    }
}

/// A message type in a multi-party protocol
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolMessage {
    /// Message type name
    pub name: String,

    /// Sender party name
    pub sender: String,

    /// Receiver party name
    pub receiver: String,

    /// Message payload fields
    pub fields: Vec<(String, crate::VcType)>,

    /// Precondition for sending
    pub send_guard: Option<Predicate>,

    /// Effect on receiver's state
    pub receive_effect: Vec<(String, Expr)>,
}

impl ProtocolMessage {
    /// Create a new message type
    pub fn new(
        name: impl Into<String>,
        sender: impl Into<String>,
        receiver: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            sender: sender.into(),
            receiver: receiver.into(),
            fields: Vec::new(),
            send_guard: None,
            receive_effect: Vec::new(),
        }
    }

    /// Add a field to the message
    pub fn add_field(&mut self, name: impl Into<String>, ty: crate::VcType) {
        self.fields.push((name.into(), ty));
    }

    /// Set the send guard
    pub fn set_send_guard(&mut self, guard: Predicate) {
        self.send_guard = Some(guard);
    }
}

/// Validation errors for protocol modules
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProtocolValidationError {
    /// Protocol name is empty
    EmptyName,

    /// Duplicate state variable name
    DuplicateVariable(String),

    /// Duplicate action name
    DuplicateAction(String),

    /// Duplicate party name
    DuplicateParty(String),

    /// Unknown party referenced
    UnknownParty(String),

    /// Invalid init predicate
    InvalidInit(String),

    /// Invalid action definition
    InvalidAction(String),

    /// Invalid fairness condition
    InvalidFairness(String),
}

impl std::fmt::Display for ProtocolValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyName => write!(f, "protocol name is empty"),
            Self::DuplicateVariable(name) => {
                write!(f, "duplicate state variable: {name}")
            }
            Self::DuplicateAction(name) => {
                write!(f, "duplicate action: {name}")
            }
            Self::DuplicateParty(name) => {
                write!(f, "duplicate party: {name}")
            }
            Self::UnknownParty(name) => {
                write!(f, "unknown party: {name}")
            }
            Self::InvalidInit(msg) => {
                write!(f, "invalid init predicate: {msg}")
            }
            Self::InvalidAction(msg) => {
                write!(f, "invalid action: {msg}")
            }
            Self::InvalidFairness(msg) => {
                write!(f, "invalid fairness condition: {msg}")
            }
        }
    }
}

impl std::error::Error for ProtocolValidationError {}

/// Result of extracting a protocol from module attributes
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolExtractionResult {
    /// Extracted protocol module (if successful)
    pub module: Option<ProtocolModule>,

    /// Errors encountered during extraction
    pub errors: Vec<ProtocolExtractionError>,

    /// Warnings
    pub warnings: Vec<String>,
}

impl ProtocolExtractionResult {
    /// Create a successful result
    #[must_use]
    pub const fn success(module: ProtocolModule) -> Self {
        Self {
            module: Some(module),
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    /// Create a failed result
    #[must_use]
    pub const fn failure(errors: Vec<ProtocolExtractionError>) -> Self {
        Self {
            module: None,
            errors,
            warnings: Vec::new(),
        }
    }

    /// Check if extraction succeeded
    #[must_use]
    pub const fn is_success(&self) -> bool {
        self.module.is_some() && self.errors.is_empty()
    }

    /// Add a warning
    pub fn add_warning(&mut self, warning: impl Into<String>) {
        self.warnings.push(warning.into());
    }
}

/// Errors during protocol extraction
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolExtractionError {
    /// Error kind
    pub kind: ProtocolExtractionErrorKind,

    /// Error message
    pub message: String,

    /// Source span (if available)
    pub span: Option<crate::SourceSpan>,
}

/// Kinds of protocol extraction errors
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProtocolExtractionErrorKind {
    /// Module is not marked with `#[protocol]`
    NotAProtocol,

    /// Invalid `#[protocol]` attribute syntax
    InvalidAttribute,

    /// Missing required init function
    MissingInit,

    /// Missing required next-state actions
    MissingActions,

    /// Invalid state variable declaration
    InvalidVariable,

    /// Invalid action definition
    InvalidAction,

    /// Invalid safety property
    InvalidSafety,

    /// Invalid liveness property
    InvalidLiveness,

    /// Invalid party definition
    InvalidParty,

    /// Invalid message definition
    InvalidMessage,

    /// Parse error
    ParseError,
}

// ============================================
// Unit Tests for Protocol Module
// ============================================

#[cfg(test)]
mod protocol_module_tests {
    use super::*;

    #[test]
    fn test_new_protocol_module() {
        let module = ProtocolModule::new("test_protocol");
        assert_eq!(module.name, "test_protocol");
        assert!(module.protocol.variables.is_empty());
        assert!(module.protocol.next.is_empty());
        assert!(module.parties.is_empty());
    }

    #[test]
    fn test_add_variable() {
        let mut module = ProtocolModule::new("test");
        module.add_variable(StateVariable {
            name: "x".to_string(),
            ty: crate::VcType::Int {
                signed: true,
                bits: 32,
            },
            type_invariant: None,
        });
        assert_eq!(module.variable_count(), 1);
        assert_eq!(module.protocol.variables[0].name, "x");
    }

    #[test]
    fn test_add_action() {
        let mut module = ProtocolModule::new("test");
        module.add_action(Action {
            name: "increment".to_string(),
            enabled: Predicate::Bool(true),
            effect: vec![("x".to_string(), Expr::Var("x".to_string()))],
        });
        assert_eq!(module.action_count(), 1);
        assert_eq!(module.protocol.next[0].name, "increment");
    }

    #[test]
    fn test_add_safety() {
        let mut module = ProtocolModule::new("test");
        module.add_safety(TemporalFormula::always(TemporalFormula::State(
            Predicate::Bool(true),
        )));
        assert_eq!(module.safety_count(), 1);
    }

    #[test]
    fn test_add_liveness() {
        let mut module = ProtocolModule::new("test");
        module.add_liveness(TemporalFormula::eventually(TemporalFormula::State(
            Predicate::Bool(true),
        )));
        assert_eq!(module.liveness_count(), 1);
    }

    #[test]
    fn test_add_party() {
        let mut module = ProtocolModule::new("test");
        module.add_party(ProtocolParty::new("Client"));
        module.add_party(ProtocolParty::new("Server"));
        assert!(module.is_multi_party());
        assert_eq!(module.parties.len(), 2);
    }

    #[test]
    fn test_single_party_not_multi_party() {
        let mut module = ProtocolModule::new("test");
        module.add_party(ProtocolParty::new("Solo"));
        assert!(!module.is_multi_party());
    }

    #[test]
    fn test_add_message() {
        let mut module = ProtocolModule::new("test");
        module.add_party(ProtocolParty::new("Client"));
        module.add_party(ProtocolParty::new("Server"));
        module.add_message(ProtocolMessage::new("Request", "Client", "Server"));
        assert_eq!(module.messages.len(), 1);
    }

    #[test]
    fn test_validate_empty_name() {
        let module = ProtocolModule::new("");
        let result = module.validate();
        assert!(matches!(result, Err(ProtocolValidationError::EmptyName)));
    }

    #[test]
    fn test_validate_duplicate_variable() {
        let mut module = ProtocolModule::new("test");
        module.add_variable(StateVariable {
            name: "x".to_string(),
            ty: crate::VcType::Int {
                signed: true,
                bits: 32,
            },
            type_invariant: None,
        });
        module.add_variable(StateVariable {
            name: "x".to_string(),
            ty: crate::VcType::Int {
                signed: true,
                bits: 32,
            },
            type_invariant: None,
        });
        let result = module.validate();
        assert!(matches!(
            result,
            Err(ProtocolValidationError::DuplicateVariable(_))
        ));
    }

    #[test]
    fn test_validate_duplicate_action() {
        let mut module = ProtocolModule::new("test");
        module.add_action(Action {
            name: "act".to_string(),
            enabled: Predicate::Bool(true),
            effect: vec![],
        });
        module.add_action(Action {
            name: "act".to_string(),
            enabled: Predicate::Bool(true),
            effect: vec![],
        });
        let result = module.validate();
        assert!(matches!(
            result,
            Err(ProtocolValidationError::DuplicateAction(_))
        ));
    }

    #[test]
    fn test_validate_duplicate_party() {
        let mut module = ProtocolModule::new("test");
        module.add_party(ProtocolParty::new("Client"));
        module.add_party(ProtocolParty::new("Client"));
        let result = module.validate();
        assert!(matches!(
            result,
            Err(ProtocolValidationError::DuplicateParty(_))
        ));
    }

    #[test]
    fn test_validate_unknown_party_in_message() {
        let mut module = ProtocolModule::new("test");
        module.add_party(ProtocolParty::new("Client"));
        module.add_party(ProtocolParty::new("Server"));
        module.add_message(ProtocolMessage::new("Request", "Client", "Unknown"));
        let result = module.validate();
        assert!(matches!(
            result,
            Err(ProtocolValidationError::UnknownParty(_))
        ));
    }

    #[test]
    fn test_validate_success() {
        let mut module = ProtocolModule::new("test");
        module.add_variable(StateVariable {
            name: "x".to_string(),
            ty: crate::VcType::Int {
                signed: true,
                bits: 32,
            },
            type_invariant: None,
        });
        module.add_action(Action {
            name: "increment".to_string(),
            enabled: Predicate::Bool(true),
            effect: vec![],
        });
        assert!(module.validate().is_ok());
    }

    #[test]
    fn test_to_spec() {
        let mut module = ProtocolModule::new("test");
        module.add_variable(StateVariable {
            name: "x".to_string(),
            ty: crate::VcType::Int {
                signed: true,
                bits: 32,
            },
            type_invariant: None,
        });
        let spec = module.to_spec();
        assert_eq!(spec.variables.len(), 1);
    }

    #[test]
    fn test_protocol_party_new() {
        let party = ProtocolParty::new("Client");
        assert_eq!(party.name, "Client");
        assert!(party.local_variables.is_empty());
        assert!(party.actions.is_empty());
    }

    #[test]
    fn test_protocol_party_add_variable() {
        let mut party = ProtocolParty::new("Client");
        party.add_variable(StateVariable {
            name: "id".to_string(),
            ty: crate::VcType::Int {
                signed: true,
                bits: 32,
            },
            type_invariant: None,
        });
        assert_eq!(party.local_variables.len(), 1);
    }

    #[test]
    fn test_protocol_party_add_action() {
        let mut party = ProtocolParty::new("Client");
        party.add_action("send_request");
        assert_eq!(party.actions.len(), 1);
        assert_eq!(party.actions[0], "send_request");
    }

    #[test]
    fn test_protocol_message_new() {
        let msg = ProtocolMessage::new("Request", "Client", "Server");
        assert_eq!(msg.name, "Request");
        assert_eq!(msg.sender, "Client");
        assert_eq!(msg.receiver, "Server");
        assert!(msg.fields.is_empty());
    }

    #[test]
    fn test_protocol_message_add_field() {
        let mut msg = ProtocolMessage::new("Request", "Client", "Server");
        msg.add_field(
            "payload",
            crate::VcType::Int {
                signed: true,
                bits: 32,
            },
        );
        assert_eq!(msg.fields.len(), 1);
        assert_eq!(msg.fields[0].0, "payload");
    }

    #[test]
    fn test_protocol_message_set_guard() {
        let mut msg = ProtocolMessage::new("Request", "Client", "Server");
        msg.set_send_guard(Predicate::Bool(true));
        assert!(msg.send_guard.is_some());
    }

    #[test]
    fn test_extraction_result_success() {
        let module = ProtocolModule::new("test");
        let result = ProtocolExtractionResult::success(module);
        assert!(result.is_success());
        assert!(result.module.is_some());
    }

    #[test]
    fn test_extraction_result_failure() {
        let result = ProtocolExtractionResult::failure(vec![ProtocolExtractionError {
            kind: ProtocolExtractionErrorKind::MissingInit,
            message: "no init function".to_string(),
            span: None,
        }]);
        assert!(!result.is_success());
        assert!(result.module.is_none());
    }

    #[test]
    fn test_extraction_result_add_warning() {
        let module = ProtocolModule::new("test");
        let mut result = ProtocolExtractionResult::success(module);
        result.add_warning("no safety properties defined");
        assert_eq!(result.warnings.len(), 1);
    }

    #[test]
    fn test_validation_error_display() {
        let err = ProtocolValidationError::EmptyName;
        assert_eq!(err.to_string(), "protocol name is empty");

        let err = ProtocolValidationError::DuplicateVariable("x".to_string());
        assert_eq!(err.to_string(), "duplicate state variable: x");

        let err = ProtocolValidationError::UnknownParty("Unknown".to_string());
        assert_eq!(err.to_string(), "unknown party: Unknown");
    }

    #[test]
    fn test_with_protocol_name() {
        let module = ProtocolModule::new("mod_name").with_protocol_name("proto_name");
        assert_eq!(module.name, "mod_name");
        assert_eq!(module.protocol.name, "proto_name");
    }

    #[test]
    fn test_add_fairness() {
        let mut module = ProtocolModule::new("test");
        module.add_fairness(FairnessCondition::Weak("send".to_string()));
        module.add_fairness(FairnessCondition::Strong("receive".to_string()));
        assert_eq!(module.protocol.fairness.len(), 2);
    }

    #[test]
    fn test_set_init() {
        let mut module = ProtocolModule::new("test");
        // x == 0
        module.set_init(Predicate::Expr(Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        )));
        assert!(!matches!(module.protocol.init, Predicate::Bool(true)));
    }
}

// ============================================
// Unit Tests for Async State Machine
// ============================================

#[cfg(test)]
mod async_state_machine_tests {
    use super::*;

    #[test]
    fn test_new_state_machine() {
        let sm = AsyncStateMachine::new("test_async");
        assert_eq!(sm.name, "test_async");
        assert_eq!(sm.states.len(), 1);
        assert_eq!(sm.states[0].name, "Start");
        assert_eq!(sm.states[0].kind, AsyncStateKind::Start);
        assert_eq!(sm.initial, 0);
        assert!(sm.finals.is_empty());
    }

    #[test]
    fn test_add_state() {
        let mut sm = AsyncStateMachine::new("test");
        let suspended = sm.add_state("AfterAwait", AsyncStateKind::Suspended);
        assert_eq!(suspended, 1);
        let end = sm.add_state("End", AsyncStateKind::End);
        assert_eq!(end, 2);
        assert!(sm.finals.contains(&end));
        assert_eq!(sm.states.len(), 3);
    }

    #[test]
    fn test_add_transition() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::End);

        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);

        assert_eq!(sm.transitions.len(), 2);
        assert_eq!(sm.transitions[0].from, 0);
        assert_eq!(sm.transitions[0].to, s1);
        assert_eq!(sm.transitions[1].from, s1);
        assert_eq!(sm.transitions[1].to, s2);
    }

    #[test]
    fn test_add_yield_point() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("BeforeAwait", AsyncStateKind::Resumable);
        let s2 = sm.add_state("AfterAwait", AsyncStateKind::Suspended);

        let yp = sm.add_yield_point(s1, s2);
        assert_eq!(yp, 0);
        assert_eq!(sm.yield_points[0].pre_state, s1);
        assert_eq!(sm.yield_points[0].post_state, s2);
    }

    #[test]
    fn test_reachable_from() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        let s3 = sm.add_state("S3", AsyncStateKind::End);

        // Start -> S1 -> S2 -> S3
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);
        sm.add_transition(s2, s3);

        let reachable = sm.reachable_from(0);
        assert!(reachable.contains(&0));
        assert!(reachable.contains(&s1));
        assert!(reachable.contains(&s2));
        assert!(reachable.contains(&s3));
    }

    #[test]
    fn test_can_terminate_true() {
        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        assert!(sm.can_terminate());
    }

    #[test]
    fn test_can_terminate_false() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let _end = sm.add_state("End", AsyncStateKind::End);

        // Start -> S1, but S1 has no path to End
        sm.add_transition(0, s1);
        // Note: End is not reachable!

        assert!(!sm.can_terminate());
    }

    #[test]
    fn test_find_deadlocks() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);

        // Start -> S1, but S1 has no outgoing transitions
        sm.add_transition(0, s1);
        // S2 also has no outgoing transitions

        let deadlocks = sm.find_deadlocks();
        assert!(deadlocks.contains(&s1));
        assert!(deadlocks.contains(&s2));
    }

    #[test]
    fn test_no_deadlocks() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);

        sm.add_transition(0, s1);
        sm.add_transition(s1, end);

        let deadlocks = sm.find_deadlocks();
        assert!(deadlocks.is_empty());
    }

    #[test]
    fn test_yield_count() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        let s3 = sm.add_state("S3", AsyncStateKind::End);

        sm.add_yield_point(0, s1);
        sm.add_yield_point(s1, s2);
        sm.add_yield_point(s2, s3);

        assert_eq!(sm.yield_count(), 3);
    }

    #[test]
    fn test_is_sequential_true() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);

        sm.add_transition(0, s1);
        sm.add_transition(s1, end);

        assert!(sm.is_sequential());
    }

    #[test]
    fn test_is_sequential_false() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);

        // Branch: Start -> S1, Start -> S2
        sm.add_transition(0, s1);
        sm.add_transition(0, s2);
        sm.add_transition(s1, end);
        sm.add_transition(s2, end);

        assert!(!sm.is_sequential());
    }

    #[test]
    fn test_captured_variable() {
        let mut sm = AsyncStateMachine::new("test");
        sm.add_captured_variable(
            "x",
            crate::VcType::Int {
                signed: true,
                bits: 32,
            },
            false,
        );
        sm.add_captured_variable(
            "y",
            crate::VcType::Int {
                signed: true,
                bits: 32,
            },
            true,
        );

        assert_eq!(sm.captured_variables.len(), 2);
        assert_eq!(sm.captured_variables[0].name, "x");
        assert!(!sm.captured_variables[0].is_mutable);
        assert_eq!(sm.captured_variables[1].name, "y");
        assert!(sm.captured_variables[1].is_mutable);
    }

    #[test]
    fn test_async_state_kind_equality() {
        assert_eq!(AsyncStateKind::Start, AsyncStateKind::Start);
        assert_ne!(AsyncStateKind::Start, AsyncStateKind::End);
        assert_ne!(AsyncStateKind::Suspended, AsyncStateKind::Resumable);
    }

    #[test]
    fn test_complex_state_machine() {
        // Simulate: async fn fetch_data() { let x = fetch().await; process(x).await; }
        let mut sm = AsyncStateMachine::new("fetch_data");

        // States: Start -> BeforeFetch -> AfterFetch -> BeforeProcess -> AfterProcess -> End
        let before_fetch = sm.add_state("BeforeFetch", AsyncStateKind::Resumable);
        let after_fetch = sm.add_state("AfterFetch", AsyncStateKind::Suspended);
        let before_process = sm.add_state("BeforeProcess", AsyncStateKind::Resumable);
        let after_process = sm.add_state("AfterProcess", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);

        // Transitions
        sm.add_transition(0, before_fetch);
        {
            let t = sm.add_transition(before_fetch, after_fetch);
            t.is_yield = true;
        }
        sm.add_transition(after_fetch, before_process);
        {
            let t = sm.add_transition(before_process, after_process);
            t.is_yield = true;
        }
        sm.add_transition(after_process, end);

        // Yield points
        sm.add_yield_point(before_fetch, after_fetch);
        sm.add_yield_point(before_process, after_process);

        // Captured variable
        sm.add_captured_variable(
            "x",
            crate::VcType::Int {
                signed: true,
                bits: 32,
            },
            false,
        );

        assert_eq!(sm.states.len(), 6);
        assert_eq!(sm.transitions.len(), 5);
        assert_eq!(sm.yield_count(), 2);
        assert!(sm.can_terminate());
        assert!(sm.find_deadlocks().is_empty());
        assert!(sm.is_sequential());
    }
}

// ============================================
// Unit Tests for Deadlock Freedom Proofs
// ============================================

#[cfg(test)]
mod deadlock_proof_tests {
    use super::*;

    #[test]
    fn test_deadlock_proof_result_is_proven() {
        let result = DeadlockProofResult::Proven {
            smt_result: "unsat".to_string(),
            time_ms: 10,
        };
        assert!(result.is_proven());
        assert!(!result.is_disproven());
        assert!(!result.is_unknown());
    }

    #[test]
    fn test_deadlock_proof_result_is_disproven() {
        let witness = DeadlockWitness {
            state_machine: "test".to_string(),
            deadlock_state: 1,
            deadlock_state_name: "S1".to_string(),
            path: vec![0, 1],
            transition_labels: vec!["0 --> 1".to_string()],
            source_span: None,
        };
        let result = DeadlockProofResult::Disproven { witness };
        assert!(!result.is_proven());
        assert!(result.is_disproven());
        assert!(result.witness().is_some());
    }

    #[test]
    fn test_deadlock_proof_result_is_unknown() {
        let result = DeadlockProofResult::Unknown {
            reason: "timeout".to_string(),
        };
        assert!(!result.is_proven());
        assert!(result.is_unknown());
    }

    #[test]
    fn test_deadlock_witness_new() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        // S1 has no outgoing transitions - it's a deadlock

        let witness = DeadlockWitness::new(&sm, s1);
        assert_eq!(witness.state_machine, "test");
        assert_eq!(witness.deadlock_state, s1);
        assert_eq!(witness.deadlock_state_name, "S1");
        assert_eq!(witness.path, vec![0, s1]);
    }

    #[test]
    fn test_deadlock_witness_path_labels() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        {
            let t = sm.add_transition(s1, s2);
            t.is_yield = true;
        }
        // S2 has no outgoing transitions - deadlock

        let witness = DeadlockWitness::new(&sm, s2);
        assert_eq!(witness.path, vec![0, s1, s2]);
        assert_eq!(witness.transition_labels.len(), 2);
        assert!(witness.transition_labels[1].contains("yield"));
    }

    #[test]
    fn test_deadlock_witness_formatted_string() {
        let witness = DeadlockWitness {
            state_machine: "test_async".to_string(),
            deadlock_state: 2,
            deadlock_state_name: "AfterAwait".to_string(),
            path: vec![0, 1, 2],
            transition_labels: vec!["0 --> 1".to_string(), "1 --yield--> 2".to_string()],
            source_span: None,
        };

        let formatted = witness.to_string_formatted();
        assert!(formatted.contains("Deadlock found"));
        assert!(formatted.contains("test_async"));
        assert!(formatted.contains("AfterAwait"));
    }

    #[test]
    fn test_deadlock_obligation_new() {
        let obligation = DeadlockProofObligation::new("test_sm");
        assert_eq!(obligation.state_machine, "test_sm");
        assert!(obligation.declarations.is_empty());
        assert!(obligation.structure_assertions.is_empty());
        assert!(obligation.deadlock_formula.is_empty());
    }

    #[test]
    fn test_deadlock_obligation_add_declaration() {
        let mut obligation = DeadlockProofObligation::new("test");
        obligation.add_declaration("(declare-const x Bool)");
        assert_eq!(obligation.declarations.len(), 1);
        assert_eq!(obligation.declarations[0], "(declare-const x Bool)");
    }

    #[test]
    fn test_deadlock_obligation_add_structure_assertion() {
        let mut obligation = DeadlockProofObligation::new("test");
        obligation.add_structure_assertion("(= x true)");
        assert_eq!(obligation.structure_assertions.len(), 1);
    }

    #[test]
    fn test_deadlock_obligation_to_smtlib() {
        let mut obligation = DeadlockProofObligation::new("test");
        obligation.add_declaration("(declare-const reachable_0 Bool)");
        obligation.add_structure_assertion("reachable_0");
        obligation.set_deadlock_formula("(and reachable_0 (not is_final_0))");

        let smtlib = obligation.to_smtlib();
        assert!(smtlib.contains("(set-logic QF_LIA)"));
        assert!(smtlib.contains("(declare-const reachable_0 Bool)"));
        assert!(smtlib.contains("(assert reachable_0)"));
        assert!(smtlib.contains("(check-sat)"));
    }

    #[test]
    fn test_generate_deadlock_obligation_simple() {
        let mut sm = AsyncStateMachine::new("simple");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        let obligation = generate_deadlock_obligation(&sm);
        assert_eq!(obligation.state_machine, "simple");
        assert!(!obligation.declarations.is_empty());
        assert!(!obligation.structure_assertions.is_empty());
        assert!(!obligation.deadlock_formula.is_empty());
    }

    #[test]
    fn test_generate_deadlock_obligation_with_deadlock() {
        let mut sm = AsyncStateMachine::new("with_deadlock");
        let s1 = sm.add_state("Stuck", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        // s1 has no outgoing transitions - deadlock!

        let obligation = generate_deadlock_obligation(&sm);
        // The formula should be satisfiable (deadlock exists)
        assert!(obligation.deadlock_formula.contains("reachable_"));
        assert!(obligation.deadlock_formula.contains("is_final_"));
        assert!(obligation.deadlock_formula.contains("has_outgoing_"));
    }

    #[test]
    fn test_generate_deadlock_obligation_reachability() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::End);
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);

        let obligation = generate_deadlock_obligation(&sm);
        // Should have reachability implications
        let smtlib = obligation.to_smtlib();
        assert!(smtlib.contains("=> reachable_0 reachable_1"));
        assert!(smtlib.contains("=> reachable_1 reachable_2"));
    }

    #[test]
    fn test_check_deadlock_syntactic_no_deadlock() {
        let mut sm = AsyncStateMachine::new("safe");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        let witness = check_deadlock_syntactic(&sm);
        assert!(witness.is_none());
    }

    #[test]
    fn test_check_deadlock_syntactic_with_deadlock() {
        let mut sm = AsyncStateMachine::new("deadlock");
        let s1 = sm.add_state("Stuck", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        // No transition from s1 - deadlock

        let witness = check_deadlock_syntactic(&sm);
        assert!(witness.is_some());
        let w = witness.unwrap();
        assert_eq!(w.deadlock_state, s1);
    }

    #[test]
    fn test_check_deadlock_syntactic_unreachable() {
        let mut sm = AsyncStateMachine::new("test");
        let end = sm.add_state("End", AsyncStateKind::End);
        let unreachable = sm.add_state("Unreachable", AsyncStateKind::Suspended);
        sm.add_transition(0, end);
        // 'unreachable' is a deadlock state but not reachable from start

        let witness = check_deadlock_syntactic(&sm);
        assert!(witness.is_none()); // Not a real deadlock since unreachable
        let _ = unreachable;
    }

    #[test]
    fn test_deadlock_obligation_empty_states() {
        // Edge case: state machine with only Start state
        let sm = AsyncStateMachine::new("empty");
        let obligation = generate_deadlock_obligation(&sm);
        // Should still generate valid SMT
        assert!(!obligation.declarations.is_empty());
    }

    #[test]
    fn test_deadlock_witness_find_path() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        let s3 = sm.add_state("S3", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);
        sm.add_transition(s2, s3);
        // s3 is a deadlock

        let path = DeadlockWitness::find_path_to(&sm, s3);
        assert_eq!(path, vec![0, s1, s2, s3]);
    }

    #[test]
    fn test_deadlock_witness_no_path() {
        let mut sm = AsyncStateMachine::new("test");
        let _end = sm.add_state("End", AsyncStateKind::End);
        let isolated = sm.add_state("Isolated", AsyncStateKind::Suspended);
        // isolated is not reachable from start

        let path = DeadlockWitness::find_path_to(&sm, isolated);
        // Should return just the target when no path exists
        assert_eq!(path, vec![isolated]);
    }
}

// ============================================
// Unit Tests for Liveness Proofs
// ============================================

#[cfg(test)]
mod liveness_proof_tests {
    use super::*;

    #[test]
    fn test_liveness_property_termination() {
        let prop = LivenessProperty::termination();
        assert_eq!(prop, LivenessProperty::Termination);
        assert_eq!(prop.description(), "termination");
    }

    #[test]
    fn test_liveness_property_response() {
        let prop = LivenessProperty::response("Request", "Response");
        match &prop {
            LivenessProperty::Response { trigger, goal } => {
                assert_eq!(trigger, "Request");
                assert_eq!(goal, "Response");
            }
            _ => panic!("Expected Response property"),
        }
        assert!(prop.description().contains("Request ~> Response"));
    }

    #[test]
    fn test_liveness_property_progress() {
        let prop = LivenessProperty::progress();
        assert_eq!(prop, LivenessProperty::Progress);
        assert_eq!(prop.description(), "progress");
    }

    #[test]
    fn test_liveness_property_reachability() {
        let prop = LivenessProperty::reachability("Done");
        match &prop {
            LivenessProperty::Reachability { target_state } => {
                assert_eq!(target_state, "Done");
            }
            _ => panic!("Expected Reachability property"),
        }
        assert!(prop.description().contains("<>Done"));
    }

    #[test]
    fn test_liveness_property_fairness() {
        let prop = LivenessProperty::fairness("process");
        match &prop {
            LivenessProperty::Fairness { action } => {
                assert_eq!(action, "process");
            }
            _ => panic!("Expected Fairness property"),
        }
        assert!(prop.description().contains("WF(process)"));
    }

    #[test]
    fn test_liveness_property_starvation_freedom() {
        let prop = LivenessProperty::starvation_freedom();
        assert_eq!(prop, LivenessProperty::StarvationFreedom);
        assert_eq!(prop.description(), "starvation freedom");
    }

    #[test]
    fn test_liveness_result_is_proven() {
        let result = LivenessProofResult::Proven {
            property: LivenessProperty::Termination,
            reason: "All paths lead to final".to_string(),
        };
        assert!(result.is_proven());
        assert!(!result.is_disproven());
        assert!(!result.is_unknown());
        assert_eq!(*result.property(), LivenessProperty::Termination);
    }

    #[test]
    fn test_liveness_result_is_disproven() {
        let witness = LivenessWitness {
            property: LivenessProperty::Termination,
            stem: vec![0, 1],
            cycle: vec![1, 2, 1],
            stem_labels: vec!["Start".to_string(), "S1".to_string()],
            cycle_labels: vec!["S1".to_string(), "S2".to_string(), "S1".to_string()],
            explanation: "Infinite loop".to_string(),
        };
        let result = LivenessProofResult::Disproven {
            property: LivenessProperty::Termination,
            witness: witness.clone(),
        };
        assert!(!result.is_proven());
        assert!(result.is_disproven());
        assert!(result.witness().is_some());
    }

    #[test]
    fn test_liveness_result_is_unknown() {
        let result = LivenessProofResult::Unknown {
            property: LivenessProperty::Termination,
            reason: "SMT timeout".to_string(),
        };
        assert!(!result.is_proven());
        assert!(!result.is_disproven());
        assert!(result.is_unknown());
        assert!(result.witness().is_none());
    }

    #[test]
    fn test_liveness_witness_new() {
        let mut sm = AsyncStateMachine::new("test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);
        sm.add_transition(s2, s1); // cycle

        let witness =
            LivenessWitness::new(LivenessProperty::Termination, &sm, vec![0], vec![s1, s2]);
        assert_eq!(witness.property, LivenessProperty::Termination);
        assert_eq!(witness.stem, vec![0]);
        assert_eq!(witness.cycle, vec![s1, s2]);
        assert_eq!(witness.stem_labels, vec!["Start"]);
        assert_eq!(witness.cycle_labels, vec!["S1", "S2"]);
    }

    #[test]
    fn test_liveness_witness_formatted_string() {
        let witness = LivenessWitness {
            property: LivenessProperty::Termination,
            stem: vec![0, 1],
            cycle: vec![1, 2],
            stem_labels: vec!["Start".to_string(), "Wait".to_string()],
            cycle_labels: vec!["Wait".to_string(), "Loop".to_string()],
            explanation: "Never terminates".to_string(),
        };
        let formatted = witness.to_string_formatted();
        assert!(formatted.contains("Liveness Violation"));
        assert!(formatted.contains("termination"));
        assert!(formatted.contains("Stem:"));
        assert!(formatted.contains("Cycle:"));
    }

    #[test]
    fn test_liveness_obligation_new() {
        let obligation = LivenessProofObligation::new("test", LivenessProperty::Termination);
        assert_eq!(obligation.state_machine, "test");
        assert_eq!(obligation.property, LivenessProperty::Termination);
        assert!(obligation.declarations.is_empty());
        assert!(obligation.structure_assertions.is_empty());
    }

    #[test]
    fn test_liveness_obligation_add_declaration() {
        let mut obligation = LivenessProofObligation::new("test", LivenessProperty::Progress);
        obligation.add_declaration("(declare-const x Bool)");
        assert_eq!(obligation.declarations.len(), 1);
    }

    #[test]
    fn test_liveness_obligation_add_structure_assertion() {
        let mut obligation = LivenessProofObligation::new("test", LivenessProperty::Progress);
        obligation.add_structure_assertion("(= x true)");
        assert_eq!(obligation.structure_assertions.len(), 1);
    }

    #[test]
    fn test_liveness_obligation_to_smtlib() {
        let mut obligation = LivenessProofObligation::new("test", LivenessProperty::Termination);
        obligation.add_declaration("(declare-const reachable_0 Bool)");
        obligation.add_structure_assertion("reachable_0");
        obligation.set_liveness_formula("(=> reachable_0 can_reach_final_0)");

        let smtlib = obligation.to_smtlib();
        assert!(smtlib.contains("; Liveness proof obligation"));
        assert!(smtlib.contains("(declare-const reachable_0 Bool)"));
        assert!(smtlib.contains("(assert reachable_0)"));
        assert!(smtlib.contains("(assert (not"));
        assert!(smtlib.contains("(check-sat)"));
    }

    #[test]
    fn test_generate_liveness_obligation_termination() {
        let mut sm = AsyncStateMachine::new("term_test");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, s1);
        sm.add_transition(s1, end);
        sm.finals.push(end);

        let obligation = generate_liveness_obligation(&sm, LivenessProperty::Termination);
        assert_eq!(obligation.state_machine, "term_test");
        assert!(!obligation.declarations.is_empty());
        assert!(!obligation.liveness_formula.is_empty());
        assert!(obligation.liveness_formula.contains("can_reach_final"));
    }

    #[test]
    fn test_generate_liveness_obligation_response() {
        let mut sm = AsyncStateMachine::new("resp_test");
        let req = sm.add_state("Request", AsyncStateKind::Suspended);
        let resp = sm.add_state("Response", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, req);
        sm.add_transition(req, resp);
        sm.add_transition(resp, end);

        let prop = LivenessProperty::response("Request", "Response");
        let obligation = generate_liveness_obligation(&sm, prop);
        assert!(obligation.description.contains("response"));
    }

    #[test]
    fn test_generate_liveness_obligation_reachability() {
        let mut sm = AsyncStateMachine::new("reach_test");
        let target = sm.add_state("Target", AsyncStateKind::Suspended);
        sm.add_transition(0, target);

        let prop = LivenessProperty::reachability("Target");
        let obligation = generate_liveness_obligation(&sm, prop);
        assert!(obligation.liveness_formula.contains("reachable_"));
    }

    #[test]
    fn test_check_liveness_syntactic_termination_passes() {
        let mut sm = AsyncStateMachine::new("terminates");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, s1);
        sm.add_transition(s1, end);
        sm.finals.push(end);

        let result = check_liveness_syntactic(&sm, &LivenessProperty::Termination);
        assert!(result.is_none()); // No violation found
    }

    #[test]
    fn test_check_liveness_syntactic_termination_fails() {
        let mut sm = AsyncStateMachine::new("loops");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);
        sm.add_transition(s2, s1); // Infinite cycle

        let result = check_liveness_syntactic(&sm, &LivenessProperty::Termination);
        assert!(result.is_some()); // Violation found
        let witness = result.unwrap();
        assert_eq!(witness.property, LivenessProperty::Termination);
    }

    #[test]
    fn test_check_liveness_syntactic_progress_passes() {
        let mut sm = AsyncStateMachine::new("progresses");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, s1);
        sm.add_transition(s1, end);
        sm.finals.push(end);

        let result = check_liveness_syntactic(&sm, &LivenessProperty::Progress);
        assert!(result.is_none());
    }

    #[test]
    fn test_check_liveness_syntactic_progress_fails() {
        let mut sm = AsyncStateMachine::new("stalls");
        let s1 = sm.add_state("Stuck", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        // s1 has no outgoing transitions - no progress

        let result = check_liveness_syntactic(&sm, &LivenessProperty::Progress);
        assert!(result.is_some());
    }

    #[test]
    fn test_check_liveness_syntactic_reachability_passes() {
        let mut sm = AsyncStateMachine::new("reachable");
        let target = sm.add_state("Target", AsyncStateKind::Suspended);
        sm.add_transition(0, target);

        let prop = LivenessProperty::reachability("Target");
        let result = check_liveness_syntactic(&sm, &prop);
        assert!(result.is_none()); // Target is reachable
    }

    #[test]
    fn test_check_liveness_syntactic_reachability_fails() {
        let mut sm = AsyncStateMachine::new("unreachable");
        let _target = sm.add_state("Target", AsyncStateKind::Suspended);
        // No transition to Target

        let prop = LivenessProperty::reachability("Target");
        let result = check_liveness_syntactic(&sm, &prop);
        assert!(result.is_some()); // Target is not reachable
    }

    #[test]
    fn test_check_liveness_syntactic_response_passes() {
        let mut sm = AsyncStateMachine::new("responds");
        let req = sm.add_state("Request", AsyncStateKind::Suspended);
        let resp = sm.add_state("Response", AsyncStateKind::Suspended);
        sm.add_transition(0, req);
        sm.add_transition(req, resp);

        let prop = LivenessProperty::response("Request", "Response");
        let result = check_liveness_syntactic(&sm, &prop);
        assert!(result.is_none()); // Response is reachable from Request
    }

    #[test]
    fn test_check_liveness_syntactic_response_fails() {
        let mut sm = AsyncStateMachine::new("no_response");
        let req = sm.add_state("Request", AsyncStateKind::Suspended);
        let _resp = sm.add_state("Response", AsyncStateKind::Suspended);
        let other = sm.add_state("Other", AsyncStateKind::Suspended);
        sm.add_transition(0, req);
        sm.add_transition(req, other);
        sm.add_transition(other, req); // Cycle without reaching Response

        let prop = LivenessProperty::response("Request", "Response");
        let result = check_liveness_syntactic(&sm, &prop);
        assert!(result.is_some()); // Response not reachable from Request
    }

    #[test]
    fn test_find_cycle_from() {
        let mut sm = AsyncStateMachine::new("cycle");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);
        sm.add_transition(s2, s1); // Cycle: s1 -> s2 -> s1

        let result = find_cycle_from(&sm, 0);
        assert!(result.is_some());
        let (stem, cycle) = result.unwrap();
        assert!(!cycle.is_empty());
        // Verify it's actually a cycle
        assert!(cycle.len() >= 2 || (cycle.len() == 1 && stem.is_empty()));
    }

    #[test]
    fn test_find_cycle_from_no_cycle() {
        let mut sm = AsyncStateMachine::new("acyclic");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, s1);
        sm.add_transition(s1, end);

        let result = find_cycle_from(&sm, 0);
        assert!(result.is_none());
    }

    #[test]
    fn test_build_path_from_initial() {
        let mut sm = AsyncStateMachine::new("path");
        let s1 = sm.add_state("S1", AsyncStateKind::Suspended);
        let s2 = sm.add_state("S2", AsyncStateKind::Suspended);
        let s3 = sm.add_state("S3", AsyncStateKind::Suspended);
        sm.add_transition(0, s1);
        sm.add_transition(s1, s2);
        sm.add_transition(s2, s3);

        let path = build_path_from_initial(&sm, s3);
        assert_eq!(path, vec![0, s1, s2, s3]);
    }

    #[test]
    fn test_build_path_from_initial_to_self() {
        let sm = AsyncStateMachine::new("self");
        let path = build_path_from_initial(&sm, 0);
        assert_eq!(path, vec![0]);
    }

    #[test]
    fn test_liveness_witness_explanation_generation() {
        let witness = LivenessWitness {
            property: LivenessProperty::Response {
                trigger: "Req".to_string(),
                goal: "Resp".to_string(),
            },
            stem: vec![0, 1],
            cycle: vec![1, 2],
            stem_labels: vec!["Start".to_string(), "Req".to_string()],
            cycle_labels: vec!["Req".to_string(), "Loop".to_string()],
            explanation: "Response violated: after Req, path Start -> Req enters cycle Req -> Loop without Resp".to_string(),
        };
        assert!(witness.explanation.contains("Response violated"));
        assert!(witness.explanation.contains("Req"));
    }
}
