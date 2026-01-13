//! TLA Extract Integration Test - Wire AsyncStateMachineExtractor to TLA2Model
//!
//! This test demonstrates the complete pipeline for extracting state machines
//! from async Rust code and converting to TLA2 format:
//!
//! ```text
//! AsyncFunctionInfo -> AsyncStateMachineExtractor -> AsyncStateMachine
//!                                                         |
//!                                                         v
//!                                              convert_to_tla2()
//!                                                         |
//!                                                         v
//!                                                    TLA2Model -> JSON
//! ```
//!
//! Expected: PASS (all extractions and conversions succeed)

use std::collections::HashMap;

// ============================================
// Type Definitions (mirrors rustc_vc types)
// ============================================

/// Source span for diagnostics
#[derive(Debug, Clone)]
pub struct SourceSpan {
    pub file: String,
    pub line_start: u32,
    pub line_end: u32,
    pub col_start: u32,
    pub col_end: u32,
}

/// Verification condition type (simplified)
#[derive(Debug, Clone)]
pub enum VcType {
    Bool,
    Int { signed: bool, bits: u32 },
    Abstract(String),
}

/// State kind in async state machines
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncStateKind {
    Start,
    Resumable,
    Suspended,
    End,
}

/// Async state machine state
#[derive(Debug, Clone)]
pub struct AsyncState {
    pub id: usize,
    pub name: String,
    pub kind: AsyncStateKind,
}

/// Captured variable across yield points
#[derive(Debug, Clone)]
pub struct CapturedVariable {
    pub name: String,
    pub ty: VcType,
    pub live_across: Vec<usize>,
    pub is_mutable: bool,
}

/// Transition effect
#[derive(Debug, Clone)]
pub struct TransitionEffect {
    pub variable: String,
    pub value: Expr,
}

/// Expression in transitions
#[derive(Debug, Clone)]
pub enum Expr {
    Var(String),
    IntLit(i128),
    BoolLit(bool),
    Add(Box<Expr>, Box<Expr>),
}

/// Predicate for guards
#[derive(Debug, Clone)]
pub enum Predicate {
    Bool(bool),
    Expr(Expr),
}

/// Async transition
#[derive(Debug, Clone)]
pub struct AsyncTransition {
    pub id: usize,
    pub from: usize,
    pub to: usize,
    pub is_yield: bool,
    pub is_poll: bool,
    pub guard: Option<Predicate>,
    pub effect: Vec<TransitionEffect>,
}

/// Yield point information
#[derive(Debug, Clone)]
pub struct YieldPoint {
    pub pre_state: usize,
    pub post_state: usize,
    pub awaited_future: Option<String>,
    pub future_type: Option<String>,
    pub source_span: Option<SourceSpan>,
}

/// Async state machine extracted from MIR
#[derive(Debug, Clone)]
pub struct AsyncStateMachine {
    pub name: String,
    pub states: Vec<AsyncState>,
    pub transitions: Vec<AsyncTransition>,
    pub yield_points: Vec<YieldPoint>,
    pub captured_variables: Vec<CapturedVariable>,
    pub initial: usize,
}

impl AsyncStateMachine {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            states: vec![AsyncState {
                id: 0,
                name: "Start".to_string(),
                kind: AsyncStateKind::Start,
            }],
            transitions: Vec::new(),
            yield_points: Vec::new(),
            captured_variables: Vec::new(),
            initial: 0,
        }
    }

    pub fn add_state(&mut self, name: &str, kind: AsyncStateKind) -> usize {
        let id = self.states.len();
        self.states.push(AsyncState {
            id,
            name: name.to_string(),
            kind,
        });
        id
    }

    pub fn add_transition(&mut self, from: usize, to: usize) -> &mut AsyncTransition {
        let id = self.transitions.len();
        self.transitions.push(AsyncTransition {
            id,
            from,
            to,
            is_yield: false,
            is_poll: false,
            guard: None,
            effect: Vec::new(),
        });
        self.transitions.last_mut().unwrap()
    }

    pub fn add_yield_point(&mut self, pre: usize, post: usize) -> usize {
        let id = self.yield_points.len();
        self.yield_points.push(YieldPoint {
            pre_state: pre,
            post_state: post,
            awaited_future: None,
            future_type: None,
            source_span: None,
        });
        id
    }

    pub fn yield_count(&self) -> usize {
        self.yield_points.len()
    }

    /// Check if the state machine can terminate (reach End state)
    pub fn can_terminate(&self) -> bool {
        let end_states: Vec<usize> = self
            .states
            .iter()
            .filter(|s| s.kind == AsyncStateKind::End)
            .map(|s| s.id)
            .collect();

        if end_states.is_empty() {
            return false;
        }

        // BFS from initial state
        let mut visited = vec![false; self.states.len()];
        let mut queue = vec![self.initial];
        visited[self.initial] = true;

        while let Some(state) = queue.pop() {
            if end_states.contains(&state) {
                return true;
            }
            for trans in &self.transitions {
                if trans.from == state && !visited[trans.to] {
                    visited[trans.to] = true;
                    queue.push(trans.to);
                }
            }
        }

        false
    }

    /// Check if state machine is sequential (no branching)
    pub fn is_sequential(&self) -> bool {
        for state in &self.states {
            let outgoing = self.transitions.iter().filter(|t| t.from == state.id).count();
            if outgoing > 1 {
                return false;
            }
        }
        true
    }

    /// Find potential deadlock states (non-end states with no outgoing transitions)
    pub fn find_deadlocks(&self) -> Vec<usize> {
        self.states
            .iter()
            .filter(|s| {
                s.kind != AsyncStateKind::End
                    && !self.transitions.iter().any(|t| t.from == s.id)
            })
            .map(|s| s.id)
            .collect()
    }
}

// ============================================
// AsyncStateMachineExtractor (mirrors rustc_vc)
// ============================================

/// Block terminator kinds (from MIR)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockTerminator {
    Goto,
    SwitchInt,
    Return,
    Yield,
    Call,
    Drop,
    Unreachable,
    Resume,
    Abort,
}

/// Yield point info from MIR analysis
#[derive(Debug, Clone)]
pub struct YieldPointInfo {
    pub index: usize,
    pub block: usize,
    pub awaited_expr: Option<String>,
    pub future_type: Option<String>,
    pub live_variables: Vec<String>,
    pub span: Option<SourceSpan>,
}

/// Basic block info from MIR
#[derive(Debug, Clone)]
pub struct BasicBlockInfo {
    pub index: usize,
    pub terminator: BlockTerminator,
    pub successors: Vec<usize>,
    pub is_yield: bool,
}

/// Async function info for extraction
#[derive(Debug, Clone)]
pub struct AsyncFunctionInfo {
    pub name: String,
    pub is_async: bool,
    pub return_type: Option<VcType>,
    pub parameters: Vec<(String, VcType)>,
    pub yield_points: Vec<YieldPointInfo>,
    pub basic_blocks: Vec<BasicBlockInfo>,
    pub span: Option<SourceSpan>,
}

/// Extraction options
#[derive(Debug, Clone, Default)]
pub struct ExtractionOptions {
    pub include_spans: bool,
    pub track_captured_variables: bool,
    pub max_states: usize,
}

/// Warning during extraction
#[derive(Debug, Clone)]
pub struct ExtractionWarning {
    pub message: String,
    pub span: Option<SourceSpan>,
}

/// Result of extraction
#[derive(Debug)]
pub struct ExtractionResult {
    pub state_machine: AsyncStateMachine,
    pub warnings: Vec<ExtractionWarning>,
    pub complete: bool,
}

/// The state machine extractor
pub struct AsyncStateMachineExtractor {
    pub state_machines: Vec<AsyncStateMachine>,
    pub options: ExtractionOptions,
}

impl Default for AsyncStateMachineExtractor {
    fn default() -> Self {
        Self::new()
    }
}

impl AsyncStateMachineExtractor {
    pub fn new() -> Self {
        Self {
            state_machines: Vec::new(),
            options: ExtractionOptions::default(),
        }
    }

    pub fn with_options(options: ExtractionOptions) -> Self {
        Self {
            state_machines: Vec::new(),
            options,
        }
    }

    /// Extract state machine from async function info
    pub fn extract(&mut self, func: &AsyncFunctionInfo) -> ExtractionResult {
        let mut warnings = Vec::new();

        if !func.is_async {
            warnings.push(ExtractionWarning {
                message: format!("Function '{}' is not async", func.name),
                span: func.span.clone(),
            });
        }

        let mut sm = AsyncStateMachine::new(&func.name);

        // If no yield points, trivial async function
        if func.yield_points.is_empty() {
            let end = sm.add_state("End", AsyncStateKind::End);
            sm.add_transition(0, end);
            self.state_machines.push(sm.clone());
            return ExtractionResult {
                state_machine: sm,
                warnings,
                complete: true,
            };
        }

        // Build state machine from yield points
        let complete = self.build_state_machine(&mut sm, func, &mut warnings);
        self.state_machines.push(sm.clone());

        ExtractionResult {
            state_machine: sm,
            warnings,
            complete,
        }
    }

    fn build_state_machine(
        &self,
        sm: &mut AsyncStateMachine,
        func: &AsyncFunctionInfo,
        warnings: &mut Vec<ExtractionWarning>,
    ) -> bool {
        let mut block_to_state: HashMap<usize, usize> = HashMap::new();
        block_to_state.insert(0, 0); // Entry maps to Start

        // Create states for yield points
        for (i, yp) in func.yield_points.iter().enumerate() {
            let state_name = format!("AfterAwait{}", i);
            let state_idx = sm.add_state(&state_name, AsyncStateKind::Suspended);
            block_to_state.insert(yp.block, state_idx);

            // Track captured variables
            if self.options.track_captured_variables {
                for var in &yp.live_variables {
                    let existing = sm.captured_variables.iter().position(|v| v.name == *var);
                    if existing.is_none() {
                        sm.captured_variables.push(CapturedVariable {
                            name: var.clone(),
                            ty: VcType::Abstract("_inferred".to_string()),
                            live_across: vec![i],
                            is_mutable: false,
                        });
                    } else if let Some(idx) = existing {
                        sm.captured_variables[idx].live_across.push(i);
                    }
                }
            }
        }

        // Create end state
        let end_state = sm.add_state("End", AsyncStateKind::End);

        // Create states for basic blocks
        use std::collections::hash_map::Entry;
        for block in &func.basic_blocks {
            if let Entry::Vacant(entry) = block_to_state.entry(block.index) {
                if block.terminator == BlockTerminator::Return {
                    entry.insert(end_state);
                } else {
                    let state_name = format!("Block{}", block.index);
                    let state_idx = sm.add_state(&state_name, AsyncStateKind::Resumable);
                    entry.insert(state_idx);
                }
            }
        }

        // Check state limit
        if self.options.max_states > 0 && sm.states.len() > self.options.max_states {
            warnings.push(ExtractionWarning {
                message: format!(
                    "State machine exceeds max states ({} > {})",
                    sm.states.len(),
                    self.options.max_states
                ),
                span: func.span.clone(),
            });
            return false;
        }

        // Create transitions
        for block in &func.basic_blocks {
            let from_state = *block_to_state.get(&block.index).unwrap_or(&0);
            for succ in &block.successors {
                let to_state = *block_to_state.get(succ).unwrap_or(&end_state);
                let t = sm.add_transition(from_state, to_state);
                t.is_yield = block.is_yield;
            }
        }

        // Add yield point metadata
        for (i, yp) in func.yield_points.iter().enumerate() {
            let pre_state = *block_to_state.get(&yp.block).unwrap_or(&0);
            let post_block = func
                .basic_blocks
                .iter()
                .find(|b| b.index == yp.block)
                .and_then(|b| b.successors.first().copied())
                .unwrap_or(yp.block.saturating_add(1));
            let post_state = *block_to_state.get(&post_block).unwrap_or(&end_state);

            let yp_idx = sm.add_yield_point(pre_state, post_state);
            sm.yield_points[yp_idx].awaited_future = yp.awaited_expr.clone();
            sm.yield_points[yp_idx].future_type = yp.future_type.clone();
            let _ = i;
        }

        true
    }

    /// Extract a simple sequential async function
    pub fn extract_sequential(&mut self, name: &str, yield_count: usize) -> AsyncStateMachine {
        let mut sm = AsyncStateMachine::new(name);

        if yield_count == 0 {
            let end = sm.add_state("End", AsyncStateKind::End);
            sm.add_transition(0, end);
            self.state_machines.push(sm.clone());
            return sm;
        }

        let mut prev_state = 0;
        for i in 0..yield_count {
            let resumable = sm.add_state(&format!("BeforeAwait{}", i), AsyncStateKind::Resumable);
            sm.add_transition(prev_state, resumable);

            let suspended = sm.add_state(&format!("AfterAwait{}", i), AsyncStateKind::Suspended);
            {
                let t = sm.add_transition(resumable, suspended);
                t.is_yield = true;
            }
            sm.add_yield_point(resumable, suspended);
            prev_state = suspended;
        }

        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(prev_state, end);

        self.state_machines.push(sm.clone());
        sm
    }

    /// Extract a branching async function
    pub fn extract_branching(&mut self, name: &str, branches: &[usize]) -> AsyncStateMachine {
        let mut sm = AsyncStateMachine::new(name);

        if branches.is_empty() || branches.iter().all(|&c| c == 0) {
            let end = sm.add_state("End", AsyncStateKind::End);
            sm.add_transition(0, end);
            self.state_machines.push(sm.clone());
            return sm;
        }

        let end = sm.add_state("End", AsyncStateKind::End);

        for (branch_idx, &yield_count) in branches.iter().enumerate() {
            let branch_start = sm.add_state(
                &format!("Branch{}_Start", branch_idx),
                AsyncStateKind::Resumable,
            );
            sm.add_transition(0, branch_start);

            let mut prev_state = branch_start;
            for i in 0..yield_count {
                let suspended = sm.add_state(
                    &format!("Branch{}_Await{}", branch_idx, i),
                    AsyncStateKind::Suspended,
                );
                {
                    let t = sm.add_transition(prev_state, suspended);
                    t.is_yield = true;
                }
                sm.add_yield_point(prev_state, suspended);
                prev_state = suspended;
            }

            sm.add_transition(prev_state, end);
        }

        self.state_machines.push(sm.clone());
        sm
    }
}

// ============================================
// TLA2Model Conversion (mirrors tla-extract)
// ============================================

/// State ID in TLA2 model
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StateId(pub usize);

/// Action ID in TLA2 model
#[derive(Debug, Clone, Copy)]
pub struct ActionId(pub u64);

/// Variable type in TLA2
#[derive(Debug, Clone)]
pub enum VarType {
    Bool,
    Int { bits: u8, signed: bool },
    Array { elem: Box<VarType>, len: usize },
    Tuple(Vec<VarType>),
    Opaque(String),
}

/// TLA2 Variable
#[derive(Debug, Clone)]
pub struct Variable {
    pub name: String,
    pub ty: VarType,
    pub initial_value: Option<TlaExpr>,
}

/// TLA2 Expression
#[derive(Debug, Clone)]
pub enum TlaExpr {
    Int(i64),
    Bool(bool),
    Var(String),
}

/// TLA2 Predicate
#[derive(Debug, Clone)]
pub enum TlaPredicate {
    Bool(bool),
    Expr(TlaExpr),
    And(Vec<TlaPredicate>),
}

/// TLA2 Assignment
#[derive(Debug, Clone)]
pub struct Assignment {
    pub variable: String,
    pub value: TlaExpr,
}

/// TLA2 Transition
#[derive(Debug, Clone)]
pub struct Transition {
    pub action_id: ActionId,
    pub name: String,
    pub from: Option<StateId>,
    pub to: Option<StateId>,
    pub guard: TlaPredicate,
    pub assignments: Vec<Assignment>,
    pub is_yield: bool,
}

/// TLA2 Model
#[derive(Debug, Clone)]
pub struct TLA2Model {
    pub version: String,
    pub name: String,
    pub variables: Vec<Variable>,
    pub init: TlaPredicate,
    pub transitions: Vec<Transition>,
    pub initial_state: StateId,
    pub terminal_states: Vec<StateId>,
}

impl TLA2Model {
    pub fn new(name: &str) -> Self {
        Self {
            version: "1.0".to_string(),
            name: name.to_string(),
            variables: Vec::new(),
            init: TlaPredicate::Bool(true),
            transitions: Vec::new(),
            initial_state: StateId(0),
            terminal_states: Vec::new(),
        }
    }

    /// Convert to JSON string
    pub fn to_json(&self) -> String {
        let mut json = String::new();
        json.push_str("{\n");
        json.push_str(&format!("  \"version\": \"{}\",\n", self.version));
        json.push_str(&format!("  \"name\": \"{}\",\n", escape_json(&self.name)));

        // Variables
        json.push_str("  \"variables\": [\n");
        for (i, var) in self.variables.iter().enumerate() {
            json.push_str(&format!("    {{ \"name\": \"{}\" }}", var.name));
            if i < self.variables.len().saturating_sub(1) {
                json.push(',');
            }
            json.push('\n');
        }
        json.push_str("  ],\n");

        // Transitions
        json.push_str("  \"transitions\": [\n");
        for (i, trans) in self.transitions.iter().enumerate() {
            json.push_str(&format!(
                "    {{ \"name\": \"{}\", \"from\": {}, \"to\": {}, \"is_yield\": {} }}",
                trans.name,
                trans.from.map(|s| s.0.to_string()).unwrap_or("null".to_string()),
                trans.to.map(|s| s.0.to_string()).unwrap_or("null".to_string()),
                trans.is_yield
            ));
            if i < self.transitions.len().saturating_sub(1) {
                json.push(',');
            }
            json.push('\n');
        }
        json.push_str("  ],\n");

        // Initial and terminal states
        json.push_str(&format!("  \"initial_state\": {},\n", self.initial_state.0));
        json.push_str("  \"terminal_states\": [");
        for (i, state) in self.terminal_states.iter().enumerate() {
            if i > 0 {
                json.push_str(", ");
            }
            json.push_str(&format!("{}", state.0));
        }
        json.push_str("]\n");

        json.push('}');
        json
    }
}

fn escape_json(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t")
}

/// Convert AsyncStateMachine to TLA2Model
pub fn convert_to_tla2(sm: &AsyncStateMachine) -> TLA2Model {
    let mut model = TLA2Model::new(&sm.name);

    // Convert captured variables
    for cv in &sm.captured_variables {
        model.variables.push(Variable {
            name: cv.name.clone(),
            ty: VarType::Opaque("_inferred".to_string()),
            initial_value: None,
        });
    }

    // Add state variable
    model.variables.push(Variable {
        name: "_state".to_string(),
        ty: VarType::Int { bits: 32, signed: false },
        initial_value: Some(TlaExpr::Int(sm.initial as i64)),
    });

    // Set initial state
    model.initial_state = StateId(sm.initial);

    // Find terminal states
    model.terminal_states = sm
        .states
        .iter()
        .filter(|s| s.kind == AsyncStateKind::End)
        .map(|s| StateId(s.id))
        .collect();

    // Convert transitions
    let mut action_counter: u64 = 0;
    for trans in &sm.transitions {
        model.transitions.push(Transition {
            action_id: ActionId(action_counter),
            name: format!("t{}_{}", trans.from, trans.to),
            from: Some(StateId(trans.from)),
            to: Some(StateId(trans.to)),
            guard: TlaPredicate::Bool(true),
            assignments: Vec::new(),
            is_yield: trans.is_yield,
        });
        action_counter += 1;
    }

    // Build init predicate
    model.init = TlaPredicate::And(vec![TlaPredicate::Expr(TlaExpr::Int(sm.initial as i64))]);

    model
}

// ============================================
// Integration Tests
// ============================================

/// Test: Extract sequential async function and convert to TLA2
fn test_sequential_extraction() -> bool {
    println!("  Testing sequential async extraction...");

    let mut extractor = AsyncStateMachineExtractor::new();

    // Simulate: async fn fetch_data() { a.await; b.await; c.await; }
    let sm = extractor.extract_sequential("fetch_data", 3);

    // Verify extraction
    if sm.yield_count() != 3 {
        println!("    FAIL: Expected 3 yield points, got {}", sm.yield_count());
        return false;
    }

    if !sm.can_terminate() {
        println!("    FAIL: State machine cannot terminate");
        return false;
    }

    if !sm.is_sequential() {
        println!("    FAIL: State machine should be sequential");
        return false;
    }

    // Convert to TLA2
    let model = convert_to_tla2(&sm);

    // Verify conversion
    if model.name != "fetch_data" {
        println!("    FAIL: Model name mismatch");
        return false;
    }

    if model.transitions.len() != sm.transitions.len() {
        println!("    FAIL: Transition count mismatch");
        return false;
    }

    if model.terminal_states.is_empty() {
        println!("    FAIL: No terminal states");
        return false;
    }

    // Export JSON
    let json = model.to_json();
    if !json.contains("\"name\": \"fetch_data\"") {
        println!("    FAIL: JSON missing name");
        return false;
    }

    if !json.contains("\"version\": \"1.0\"") {
        println!("    FAIL: JSON missing version");
        return false;
    }

    println!("    PASS: Sequential extraction successful");
    true
}

/// Test: Extract branching async function and convert to TLA2
fn test_branching_extraction() -> bool {
    println!("  Testing branching async extraction...");

    let mut extractor = AsyncStateMachineExtractor::new();

    // Simulate: async fn select_path(cond: bool) { if cond { a.await } else { b.await; c.await } }
    let sm = extractor.extract_branching("select_path", &[1, 2]);

    // Verify extraction
    if sm.yield_count() != 3 {
        println!("    FAIL: Expected 3 yield points, got {}", sm.yield_count());
        return false;
    }

    if !sm.can_terminate() {
        println!("    FAIL: State machine cannot terminate");
        return false;
    }

    if sm.is_sequential() {
        println!("    FAIL: State machine should NOT be sequential (has branches)");
        return false;
    }

    // Convert to TLA2
    let model = convert_to_tla2(&sm);

    if model.terminal_states.len() != 1 {
        println!("    FAIL: Expected 1 terminal state, got {}", model.terminal_states.len());
        return false;
    }

    // Export JSON
    let json = model.to_json();
    if !json.contains("\"name\": \"select_path\"") {
        println!("    FAIL: JSON missing name");
        return false;
    }

    println!("    PASS: Branching extraction successful");
    true
}

/// Test: Extract from AsyncFunctionInfo (realistic MIR simulation)
fn test_function_info_extraction() -> bool {
    println!("  Testing AsyncFunctionInfo extraction...");

    let mut extractor = AsyncStateMachineExtractor::with_options(ExtractionOptions {
        include_spans: true,
        track_captured_variables: true,
        max_states: 100,
    });

    // Simulate MIR for: async fn process_request(url: &str) { let resp = fetch(url).await; parse(resp).await; }
    let func = AsyncFunctionInfo {
        name: "process_request".to_string(),
        is_async: true,
        return_type: None,
        parameters: vec![("url".to_string(), VcType::Abstract("&str".to_string()))],
        yield_points: vec![
            YieldPointInfo {
                index: 0,
                block: 1,
                awaited_expr: Some("fetch(url)".to_string()),
                future_type: Some("impl Future<Output=Response>".to_string()),
                live_variables: vec!["url".to_string()],
                span: None,
            },
            YieldPointInfo {
                index: 1,
                block: 2,
                awaited_expr: Some("parse(resp)".to_string()),
                future_type: Some("impl Future<Output=Data>".to_string()),
                live_variables: vec!["resp".to_string()],
                span: None,
            },
        ],
        basic_blocks: vec![
            BasicBlockInfo {
                index: 0,
                terminator: BlockTerminator::Goto,
                successors: vec![1],
                is_yield: false,
            },
            BasicBlockInfo {
                index: 1,
                terminator: BlockTerminator::Yield,
                successors: vec![2],
                is_yield: true,
            },
            BasicBlockInfo {
                index: 2,
                terminator: BlockTerminator::Yield,
                successors: vec![3],
                is_yield: true,
            },
            BasicBlockInfo {
                index: 3,
                terminator: BlockTerminator::Return,
                successors: vec![],
                is_yield: false,
            },
        ],
        span: Some(SourceSpan {
            file: "src/handlers.rs".to_string(),
            line_start: 42,
            line_end: 45,
            col_start: 1,
            col_end: 2,
        }),
    };

    let result = extractor.extract(&func);

    // Verify extraction
    if !result.complete {
        println!("    FAIL: Extraction incomplete");
        return false;
    }

    if !result.warnings.is_empty() {
        println!("    FAIL: Unexpected warnings during extraction");
        return false;
    }

    let sm = &result.state_machine;
    if sm.yield_count() != 2 {
        println!("    FAIL: Expected 2 yield points, got {}", sm.yield_count());
        return false;
    }

    if !sm.can_terminate() {
        println!("    FAIL: State machine cannot terminate");
        return false;
    }

    // Verify captured variables tracking
    if sm.captured_variables.len() != 2 {
        println!("    FAIL: Expected 2 captured variables, got {}", sm.captured_variables.len());
        return false;
    }

    // Convert to TLA2
    let model = convert_to_tla2(&sm);

    // Verify model has variables (captured + _state)
    if model.variables.len() != 3 {
        println!("    FAIL: Expected 3 variables (2 captured + _state), got {}", model.variables.len());
        return false;
    }

    // Export JSON and validate
    let json = model.to_json();
    if !json.contains("\"name\": \"process_request\"") {
        println!("    FAIL: JSON missing name");
        return false;
    }

    println!("    PASS: AsyncFunctionInfo extraction successful");
    println!("    JSON output preview: {}", &json[..json.len().min(200)]);
    true
}

/// Test: Detect deadlock in extracted state machine
fn test_deadlock_detection() -> bool {
    println!("  Testing deadlock detection...");

    // Manually create a state machine with a deadlock
    let mut sm = AsyncStateMachine::new("deadlock_test");
    let stuck = sm.add_state("Stuck", AsyncStateKind::Resumable);
    let _end = sm.add_state("End", AsyncStateKind::End);

    // Transition to Stuck, but no way out
    sm.add_transition(0, stuck);

    let deadlocks = sm.find_deadlocks();
    if deadlocks.len() != 1 {
        println!("    FAIL: Expected 1 deadlock state, got {}", deadlocks.len());
        return false;
    }

    if deadlocks[0] != stuck {
        println!("    FAIL: Wrong deadlock state identified");
        return false;
    }

    println!("    PASS: Deadlock detection successful");
    true
}

/// Test: Validate JSON output structure
fn test_json_output_validation() -> bool {
    println!("  Testing JSON output validation...");

    let mut extractor = AsyncStateMachineExtractor::new();
    let sm = extractor.extract_sequential("json_test", 2);
    let model = convert_to_tla2(&sm);
    let json = model.to_json();

    // Validate required fields
    let required_fields = [
        "\"version\":",
        "\"name\":",
        "\"variables\":",
        "\"transitions\":",
        "\"initial_state\":",
        "\"terminal_states\":",
    ];

    for field in required_fields {
        if !json.contains(field) {
            println!("    FAIL: JSON missing required field: {}", field);
            return false;
        }
    }

    // Validate JSON is parseable (basic check)
    if !json.starts_with('{') || !json.ends_with('}') {
        println!("    FAIL: Invalid JSON structure");
        return false;
    }

    println!("    PASS: JSON output validation successful");
    true
}

// ============================================
// Main Entry Point
// ============================================

fn main() {
    println!("=== TLA Extract Integration Test ===\n");

    println!("This test validates the complete state machine extraction pipeline:");
    println!("  AsyncFunctionInfo -> AsyncStateMachineExtractor -> AsyncStateMachine");
    println!("                    -> convert_to_tla2() -> TLA2Model -> JSON\n");

    println!("--- Running Integration Tests ---\n");

    let mut passed = 0;
    let mut failed = 0;

    if test_sequential_extraction() {
        passed += 1;
    } else {
        failed += 1;
    }

    if test_branching_extraction() {
        passed += 1;
    } else {
        failed += 1;
    }

    if test_function_info_extraction() {
        passed += 1;
    } else {
        failed += 1;
    }

    if test_deadlock_detection() {
        passed += 1;
    } else {
        failed += 1;
    }

    if test_json_output_validation() {
        passed += 1;
    } else {
        failed += 1;
    }

    println!("\n--- Results ---");
    println!("Passed: {}", passed);
    println!("Failed: {}", failed);

    if failed == 0 {
        println!("\n=== TLA Extract Integration Test: ALL PASS ===");
    } else {
        println!("\n=== TLA Extract Integration Test: {} FAILURES ===", failed);
        std::process::exit(1);
    }
}

// ============================================
// Unit Tests
// ============================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extractor_new() {
        let extractor = AsyncStateMachineExtractor::new();
        assert!(extractor.state_machines.is_empty());
    }

    #[test]
    fn test_sequential_state_machine() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let sm = extractor.extract_sequential("test", 2);
        assert!(sm.is_sequential());
        assert!(sm.can_terminate());
        assert_eq!(sm.yield_count(), 2);
    }

    #[test]
    fn test_branching_state_machine() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let sm = extractor.extract_branching("test", &[1, 2]);
        assert!(!sm.is_sequential());
        assert!(sm.can_terminate());
        assert_eq!(sm.yield_count(), 3);
    }

    #[test]
    fn test_tla2_conversion() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let sm = extractor.extract_sequential("convert_test", 1);
        let model = convert_to_tla2(&sm);
        assert_eq!(model.name, "convert_test");
        assert!(!model.terminal_states.is_empty());
    }

    #[test]
    fn test_json_export() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let sm = extractor.extract_sequential("json_test", 1);
        let model = convert_to_tla2(&sm);
        let json = model.to_json();
        assert!(json.contains("\"name\": \"json_test\""));
        assert!(json.contains("\"version\": \"1.0\""));
    }

    #[test]
    fn test_deadlock_states() {
        let mut sm = AsyncStateMachine::new("deadlock");
        let stuck = sm.add_state("Stuck", AsyncStateKind::Resumable);
        sm.add_transition(0, stuck);
        // No transition out of stuck state
        let deadlocks = sm.find_deadlocks();
        assert_eq!(deadlocks.len(), 1);
        assert_eq!(deadlocks[0], stuck);
    }

    #[test]
    fn test_async_function_info_extraction() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let func = AsyncFunctionInfo {
            name: "test_fn".to_string(),
            is_async: true,
            return_type: None,
            parameters: vec![],
            yield_points: vec![YieldPointInfo {
                index: 0,
                block: 1,
                awaited_expr: Some("f()".to_string()),
                future_type: None,
                live_variables: vec![],
                span: None,
            }],
            basic_blocks: vec![
                BasicBlockInfo {
                    index: 0,
                    terminator: BlockTerminator::Goto,
                    successors: vec![1],
                    is_yield: false,
                },
                BasicBlockInfo {
                    index: 1,
                    terminator: BlockTerminator::Yield,
                    successors: vec![2],
                    is_yield: true,
                },
                BasicBlockInfo {
                    index: 2,
                    terminator: BlockTerminator::Return,
                    successors: vec![],
                    is_yield: false,
                },
            ],
            span: None,
        };
        let result = extractor.extract(&func);
        assert!(result.complete);
        assert!(result.warnings.is_empty());
        assert_eq!(result.state_machine.yield_count(), 1);
    }
}
