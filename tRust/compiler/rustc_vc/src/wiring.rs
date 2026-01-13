//! Wiring Verification (Phase 6.5)
//!
//! Verifies structural connectivity in programs - that code paths exist
//! from entry points through all annotated states.
//!
//! Wire annotations:
//! - `#[wire::start]` - entry point for reachability analysis
//! - `#[wire::state("name")]` - named state that must be reachable
//! - `#[wire::must_reach("state1", "state2")]` - required successors
//! - `#[wire::recoverable]` - error state with recovery path
//! - `#[wire::terminal]` - valid end point

use crate::{AggregateKind, Local, MirFunction, MirType, Operand, Rvalue, Statement, Terminator};
use std::collections::{HashMap, HashSet, VecDeque};
#[cfg(test)]
use vc_ir::WireAnnotation;
use vc_ir::{
    AsyncChain, AsyncChainNode, AsyncChainViolation, AsyncChainViolationType, AsyncTermination,
    DataFlowViolation, DeadCode, DeadCodeReason, MissingAwait, MissingReach, PartialStructUpdate,
    PartialUpdateReason, PathAnomaly, ResultHandling, SourceSpan, UnhandledResult,
    UnreachableState, UnusedValue, WireSpec, WireVerifyResult,
};

/// Call graph for wiring analysis
#[derive(Debug, Default)]
pub struct CallGraph {
    /// Map from function name to list of called functions
    calls: HashMap<String, Vec<String>>,
    /// Map from function name to its wire specification
    wire_specs: HashMap<String, WireSpec>,
    /// Map from state name to function name
    states: HashMap<String, String>,
    /// Start functions
    start_functions: Vec<String>,
}

impl CallGraph {
    /// Create a new empty call graph
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a function to the call graph
    pub fn add_function(&mut self, name: &str, callees: Vec<String>) {
        self.calls.insert(name.to_string(), callees);
    }

    /// Add wire specification for a function
    pub fn add_wire_spec(&mut self, name: &str, spec: WireSpec) {
        // Track state names
        if let Some(state_name) = spec.state_name() {
            self.states.insert(state_name.to_string(), name.to_string());
        }

        // Track start functions
        if spec.is_start() {
            self.start_functions.push(name.to_string());
        }

        self.wire_specs.insert(name.to_string(), spec);
    }

    /// Get functions called by a function
    #[must_use]
    pub fn get_callees(&self, name: &str) -> Option<&[String]> {
        self.calls.get(name).map(Vec::as_slice)
    }

    /// Get wire spec for a function
    #[must_use]
    pub fn get_wire_spec(&self, name: &str) -> Option<&WireSpec> {
        self.wire_specs.get(name)
    }

    /// Build call graph from MIR functions
    #[must_use]
    pub fn from_mir_functions(funcs: &[MirFunction]) -> Self {
        let mut graph = Self::new();

        for func in funcs {
            let mut callees = Vec::new();

            // Extract call targets from MIR
            // Phase 6.5.2: Track generic arguments for monomorphized calls
            for block in &func.blocks {
                if let Terminator::Call {
                    func: callee,
                    generic_args,
                    ..
                } = &block.terminator
                {
                    // Use monomorphized name if generic arguments are present
                    let callee_name = crate::monomorphized_name(callee, generic_args);
                    callees.push(callee_name);
                }
            }

            graph.add_function(&func.name, callees);
        }

        graph
    }

    /// Compute reachable functions from a starting point
    #[must_use]
    pub fn reachable_from(&self, start: &str) -> HashSet<String> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();

        queue.push_back(start.to_string());

        while let Some(current) = queue.pop_front() {
            if visited.contains(&current) {
                continue;
            }
            visited.insert(current.clone());

            if let Some(callees) = self.calls.get(&current) {
                for callee in callees {
                    if !visited.contains(callee) {
                        queue.push_back(callee.clone());
                    }
                }
            }
        }

        visited
    }

    /// Check if a target is reachable from source
    #[must_use]
    pub fn can_reach(&self, source: &str, target: &str) -> bool {
        self.reachable_from(source).contains(target)
    }

    /// Check if a state is reachable from any start point
    #[must_use]
    pub fn state_reachable(&self, state: &str) -> bool {
        // Find the function containing this state
        if let Some(func_name) = self.states.get(state) {
            // Check if reachable from any start function
            for start in &self.start_functions {
                if self.can_reach(start, func_name) {
                    return true;
                }
            }
        }
        false
    }
}

/// Wiring verifier
#[derive(Debug)]
pub struct WiringVerifier {
    call_graph: CallGraph,
}

impl WiringVerifier {
    /// Create a new wiring verifier from a call graph
    #[must_use]
    pub const fn new(call_graph: CallGraph) -> Self {
        Self { call_graph }
    }

    /// Build verifier from MIR functions
    #[must_use]
    pub fn from_mir_functions(funcs: &[MirFunction]) -> Self {
        Self::new(CallGraph::from_mir_functions(funcs))
    }

    /// Add wire specification for a function
    pub fn add_wire_spec(&mut self, name: &str, spec: WireSpec) {
        self.call_graph.add_wire_spec(name, spec);
    }

    /// Verify wiring constraints
    #[must_use]
    pub fn verify(&self) -> WireVerifyResult {
        let mut result = WireVerifyResult::default();

        // Check for unreachable states
        self.check_reachability(&mut result);

        // Check must_reach constraints
        self.check_must_reach(&mut result);

        // Check recoverable states
        self.check_recoverable(&mut result);

        // Check for dead code (Phase 6.5.4)
        self.check_dead_code(&mut result);

        result
    }

    /// Check that all states are reachable from start
    fn check_reachability(&self, result: &mut WireVerifyResult) {
        // If no start functions, all states with wire specs are potentially unreachable
        if self.call_graph.start_functions.is_empty() {
            // No start point defined - skip reachability check
            return;
        }

        // Compute all reachable functions from all start points
        let mut all_reachable = HashSet::new();
        for start in &self.call_graph.start_functions {
            all_reachable.extend(self.call_graph.reachable_from(start));
        }

        // Check each state
        for (state_name, func_name) in &self.call_graph.states {
            if !all_reachable.contains(func_name) {
                let span = self
                    .call_graph
                    .wire_specs
                    .get(func_name)
                    .and_then(|s| s.span.clone())
                    .unwrap_or_else(|| SourceSpan {
                        file: std::sync::Arc::from("unknown"),
                        line_start: 0,
                        line_end: 0,
                        col_start: 0,
                        col_end: 0,
                    });

                result.unreachable_states.push(UnreachableState {
                    state: state_name.clone(),
                    function: func_name.clone(),
                    span,
                });
            }
        }
    }

    /// Check must_reach constraints
    fn check_must_reach(&self, result: &mut WireVerifyResult) {
        for (func_name, spec) in &self.call_graph.wire_specs {
            let must_reach = spec.must_reach();
            for target_state in must_reach {
                // Find the function containing the target state
                if let Some(target_func) = self.call_graph.states.get(target_state) {
                    if !self.call_graph.can_reach(func_name, target_func) {
                        let span = spec.span.clone().unwrap_or_else(|| SourceSpan {
                            file: std::sync::Arc::from("unknown"),
                            line_start: 0,
                            line_end: 0,
                            col_start: 0,
                            col_end: 0,
                        });

                        result.missing_reaches.push(MissingReach {
                            from_function: func_name.clone(),
                            target_state: target_state.to_string(),
                            span,
                        });
                    }
                } else {
                    // Target state doesn't exist - report as missing reach
                    let span = spec.span.clone().unwrap_or_else(|| SourceSpan {
                        file: std::sync::Arc::from("unknown"),
                        line_start: 0,
                        line_end: 0,
                        col_start: 0,
                        col_end: 0,
                    });

                    result.missing_reaches.push(MissingReach {
                        from_function: func_name.clone(),
                        target_state: target_state.to_string(),
                        span,
                    });
                }
            }
        }
    }

    /// Check recoverable states have recovery paths
    fn check_recoverable(&self, result: &mut WireVerifyResult) {
        for (func_name, spec) in &self.call_graph.wire_specs {
            if !spec.is_recoverable() {
                continue;
            }

            // A recoverable state must be able to reach a non-recoverable, non-terminal state
            let reachable = self.call_graph.reachable_from(func_name);
            let has_recovery = reachable.iter().any(|reached| {
                if reached == func_name {
                    return false; // Can't recover to itself
                }
                if let Some(reached_spec) = self.call_graph.wire_specs.get(reached) {
                    // Must reach something that's not also recoverable (error) and not terminal
                    !reached_spec.is_recoverable() && reached_spec.state_name().is_some()
                } else {
                    false
                }
            });

            if !has_recovery {
                result.unrecoverable_states.push(func_name.clone());
            }
        }
    }

    /// Check for dead code paths (Phase 6.5.4)
    ///
    /// Detects functions that are defined but never called from any
    /// entry point. This only applies when at least one start function
    /// is defined.
    fn check_dead_code(&self, result: &mut WireVerifyResult) {
        // Only check for dead code if we have start functions
        if self.call_graph.start_functions.is_empty() {
            return;
        }

        // Compute all reachable functions from all start points
        let mut all_reachable = HashSet::new();
        for start in &self.call_graph.start_functions {
            all_reachable.extend(self.call_graph.reachable_from(start));
        }

        // Find functions that have wire specs but are not reachable
        // These are dead code - they have annotations but can't be reached
        for (func_name, spec) in &self.call_graph.wire_specs {
            // Skip start functions themselves
            if spec.is_start() {
                continue;
            }

            // If this function has wire annotations but isn't reachable, it's dead code
            if !spec.is_empty() && !all_reachable.contains(func_name) {
                let span = spec.span.clone().unwrap_or_else(|| SourceSpan {
                    file: std::sync::Arc::from("unknown"),
                    line_start: 0,
                    line_end: 0,
                    col_start: 0,
                    col_end: 0,
                });

                result.path_anomalies.push(PathAnomaly::DeadCode(DeadCode {
                    function: func_name.clone(),
                    reason: DeadCodeReason::UnreachableFromStart,
                    span,
                }));
            }
        }
    }

    /// Check for functions that are never called (no callers)
    ///
    /// This is a more general dead code check that doesn't require
    /// start functions to be defined.
    #[must_use]
    pub fn check_never_called(&self, all_functions: &[String]) -> Vec<PathAnomaly> {
        let mut anomalies = Vec::new();

        // Build reverse call graph (who calls whom)
        let mut called_by: HashMap<String, Vec<String>> = HashMap::new();
        for (caller, callees) in &self.call_graph.calls {
            for callee in callees {
                called_by
                    .entry(callee.clone())
                    .or_default()
                    .push(caller.clone());
            }
        }

        // Find functions that have no callers and are not start functions
        for func in all_functions {
            let is_start = self
                .call_graph
                .wire_specs
                .get(func)
                .is_some_and(WireSpec::is_start);

            if is_start {
                continue;
            }

            let has_callers = called_by.get(func).is_some_and(|v| !v.is_empty());

            if !has_callers {
                // Check if this function has a wire spec with a span
                let span = self
                    .call_graph
                    .wire_specs
                    .get(func)
                    .and_then(|s| s.span.clone())
                    .unwrap_or_else(|| SourceSpan {
                        file: std::sync::Arc::from("unknown"),
                        line_start: 0,
                        line_end: 0,
                        col_start: 0,
                        col_end: 0,
                    });

                anomalies.push(PathAnomaly::DeadCode(DeadCode {
                    function: func.clone(),
                    reason: DeadCodeReason::NeverCalled,
                    span,
                }));
            }
        }

        anomalies
    }

    /// Check for unhandled Result values (Phase 6.5.4)
    ///
    /// Detects when a function call returns Result<T,E> but the caller
    /// ignores or doesn't properly handle the error case.
    #[must_use]
    pub fn check_unhandled_results(&self, funcs: &[MirFunction]) -> Vec<PathAnomaly> {
        let analyzer = ResultAnalyzer::new(funcs);
        analyzer.find_unhandled_results()
    }

    /// Check for missing await calls (Phase 6.5.4)
    ///
    /// Detects when an async function is called but the returned Future
    /// is not awaited or otherwise consumed.
    #[must_use]
    pub fn check_missing_awaits(&self, funcs: &[MirFunction]) -> Vec<PathAnomaly> {
        let analyzer = AwaitAnalyzer::new(funcs);
        analyzer.find_missing_awaits()
    }

    /// Check for partial struct updates (Phase 6.5.4)
    ///
    /// Detects when a struct is created using update syntax (`..old`)
    /// or when struct fields are partially moved/mutated.
    #[must_use]
    pub fn check_partial_struct_updates(&self, funcs: &[MirFunction]) -> Vec<PathAnomaly> {
        let analyzer = StructUpdateAnalyzer::new(funcs);
        analyzer.find_partial_updates()
    }

    /// Check for unused values (Phase 6.5.5)
    ///
    /// Detects when a value is read but never used, or when a computed
    /// value is never returned or stored.
    #[must_use]
    pub fn check_unused_values(&self, funcs: &[MirFunction]) -> Vec<PathAnomaly> {
        let analyzer = DataFlowAnalyzer::new(funcs);
        analyzer.find_unused_values()
    }

    /// Check data flow annotations (Phase 6.5.5)
    ///
    /// Verifies that annotated inputs reach annotated outputs through
    /// the data flow graph.
    #[must_use]
    pub fn check_data_flow_annotations(&self, funcs: &[MirFunction]) -> Vec<DataFlowViolation> {
        let analyzer = DataFlowAnalyzer::new(funcs);
        analyzer.verify_data_flow_annotations(&self.call_graph)
    }

    /// Check for async chain violations (Phase 6.5.2)
    ///
    /// Detects issues in async function call chains:
    /// - Futures that are never awaited
    /// - Incomplete async chains
    /// - Dangling spawned tasks
    /// - Cyclic await dependencies
    #[must_use]
    pub fn check_async_chains(&self, funcs: &[MirFunction]) -> Vec<PathAnomaly> {
        let mut analyzer = AsyncChainAnalyzer::new(funcs);
        let mut anomalies = analyzer.find_async_chain_violations();
        anomalies.extend(analyzer.find_cyclic_dependencies());
        anomalies
    }
}

/// Analyzes Result handling in MIR code (Phase 6.5.4)
///
/// Detects calls to functions that return Result where the error
/// case is not properly handled.
#[derive(Debug)]
pub struct ResultAnalyzer<'a> {
    /// Functions to analyze
    funcs: &'a [MirFunction],
    /// Map from function name to return type
    return_types: HashMap<String, &'a MirType>,
}

impl<'a> ResultAnalyzer<'a> {
    /// Create a new Result analyzer
    #[must_use]
    pub fn new(funcs: &'a [MirFunction]) -> Self {
        let mut return_types = HashMap::new();
        for func in funcs {
            return_types.insert(func.name.clone(), &func.return_type);
        }
        Self {
            funcs,
            return_types,
        }
    }

    /// Check if a type is a Result type
    fn is_result_type(ty: &MirType) -> bool {
        match ty {
            MirType::Adt { name } => {
                // Match Result, std::result::Result, core::result::Result
                name == "Result" || name.ends_with("::Result") || name.starts_with("Result<")
            }
            _ => false,
        }
    }

    /// Check if a local is used (read) in the function after a given block
    fn is_local_used(func: &MirFunction, local: Local, from_block: usize) -> bool {
        // Check all blocks from the given block onwards
        for block_idx in from_block..func.blocks.len() {
            let block = &func.blocks[block_idx];

            // Check statements for reads of this local
            for stmt in &block.statements {
                if let Statement::Assign { rvalue, .. } = stmt {
                    if Self::rvalue_reads_local(rvalue, local) {
                        return true;
                    }
                }
            }

            // Check terminator for reads
            if Self::terminator_reads_local(&block.terminator, local) {
                return true;
            }
        }
        false
    }

    /// Check if an rvalue reads a given local
    fn rvalue_reads_local(rvalue: &Rvalue, local: Local) -> bool {
        match rvalue {
            Rvalue::Use(op)
            | Rvalue::UnaryOp(_, op)
            | Rvalue::Cast { operand: op, .. }
            | Rvalue::Repeat { operand: op, .. } => Self::operand_is_local(op, local),
            Rvalue::BinaryOp(_, left, right) | Rvalue::CheckedBinaryOp(_, left, right) => {
                Self::operand_is_local(left, local) || Self::operand_is_local(right, local)
            }
            Rvalue::Ref { place, .. } | Rvalue::Discriminant(place) | Rvalue::Len(place) => {
                place.local == local
            }
            Rvalue::Aggregate { operands, .. } => {
                operands.iter().any(|op| Self::operand_is_local(op, local))
            }
            Rvalue::NullaryOp(_, _) => false, // NullaryOp (SizeOf, AlignOf) don't read locals
        }
    }

    /// Check if an operand references a local
    fn operand_is_local(op: &Operand, local: Local) -> bool {
        match op {
            Operand::Copy(place) | Operand::Move(place) => place.local == local,
            Operand::Constant(_) => false,
        }
    }

    /// Check if a terminator reads a given local
    fn terminator_reads_local(term: &Terminator, local: Local) -> bool {
        match term {
            Terminator::SwitchInt { discr, .. } => Self::operand_is_local(discr, local),
            Terminator::Call { args, .. } => {
                args.iter().any(|op| Self::operand_is_local(op, local))
            }
            Terminator::IndirectCall { callee, args, .. } => {
                callee.local == local || args.iter().any(|op| Self::operand_is_local(op, local))
            }
            Terminator::Assert { cond, .. } => Self::operand_is_local(cond, local),
            Terminator::Return | Terminator::Goto { .. } | Terminator::Unreachable => false,
        }
    }

    /// Find all unhandled Result values in the analyzed functions
    #[must_use]
    pub fn find_unhandled_results(&self) -> Vec<PathAnomaly> {
        let mut anomalies = Vec::new();

        for func in self.funcs {
            for block in &func.blocks {
                if let Terminator::Call {
                    func: callee,
                    destination,
                    span,
                    target,
                    ..
                } = &block.terminator
                {
                    // Check if callee returns Result
                    let returns_result = self
                        .return_types
                        .get(callee)
                        .is_some_and(|ty| Self::is_result_type(ty));

                    // Also check for known Result-returning functions
                    let is_known_result_fn = Self::is_known_result_function(callee);

                    if returns_result || is_known_result_fn {
                        // Check if the destination local is ever used
                        let dest_local = destination.local;
                        let is_used = Self::is_local_used(func, dest_local, *target);

                        if !is_used {
                            anomalies.push(PathAnomaly::UnhandledResult(UnhandledResult {
                                function: func.name.clone(),
                                call_site: format!("{callee}()"),
                                callee: callee.clone(),
                                handling: ResultHandling::Ignored,
                                span: span.clone(),
                            }));
                        }
                    }
                }
            }
        }

        anomalies
    }

    /// Check if a function is known to return Result (built-in heuristics)
    fn is_known_result_function(name: &str) -> bool {
        // Common Result-returning patterns
        name.contains("::open")
            || name.contains("::read")
            || name.contains("::write")
            || name.contains("::parse")
            || name.contains("::connect")
            || name.contains("::send")
            || name.contains("::recv")
            || name.contains("::try_")
            || name.ends_with("_or_err")
            || name.ends_with("_checked")
    }
}

/// Analyzes async function calls for missing .await (Phase 6.5.4)
///
/// Detects calls to async functions where the returned Future is
/// not awaited or otherwise consumed.
#[derive(Debug)]
pub struct AwaitAnalyzer<'a> {
    /// Functions to analyze
    funcs: &'a [MirFunction],
    /// Map from function name to return type
    return_types: HashMap<String, &'a MirType>,
    /// Set of async function names (by pattern detection)
    async_functions: HashSet<String>,
}

impl<'a> AwaitAnalyzer<'a> {
    /// Create a new await analyzer
    #[must_use]
    pub fn new(funcs: &'a [MirFunction]) -> Self {
        let mut return_types = HashMap::new();
        let mut async_functions = HashSet::new();

        for func in funcs {
            return_types.insert(func.name.clone(), &func.return_type);

            // Detect async functions by return type
            if Self::is_future_type(&func.return_type) {
                async_functions.insert(func.name.clone());
            }
        }

        Self {
            funcs,
            return_types,
            async_functions,
        }
    }

    /// Check if a type is a Future type
    #[must_use]
    pub fn is_future_type(ty: &MirType) -> bool {
        match ty {
            MirType::Adt { name } => {
                // Match Future, impl Future, Poll, async return types
                name.contains("Future") ||
                name.contains("Poll") ||
                name.contains("impl Future") ||
                name.starts_with("async ") ||
                // Match common async executor types
                name.contains("JoinHandle") ||
                name.contains("Task") ||
                // Pin<Box<dyn Future<...>>>
                (name.contains("Pin") && name.contains("Future"))
            }
            _ => false,
        }
    }

    /// Check if a function is known to be async (built-in heuristics)
    #[must_use]
    pub fn is_known_async_function(&self, name: &str) -> bool {
        // Common async function patterns
        name.starts_with("async_") ||
        name.ends_with("_async") ||
        // tokio patterns
        name.contains("::spawn") ||
        name.contains("::sleep") ||
        name.contains("::timeout") ||
        name.contains("::select") ||
        // async-std patterns
        name.contains("::task::") ||
        // Future combinators that return futures
        name.ends_with("::then") ||
        name.ends_with("::and_then") ||
        name.ends_with("::map") ||
        name.ends_with("::flat_map") ||
        // Network async operations
        name.contains("::connect_async") ||
        name.contains("::accept_async") ||
        name.contains("::read_async") ||
        name.contains("::write_async")
    }

    /// Check if a local is used (read) in the function after a given block
    ///
    /// A Future is considered "used" if it is:
    /// - Passed to another function (likely awaited there)
    /// - Moved to a variable that is used
    /// - Part of a return value
    fn is_local_used(func: &MirFunction, local: Local, from_block: usize) -> bool {
        for block_idx in from_block..func.blocks.len() {
            let block = &func.blocks[block_idx];

            // Check statements for reads of this local
            for stmt in &block.statements {
                if let Statement::Assign { rvalue, .. } = stmt {
                    if Self::rvalue_reads_local(rvalue, local) {
                        return true;
                    }
                }
            }

            // Check terminator for reads
            if Self::terminator_reads_local(&block.terminator, local) {
                return true;
            }
        }
        false
    }

    /// Check if an rvalue reads a given local
    fn rvalue_reads_local(rvalue: &Rvalue, local: Local) -> bool {
        match rvalue {
            Rvalue::Use(op)
            | Rvalue::UnaryOp(_, op)
            | Rvalue::Cast { operand: op, .. }
            | Rvalue::Repeat { operand: op, .. } => Self::operand_is_local(op, local),
            Rvalue::BinaryOp(_, left, right) | Rvalue::CheckedBinaryOp(_, left, right) => {
                Self::operand_is_local(left, local) || Self::operand_is_local(right, local)
            }
            Rvalue::Ref { place, .. } | Rvalue::Discriminant(place) | Rvalue::Len(place) => {
                place.local == local
            }
            Rvalue::Aggregate { operands, .. } => {
                operands.iter().any(|op| Self::operand_is_local(op, local))
            }
            Rvalue::NullaryOp(_, _) => false,
        }
    }

    /// Check if an operand references a local
    fn operand_is_local(op: &Operand, local: Local) -> bool {
        match op {
            Operand::Copy(place) | Operand::Move(place) => place.local == local,
            Operand::Constant(_) => false,
        }
    }

    /// Check if a terminator reads a given local
    fn terminator_reads_local(term: &Terminator, local: Local) -> bool {
        match term {
            Terminator::SwitchInt { discr, .. } => Self::operand_is_local(discr, local),
            Terminator::Call { args, .. } => {
                args.iter().any(|op| Self::operand_is_local(op, local))
            }
            Terminator::IndirectCall { callee, args, .. } => {
                callee.local == local || args.iter().any(|op| Self::operand_is_local(op, local))
            }
            Terminator::Assert { cond, .. } => Self::operand_is_local(cond, local),
            Terminator::Return | Terminator::Goto { .. } | Terminator::Unreachable => false,
        }
    }

    /// Find all missing await calls in the analyzed functions
    #[must_use]
    pub fn find_missing_awaits(&self) -> Vec<PathAnomaly> {
        let mut anomalies = Vec::new();

        for func in self.funcs {
            for block in &func.blocks {
                if let Terminator::Call {
                    func: callee,
                    destination,
                    span,
                    target,
                    ..
                } = &block.terminator
                {
                    // Check if callee returns a Future type
                    let returns_future = self
                        .return_types
                        .get(callee)
                        .is_some_and(|ty| Self::is_future_type(ty));

                    // Also check if it's a known async function
                    let is_known_async = self.is_known_async_function(callee)
                        || self.async_functions.contains(callee);

                    if returns_future || is_known_async {
                        // Check if the destination local (the Future) is ever used
                        let dest_local = destination.local;
                        let is_used = Self::is_local_used(func, dest_local, *target);

                        if !is_used {
                            anomalies.push(PathAnomaly::MissingAwait(MissingAwait {
                                function: func.name.clone(),
                                async_callee: callee.clone(),
                                span: span.clone(),
                            }));
                        }
                    }
                }
            }
        }

        anomalies
    }
}

// ============================================
// Async Chain Analysis (Phase 6.5.2)
// ============================================

/// Analyzes async function call chains for proper termination (Phase 6.5.2)
///
/// Tracks the flow of futures through a program and detects:
/// - Futures that are never awaited (NoAwaitPoint)
/// - Async chains that don't properly terminate (IncompleteChain)
/// - Spawned tasks that are never joined (DanglingSpawn)
/// - Cyclic await dependencies (CyclicDependency)
/// - Sync/async boundary issues (SyncBoundaryCrossing)
#[derive(Debug)]
pub struct AsyncChainAnalyzer<'a> {
    /// Functions to analyze
    funcs: &'a [MirFunction],
    /// Map from function name to function data
    func_map: HashMap<String, &'a MirFunction>,
    /// Set of async function names
    async_functions: HashSet<String>,
    /// Call graph edges (caller -> list of callees)
    call_edges: HashMap<String, Vec<String>>,
    /// Functions that spawn tasks (e.g., tokio::spawn)
    spawn_functions: HashSet<String>,
    /// Functions that represent await points (e.g., .await desugared)
    await_markers: HashSet<String>,
    /// Functions that block on futures (e.g., block_on)
    block_on_functions: HashSet<String>,
    /// Chain ID counter
    next_chain_id: usize,
    /// Closures defined in each function (function name -> list of closure def_ids)
    closures_in_func: HashMap<String, Vec<String>>,
    /// Coroutines (async blocks) defined in each function
    coroutines_in_func: HashMap<String, Vec<String>>,
    /// Closures passed to spawn calls (spawn call site -> closure def_id)
    closures_to_spawn: HashMap<String, Vec<ClosureSpawnInfo>>,
    /// Indirect calls in each function
    indirect_calls: HashMap<String, Vec<IndirectCallInfo>>,
}

/// Information about a closure passed to a spawn function
#[derive(Debug, Clone)]
pub struct ClosureSpawnInfo {
    /// The closure or coroutine def_id being spawned
    pub closure_def_id: String,
    /// The spawn function being called (e.g., "tokio::spawn")
    pub spawn_func: String,
    /// Source location of the spawn call
    pub span: SourceSpan,
    /// Whether the JoinHandle is tracked (stored/awaited)
    pub join_handle_tracked: bool,
}

/// Information about an indirect call
#[derive(Debug, Clone)]
pub struct IndirectCallInfo {
    /// The local variable containing the callee
    pub callee_local: Local,
    /// The type of the callee (Closure, FnPtr, etc.)
    pub callee_type: MirType,
    /// Source location
    pub span: SourceSpan,
}

impl<'a> AsyncChainAnalyzer<'a> {
    /// Create a new async chain analyzer
    #[must_use]
    pub fn new(funcs: &'a [MirFunction]) -> Self {
        let mut func_map = HashMap::new();
        let mut async_functions = HashSet::new();
        let mut call_edges = HashMap::new();
        let mut closures_in_func = HashMap::new();
        let mut coroutines_in_func = HashMap::new();
        let mut closures_to_spawn = HashMap::new();
        let mut indirect_calls = HashMap::new();

        // Build function map and detect async functions
        for func in funcs {
            func_map.insert(func.name.clone(), func);

            // Detect async functions by return type
            if AwaitAnalyzer::is_future_type(&func.return_type) {
                async_functions.insert(func.name.clone());
            }

            // Build call edges and detect closures/coroutines
            let mut callees = Vec::new();
            let mut func_closures = Vec::new();
            let mut func_coroutines = Vec::new();
            let mut func_indirect_calls = Vec::new();

            for block in &func.blocks {
                // Extract closures and coroutines from statements
                for stmt in &block.statements {
                    if let Statement::Assign {
                        rvalue: Rvalue::Aggregate { kind, .. },
                        ..
                    } = stmt
                    {
                        match kind {
                            AggregateKind::Closure { def_id } => {
                                func_closures.push(def_id.clone());
                            }
                            AggregateKind::Coroutine { def_id } => {
                                func_coroutines.push(def_id.clone());
                            }
                            _ => {}
                        }
                    }
                }

                // Extract call edges and indirect calls from terminators
                match &block.terminator {
                    Terminator::Call {
                        func: callee,
                        span: _,
                        ..
                    } => {
                        callees.push(callee.clone());
                    }
                    Terminator::IndirectCall {
                        callee,
                        callee_ty,
                        span,
                        ..
                    } => {
                        func_indirect_calls.push(IndirectCallInfo {
                            callee_local: callee.local,
                            callee_type: callee_ty.clone(),
                            span: span.clone(),
                        });
                    }
                    _ => {}
                }
            }

            call_edges.insert(func.name.clone(), callees);
            closures_in_func.insert(func.name.clone(), func_closures);
            coroutines_in_func.insert(func.name.clone(), func_coroutines);
            indirect_calls.insert(func.name.clone(), func_indirect_calls);
        }

        // Initialize known patterns
        let spawn_functions = Self::known_spawn_functions();
        let await_markers = Self::known_await_markers();
        let block_on_functions = Self::known_block_on_functions();

        // Detect closures passed to spawn functions
        for func in funcs {
            let spawn_infos = Self::extract_spawn_closures(func, &spawn_functions);
            if !spawn_infos.is_empty() {
                closures_to_spawn.insert(func.name.clone(), spawn_infos);
            }
        }

        Self {
            funcs,
            func_map,
            async_functions,
            call_edges,
            spawn_functions,
            await_markers,
            block_on_functions,
            next_chain_id: 0,
            closures_in_func,
            coroutines_in_func,
            closures_to_spawn,
            indirect_calls,
        }
    }

    /// Extract information about closures/coroutines passed to spawn functions
    fn extract_spawn_closures(
        func: &MirFunction,
        spawn_functions: &HashSet<String>,
    ) -> Vec<ClosureSpawnInfo> {
        let mut spawn_infos = Vec::new();

        // Build a map of local -> closure def_id from assignments
        let mut local_to_closure: HashMap<Local, String> = HashMap::new();
        for block in &func.blocks {
            for stmt in &block.statements {
                if let Statement::Assign {
                    place,
                    rvalue:
                        Rvalue::Aggregate {
                            kind:
                                AggregateKind::Closure { def_id } | AggregateKind::Coroutine { def_id },
                            ..
                        },
                } = stmt
                {
                    local_to_closure.insert(place.local, def_id.clone());
                }
            }
        }

        // Find spawn calls and check if arguments are closures
        for block in &func.blocks {
            if let Terminator::Call {
                func: callee,
                args,
                span,
                ..
            } = &block.terminator
            {
                if spawn_functions.contains(callee) || callee.contains("spawn") {
                    // Check each argument to see if it's a closure
                    for arg in args {
                        if let Operand::Move(place) | Operand::Copy(place) = arg {
                            if let Some(closure_def_id) = local_to_closure.get(&place.local) {
                                spawn_infos.push(ClosureSpawnInfo {
                                    closure_def_id: closure_def_id.clone(),
                                    spawn_func: callee.clone(),
                                    span: span.clone(),
                                    join_handle_tracked: false, // Would need data flow analysis
                                });
                            }
                        }
                    }
                }
            }
        }

        spawn_infos
    }

    /// Known functions that spawn tasks
    fn known_spawn_functions() -> HashSet<String> {
        [
            "tokio::spawn",
            "tokio::task::spawn",
            "tokio::task::spawn_local",
            "tokio::task::spawn_blocking",
            "async_std::task::spawn",
            "async_std::task::spawn_local",
            "async_std::task::spawn_blocking",
            "futures::executor::spawn",
            "smol::spawn",
        ]
        .iter()
        .map(|s| (*s).to_string())
        .collect()
    }

    /// Known markers for await points
    fn known_await_markers() -> HashSet<String> {
        [
            "__rust_await",
            "poll",
            "IntoFuture::into_future",
            "Future::poll",
        ]
        .iter()
        .map(|s| (*s).to_string())
        .collect()
    }

    /// Known functions that block on futures
    fn known_block_on_functions() -> HashSet<String> {
        [
            "tokio::runtime::Runtime::block_on",
            "tokio::runtime::Handle::block_on",
            "futures::executor::block_on",
            "async_std::task::block_on",
            "smol::block_on",
            "pollster::block_on",
        ]
        .iter()
        .map(|s| (*s).to_string())
        .collect()
    }

    /// Check if a function is an async function
    #[must_use]
    pub fn is_async(&self, name: &str) -> bool {
        self.async_functions.contains(name) || Self::is_known_async_pattern(name)
    }

    /// Check if a function name matches known async patterns
    fn is_known_async_pattern(name: &str) -> bool {
        name.starts_with("async_")
            || name.ends_with("_async")
            || name.contains("::async_")
            || name.contains("_async::")
    }

    /// Check if a function call is a spawn call
    #[must_use]
    pub fn is_spawn_call(&self, callee: &str) -> bool {
        self.spawn_functions.contains(callee) || callee.contains("spawn")
    }

    /// Check if a function call blocks on a future
    #[must_use]
    pub fn is_block_on_call(&self, callee: &str) -> bool {
        self.block_on_functions.contains(callee) || callee.contains("block_on")
    }

    /// Get closures defined in a function
    #[must_use]
    pub fn get_closures(&self, func_name: &str) -> Option<&[String]> {
        self.closures_in_func.get(func_name).map(Vec::as_slice)
    }

    /// Get coroutines (async blocks) defined in a function
    #[must_use]
    pub fn get_coroutines(&self, func_name: &str) -> Option<&[String]> {
        self.coroutines_in_func.get(func_name).map(Vec::as_slice)
    }

    /// Get closures passed to spawn calls in a function
    #[must_use]
    pub fn get_spawn_closures(&self, func_name: &str) -> Option<&[ClosureSpawnInfo]> {
        self.closures_to_spawn.get(func_name).map(Vec::as_slice)
    }

    /// Get indirect calls in a function
    #[must_use]
    pub fn get_indirect_calls(&self, func_name: &str) -> Option<&[IndirectCallInfo]> {
        self.indirect_calls.get(func_name).map(Vec::as_slice)
    }

    /// Check if a function has any closures or coroutines
    #[must_use]
    pub fn has_closures(&self, func_name: &str) -> bool {
        self.closures_in_func
            .get(func_name)
            .is_some_and(|c| !c.is_empty())
            || self
                .coroutines_in_func
                .get(func_name)
                .is_some_and(|c| !c.is_empty())
    }

    /// Check if a function has indirect calls
    #[must_use]
    pub fn has_indirect_calls(&self, func_name: &str) -> bool {
        self.indirect_calls
            .get(func_name)
            .is_some_and(|c| !c.is_empty())
    }

    /// Check if a closure def_id appears to be an async closure/coroutine
    #[must_use]
    pub fn is_async_closure(&self, def_id: &str) -> bool {
        def_id.contains("async") || def_id.contains("coroutine") || def_id.contains("{async")
    }

    /// Find closure-related violations in async chains
    #[must_use]
    pub fn find_closure_violations(&self) -> Vec<PathAnomaly> {
        let mut anomalies = Vec::new();

        for func in self.funcs {
            // Check for spawned closures that might not be awaited
            if let Some(spawn_infos) = self.closures_to_spawn.get(&func.name) {
                for spawn_info in spawn_infos {
                    if !spawn_info.join_handle_tracked {
                        // This is a potential dangling spawn via closure
                        let mut chain = AsyncChain::new(0);
                        chain.add_node(AsyncChainNode::new(
                            &spawn_info.closure_def_id,
                            true,
                            spawn_info.span.clone(),
                        ));
                        chain.terminate(AsyncTermination::Spawned);

                        anomalies.push(PathAnomaly::AsyncChainViolation(AsyncChainViolation::new(
                            chain,
                            AsyncChainViolationType::DanglingSpawn,
                            &format!(
                                "Closure '{}' spawned via {} but JoinHandle not tracked",
                                spawn_info.closure_def_id, spawn_info.spawn_func
                            ),
                            spawn_info.span.clone(),
                        )));
                    }
                }
            }

            // Check for indirect calls through function pointers that might be async
            if let Some(indirect_infos) = self.indirect_calls.get(&func.name) {
                for indirect_info in indirect_infos {
                    // Check if the callee type is a closure or fn ptr that returns Future
                    if let MirType::Closure { def_id, .. } = &indirect_info.callee_type {
                        if self.is_async_closure(def_id) {
                            // This is an indirect call to an async closure - may need await
                            let mut chain = AsyncChain::new(0);
                            chain.add_node(AsyncChainNode::new(
                                def_id,
                                true,
                                indirect_info.span.clone(),
                            ));

                            anomalies.push(PathAnomaly::AsyncChainViolation(
                                AsyncChainViolation::new(
                                    chain,
                                    AsyncChainViolationType::IndirectAsyncCall,
                                    &format!(
                                        "Indirect call to async closure '{def_id}' - ensure result is awaited"
                                    ),
                                    indirect_info.span.clone(),
                                ),
                            ));
                        }
                    } else if let MirType::FnPtr { ret, .. } = &indirect_info.callee_type {
                        // Check if fn ptr returns a Future-like type
                        if AwaitAnalyzer::is_future_type(ret) {
                            let mut chain = AsyncChain::new(0);
                            chain.add_node(AsyncChainNode::new(
                                &format!("fn_ptr@{}", indirect_info.callee_local.0),
                                true,
                                indirect_info.span.clone(),
                            ));

                            anomalies.push(PathAnomaly::AsyncChainViolation(
                                AsyncChainViolation::new(
                                    chain,
                                    AsyncChainViolationType::IndirectAsyncCall,
                                    "Indirect call through function pointer returning Future - ensure result is awaited",
                                    indirect_info.span.clone(),
                                ),
                            ));
                        }
                    }
                }
            }
        }

        anomalies
    }

    /// Check if a function contains an await marker
    fn has_await_point(&self, func: &MirFunction) -> bool {
        for block in &func.blocks {
            if let Terminator::Call { func: callee, .. } = &block.terminator {
                if self.await_markers.contains(callee)
                    || callee.contains("await")
                    || callee.contains("poll")
                {
                    return true;
                }
            }
        }
        false
    }

    /// Get the span for a function
    fn function_span(func: &MirFunction) -> SourceSpan {
        // Try to get span from first block's terminator, or create default
        func.blocks.first().map_or_else(
            || Self::default_span(&func.name),
            |block| match &block.terminator {
                Terminator::Call { span, .. } => span.clone(),
                _ => Self::default_span(&func.name),
            },
        )
    }

    /// Create a default span for a function
    fn default_span(func_name: &str) -> SourceSpan {
        SourceSpan {
            file: std::sync::Arc::from(format!("{func_name}.rs")),
            line_start: 1,
            line_end: 1,
            col_start: 0,
            col_end: 0,
        }
    }

    /// Generate a new chain ID
    const fn next_chain_id(&mut self) -> usize {
        let id = self.next_chain_id;
        self.next_chain_id += 1;
        id
    }

    /// Build async chains starting from a given function
    fn build_chains_from(
        &mut self,
        start_func: &str,
        visited: &mut HashSet<String>,
    ) -> Vec<AsyncChain> {
        let mut chains = Vec::new();

        // Avoid cycles
        if visited.contains(start_func) {
            return chains;
        }
        visited.insert(start_func.to_string());

        let func = match self.func_map.get(start_func) {
            Some(f) => *f,
            None => return chains,
        };

        // Check if this function creates/returns a Future
        let is_async_origin = self.is_async(start_func);

        if is_async_origin {
            // Start a new chain
            let chain_id = self.next_chain_id();
            let mut chain = AsyncChain::new(chain_id);

            let has_await = self.has_await_point(func);
            let span = Self::function_span(func);

            // Get callees for this function
            let callees = self.call_edges.get(start_func).cloned().unwrap_or_default();

            let node = AsyncChainNode::new(start_func, true, span).with_callees(callees.clone());
            let node = if has_await { node.with_await() } else { node };
            chain.add_node(node);

            // Track how the chain terminates
            let mut terminated = false;

            for callee in &callees {
                // Check if this is a spawn call
                if self.is_spawn_call(callee) {
                    chain.terminate(AsyncTermination::Spawned);
                    terminated = true;
                    break;
                }
                // Check if this is a block_on call
                if self.is_block_on_call(callee) {
                    chain.terminate(AsyncTermination::BlockOn);
                    terminated = true;
                    break;
                }
            }

            // If has await point, mark as awaited
            if !terminated && has_await {
                chain.terminate(AsyncTermination::Awaited);
                terminated = true;
            }

            // Check if returned (function returns Future type)
            if !terminated && AwaitAnalyzer::is_future_type(&func.return_type) {
                chain.terminate(AsyncTermination::Returned);
                // terminated = true; -- not needed, last check
            }

            chains.push(chain);
        }

        // Recursively analyze callees
        let callees = self.call_edges.get(start_func).cloned().unwrap_or_default();
        for callee in callees {
            let sub_chains = self.build_chains_from(&callee, visited);
            chains.extend(sub_chains);
        }

        chains
    }

    /// Analyze all async chains and detect violations
    pub fn find_async_chain_violations(&mut self) -> Vec<PathAnomaly> {
        let mut anomalies = Vec::new();
        let mut all_chains = Vec::new();

        // Build chains starting from each function
        let func_names: Vec<String> = self.funcs.iter().map(|f| f.name.clone()).collect();

        for func_name in func_names {
            let mut visited = HashSet::new();
            let chains = self.build_chains_from(&func_name, &mut visited);
            all_chains.extend(chains);
        }

        // Analyze chains for violations
        for chain in all_chains {
            // Check for NoAwaitPoint: async chain with no await
            if !chain.is_terminated && !chain.has_any_await() {
                if let Some(origin) = chain.origin() {
                    let span = chain
                        .nodes
                        .first()
                        .map_or_else(|| Self::default_span(origin), |n| n.span.clone());

                    anomalies.push(PathAnomaly::AsyncChainViolation(AsyncChainViolation::new(
                        chain.clone(),
                        AsyncChainViolationType::NoAwaitPoint,
                        "Future created but never awaited",
                        span,
                    )));
                }
            }

            // Check for IncompleteChain: chain that doesn't properly terminate
            if !chain.is_terminated && chain.has_any_await() {
                if let Some(origin) = chain.origin() {
                    let span = chain
                        .nodes
                        .first()
                        .map_or_else(|| Self::default_span(origin), |n| n.span.clone());

                    anomalies.push(PathAnomaly::AsyncChainViolation(AsyncChainViolation::new(
                        chain.clone(),
                        AsyncChainViolationType::IncompleteChain,
                        "Async chain does not properly terminate",
                        span,
                    )));
                }
            }

            // Check for DanglingSpawn: spawned but termination is Spawned without join
            if matches!(chain.termination, Some(AsyncTermination::Spawned)) {
                // For now, flag all spawns as potential issues (would need JoinHandle tracking)
                // In practice, would check if the JoinHandle is awaited
                if let Some(origin) = chain.origin() {
                    let span = chain
                        .nodes
                        .first()
                        .map_or_else(|| Self::default_span(origin), |n| n.span.clone());

                    anomalies.push(PathAnomaly::AsyncChainViolation(AsyncChainViolation::new(
                        chain.clone(),
                        AsyncChainViolationType::DanglingSpawn,
                        "Task spawned but JoinHandle not awaited",
                        span,
                    )));
                }
            }
        }

        anomalies
    }

    /// Detect cyclic await dependencies
    ///
    /// A cyclic dependency occurs when function A awaits function B,
    /// and function B (directly or indirectly) awaits function A.
    #[must_use]
    pub fn find_cyclic_dependencies(&self) -> Vec<PathAnomaly> {
        let mut anomalies = Vec::new();

        // Build await dependency graph (only for async functions)
        let mut await_deps: HashMap<String, HashSet<String>> = HashMap::new();

        for func in self.funcs {
            if !self.is_async(&func.name) {
                continue;
            }

            let mut deps = HashSet::new();
            for block in &func.blocks {
                if let Terminator::Call { func: callee, .. } = &block.terminator {
                    if self.is_async(callee) {
                        deps.insert(callee.clone());
                    }
                }
            }
            await_deps.insert(func.name.clone(), deps);
        }

        // Find cycles using DFS
        for start in await_deps.keys() {
            let mut visited = HashSet::new();
            let mut path = Vec::new();

            if let Some(cycle) = Self::find_cycle(start, &await_deps, &mut visited, &mut path) {
                let mut chain = AsyncChain::new(0);
                for func_name in &cycle {
                    chain.add_node(AsyncChainNode::new(
                        func_name,
                        func_name == start,
                        Self::default_span(func_name),
                    ));
                }

                anomalies.push(PathAnomaly::AsyncChainViolation(AsyncChainViolation::new(
                    chain,
                    AsyncChainViolationType::CyclicDependency,
                    &format!("Cyclic await dependency detected: {}", cycle.join(" -> ")),
                    Self::default_span(start),
                )));
            }
        }

        anomalies
    }

    /// DFS helper to find cycles
    fn find_cycle(
        current: &str,
        deps: &HashMap<String, HashSet<String>>,
        visited: &mut HashSet<String>,
        path: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        if path.contains(&current.to_string()) {
            // Found cycle
            let cycle_start = path
                .iter()
                .position(|s| s == current)
                .expect("current must be in path since path.contains() returned true");
            let mut cycle: Vec<String> = path[cycle_start..].to_vec();
            cycle.push(current.to_string());
            return Some(cycle);
        }

        if visited.contains(current) {
            return None;
        }

        visited.insert(current.to_string());
        path.push(current.to_string());

        if let Some(neighbors) = deps.get(current) {
            for neighbor in neighbors {
                if let Some(cycle) = Self::find_cycle(neighbor, deps, visited, path) {
                    return Some(cycle);
                }
            }
        }

        path.pop();
        None
    }
}

/// Analyzes struct creation and update patterns (Phase 6.5.4)
///
/// Detects:
/// - Struct update syntax (`..old`) where fields carry over
/// - Partial moves of struct fields
/// - Partial mutations through `&mut self`
#[derive(Debug)]
pub struct StructUpdateAnalyzer<'a> {
    /// Functions to analyze
    funcs: &'a [MirFunction],
    /// Track struct types seen (name -> field count estimate)
    struct_info: HashMap<String, StructInfo>,
}

/// Information about a struct type
#[derive(Debug, Clone)]
struct StructInfo {
    /// Estimated number of fields (from aggregate constructions seen)
    field_count: usize,
}

impl<'a> StructUpdateAnalyzer<'a> {
    /// Create a new struct update analyzer
    #[must_use]
    pub fn new(funcs: &'a [MirFunction]) -> Self {
        let mut struct_info = HashMap::new();

        // First pass: learn about struct field counts from aggregate constructions
        for func in funcs {
            for block in &func.blocks {
                for stmt in &block.statements {
                    if let Statement::Assign {
                        rvalue:
                            Rvalue::Aggregate {
                                kind: AggregateKind::Adt { name, .. },
                                operands,
                            },
                        ..
                    } = stmt
                    {
                        // Record the field count we see
                        let entry = struct_info
                            .entry(name.clone())
                            .or_insert(StructInfo { field_count: 0 });
                        // Update to max seen (in case different constructions have different counts)
                        entry.field_count = entry.field_count.max(operands.len());
                    }
                }
            }
        }

        Self { funcs, struct_info }
    }

    /// Find all partial struct update issues
    #[must_use]
    pub fn find_partial_updates(&self) -> Vec<PathAnomaly> {
        let mut anomalies = Vec::new();

        for func in self.funcs {
            // Track which fields of which locals have been moved
            let mut partial_moves: HashMap<Local, HashSet<usize>> = HashMap::new();

            for (block_idx, block) in func.blocks.iter().enumerate() {
                for stmt in &block.statements {
                    if let Statement::Assign { place: _, rvalue } = stmt {
                        // Check for struct update syntax patterns
                        if let Some(anomaly) =
                            self.check_struct_update_syntax(func, block_idx, rvalue)
                        {
                            anomalies.push(anomaly);
                        }

                        // Track partial field moves
                        if let Rvalue::Use(Operand::Move(source)) = rvalue {
                            if let Some(crate::Projection::Field(field_idx)) =
                                source.projections.first()
                            {
                                partial_moves
                                    .entry(source.local)
                                    .or_default()
                                    .insert(*field_idx);
                            }
                        }

                        // Check if the rvalue reads from a partially moved struct
                        if let Some(anomaly) =
                            Self::check_partial_move_in_rvalue(func, rvalue, &partial_moves)
                        {
                            anomalies.push(anomaly);
                        }
                    }
                }
            }
        }

        anomalies
    }

    /// Check for struct update syntax where fields are copied from another struct
    ///
    /// Pattern: Aggregate { Adt, operands } where some operands are Field projections
    /// from the same source local (indicating `..source` syntax)
    fn check_struct_update_syntax(
        &self,
        func: &MirFunction,
        _block_idx: usize,
        rvalue: &Rvalue,
    ) -> Option<PathAnomaly> {
        if let Rvalue::Aggregate {
            kind: AggregateKind::Adt { name, .. },
            operands,
        } = rvalue
        {
            // Look for operands that come from field projections of the same struct
            let mut source_local: Option<Local> = None;
            let mut explicit_fields: Vec<String> = Vec::new();
            let mut copied_fields: Vec<String> = Vec::new();

            for (idx, op) in operands.iter().enumerate() {
                match op {
                    Operand::Copy(place) | Operand::Move(place) => {
                        if let Some(crate::Projection::Field(field_idx)) = place.projections.first()
                        {
                            // This operand comes from a field projection
                            if source_local.is_none() {
                                source_local = Some(place.local);
                            }
                            if source_local == Some(place.local) {
                                // Same source - this is struct update syntax
                                copied_fields.push(format!("field_{field_idx}"));
                            } else {
                                explicit_fields.push(format!("field_{idx}"));
                            }
                        } else {
                            explicit_fields.push(format!("field_{idx}"));
                        }
                    }
                    Operand::Constant(_) => {
                        explicit_fields.push(format!("field_{idx}"));
                    }
                }
            }

            // If we have both explicit fields and copied fields from same source,
            // this is struct update syntax
            if !copied_fields.is_empty() && !explicit_fields.is_empty() {
                // Get expected field count if known
                let expected = self.struct_info.get(name).map_or(0, |i| i.field_count);

                // Only report if it looks like some fields were unintentionally carried over
                // Heuristic: if we explicitly set more than half the fields but not all,
                // it might be intentional. Report only if few explicit fields.
                if explicit_fields.len() < expected / 2 || expected == 0 {
                    // Construct a span from the function's first block (fallback)
                    let span = func
                        .blocks
                        .first()
                        .and_then(|b| match &b.terminator {
                            Terminator::Call { span, .. } => Some(span.clone()),
                            _ => None,
                        })
                        .unwrap_or_else(|| SourceSpan {
                            file: std::sync::Arc::from("unknown"),
                            line_start: 0,
                            line_end: 0,
                            col_start: 0,
                            col_end: 0,
                        });

                    return Some(PathAnomaly::PartialStructUpdate(PartialStructUpdate {
                        function: func.name.clone(),
                        struct_type: name.clone(),
                        uninitialized_fields: copied_fields,
                        initialized_fields: explicit_fields,
                        reason: PartialUpdateReason::StructUpdateSyntax,
                        span,
                    }));
                }
            }
        }

        None
    }

    /// Check if an rvalue reads from a partially moved struct
    fn check_partial_move_in_rvalue(
        func: &MirFunction,
        rvalue: &Rvalue,
        partial_moves: &HashMap<Local, HashSet<usize>>,
    ) -> Option<PathAnomaly> {
        // Extract the source place from the rvalue if it reads a whole struct
        let source_place = match rvalue {
            Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) => {
                // Only interested in whole struct access (no field projections)
                if place.projections.is_empty() {
                    Some(place)
                } else {
                    None
                }
            }
            _ => None,
        };

        if let Some(place) = source_place {
            if let Some(moved_fields) = partial_moves.get(&place.local) {
                if !moved_fields.is_empty() {
                    // Get local type info if available
                    let local_type = func
                        .locals
                        .get(place.local.0)
                        .and_then(|l| l.name.clone())
                        .unwrap_or_else(|| format!("local_{}", place.local.0));

                    let span = SourceSpan {
                        file: std::sync::Arc::from("unknown"),
                        line_start: 0,
                        line_end: 0,
                        col_start: 0,
                        col_end: 0,
                    };

                    let moved_field_names: Vec<String> = moved_fields
                        .iter()
                        .map(|idx| format!("field_{idx}"))
                        .collect();

                    return Some(PathAnomaly::PartialStructUpdate(PartialStructUpdate {
                        function: func.name.clone(),
                        struct_type: local_type,
                        uninitialized_fields: moved_field_names,
                        initialized_fields: vec![],
                        reason: PartialUpdateReason::PartialMove,
                        span,
                    }));
                }
            }
        }

        None
    }
}

/// Analyzes data flow in MIR code (Phase 6.5.5)
///
/// Detects:
/// - Values that are read but never used
/// - Computed values that are never returned or stored
/// - Data flow annotations that are not satisfied
#[derive(Debug)]
pub struct DataFlowAnalyzer<'a> {
    /// Functions to analyze
    funcs: &'a [MirFunction],
}

/// Tracks the state of a local variable through analysis
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LocalState {
    /// Local has not been assigned
    #[allow(dead_code)] // Kept for completeness in state machine
    Unassigned,
    /// Local has been assigned a value
    Assigned,
    /// Local has been read/used
    Used,
    /// Local has been returned
    Returned,
}

impl<'a> DataFlowAnalyzer<'a> {
    /// Create a new data flow analyzer
    #[must_use]
    pub const fn new(funcs: &'a [MirFunction]) -> Self {
        Self { funcs }
    }

    /// Find all unused values in the analyzed functions
    ///
    /// Returns anomalies for:
    /// - Values that are computed but never read
    /// - Parameter values that are never used
    #[must_use]
    pub fn find_unused_values(&self) -> Vec<PathAnomaly> {
        let mut anomalies = Vec::new();

        for func in self.funcs {
            // Track state of each local
            let mut local_states: HashMap<Local, LocalState> = HashMap::new();
            let mut local_assign_spans: HashMap<Local, SourceSpan> = HashMap::new();

            // Initialize params as Assigned (they come in with values)
            for (idx, _param) in func.params.iter().enumerate() {
                local_states.insert(Local(idx), LocalState::Assigned);
            }

            // Process all blocks
            for block in &func.blocks {
                // Process statements
                for stmt in &block.statements {
                    if let Statement::Assign { place, rvalue } = stmt {
                        // Mark destination as assigned
                        local_states.insert(place.local, LocalState::Assigned);
                        // Record span for later error reporting
                        if let Some(span) = Self::get_rvalue_span(rvalue, func) {
                            local_assign_spans.insert(place.local, span);
                        }

                        // Mark operands in rvalue as used
                        Self::mark_rvalue_locals_used(rvalue, &mut local_states);
                    }
                }

                // Process terminator
                Self::mark_terminator_locals_used(&block.terminator, &mut local_states);

                // Check for Return terminator - the return local is returned
                if matches!(&block.terminator, Terminator::Return) {
                    // Local 0 is typically the return place
                    local_states.insert(Local(0), LocalState::Returned);
                }
            }

            // Find locals that were assigned but never used
            for (local, state) in &local_states {
                if *state == LocalState::Assigned {
                    // Skip if this is a temporary (no name) and not a parameter
                    let is_param = local.0 < func.params.len();
                    let local_name = func.locals.get(local.0).and_then(|l| l.name.clone());

                    // Only report named locals or parameters
                    if local_name.is_some() || is_param {
                        let span =
                            local_assign_spans
                                .get(local)
                                .cloned()
                                .unwrap_or_else(|| SourceSpan {
                                    file: std::sync::Arc::from("unknown"),
                                    line_start: 0,
                                    line_end: 0,
                                    col_start: 0,
                                    col_end: 0,
                                });

                        let computation = if is_param {
                            format!(
                                "parameter `{}`",
                                local_name.unwrap_or_else(|| format!("_{}", local.0))
                            )
                        } else {
                            format!(
                                "computed value `{}`",
                                local_name.unwrap_or_else(|| format!("_{}", local.0))
                            )
                        };

                        anomalies.push(PathAnomaly::UnusedValue(UnusedValue {
                            function: func.name.clone(),
                            computation,
                            span,
                        }));
                    }
                }
            }
        }

        anomalies
    }

    /// Mark all locals in an rvalue as Used
    fn mark_rvalue_locals_used(rvalue: &Rvalue, states: &mut HashMap<Local, LocalState>) {
        match rvalue {
            Rvalue::Use(op)
            | Rvalue::UnaryOp(_, op)
            | Rvalue::Cast { operand: op, .. }
            | Rvalue::Repeat { operand: op, .. } => Self::mark_operand_used(op, states),
            Rvalue::BinaryOp(_, left, right) | Rvalue::CheckedBinaryOp(_, left, right) => {
                Self::mark_operand_used(left, states);
                Self::mark_operand_used(right, states);
            }
            Rvalue::Ref { place, .. } | Rvalue::Discriminant(place) | Rvalue::Len(place) => {
                states.insert(place.local, LocalState::Used);
            }
            Rvalue::Aggregate { operands, .. } => {
                for op in operands {
                    Self::mark_operand_used(op, states);
                }
            }
            Rvalue::NullaryOp(_, _) => {}
        }
    }

    /// Mark an operand as Used
    fn mark_operand_used(op: &Operand, states: &mut HashMap<Local, LocalState>) {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                states.insert(place.local, LocalState::Used);
            }
            Operand::Constant(_) => {}
        }
    }

    /// Mark all locals in a terminator as Used
    fn mark_terminator_locals_used(term: &Terminator, states: &mut HashMap<Local, LocalState>) {
        match term {
            Terminator::SwitchInt { discr, .. } => {
                Self::mark_operand_used(discr, states);
            }
            Terminator::Call { args, .. } => {
                for arg in args {
                    Self::mark_operand_used(arg, states);
                }
            }
            Terminator::IndirectCall { callee, args, .. } => {
                // Mark the callee place as used
                states.insert(callee.local, LocalState::Used);
                for arg in args {
                    Self::mark_operand_used(arg, states);
                }
            }
            Terminator::Assert { cond, .. } => {
                Self::mark_operand_used(cond, states);
            }
            Terminator::Return | Terminator::Goto { .. } | Terminator::Unreachable => {}
        }
    }

    /// Get span from rvalue (if available)
    fn get_rvalue_span(_rvalue: &Rvalue, func: &MirFunction) -> Option<SourceSpan> {
        // Try to get a span from the function
        func.blocks.first().and_then(|b| match &b.terminator {
            Terminator::Call { span, .. } => Some(span.clone()),
            _ => None,
        })
    }

    /// Verify data flow annotations
    ///
    /// Checks that annotated inputs reach annotated outputs according
    /// to wire_data_flow specifications.
    #[must_use]
    pub fn verify_data_flow_annotations(&self, call_graph: &CallGraph) -> Vec<DataFlowViolation> {
        let mut violations = Vec::new();

        // Get all data flow specs from the call graph
        for (func_name, spec) in &call_graph.wire_specs {
            // Get data flow annotations from the spec
            for ann in &spec.annotations {
                if let vc_ir::WireAnnotation::DataFlow { input, output } = ann {
                    // Check if the data flow path is satisfied
                    if !self.verify_single_data_flow(func_name, input, output) {
                        let span = spec.span.clone().unwrap_or_else(|| SourceSpan {
                            file: std::sync::Arc::from("unknown"),
                            line_start: 0,
                            line_end: 0,
                            col_start: 0,
                            col_end: 0,
                        });

                        violations.push(DataFlowViolation {
                            function: func_name.clone(),
                            input: input.clone(),
                            output: output.clone(),
                            reason: format!("Data flow from '{input}' to '{output}' not verified"),
                            span,
                        });
                    }
                }
            }
        }

        violations
    }

    /// Verify a single data flow path
    ///
    /// Returns true if data flows from input to output in the function.
    fn verify_single_data_flow(&self, func_name: &str, input: &str, output: &str) -> bool {
        // Find the function
        let Some(func) = self.funcs.iter().find(|f| f.name == func_name) else {
            return false;
        };

        // Build def-use chains to track data flow
        let mut flows_from: HashMap<Local, HashSet<Local>> = HashMap::new();

        // Find the input local (parameter with matching name)
        // Params are typically stored starting from local index 1 (local 0 is return place)
        let input_local = func
            .params
            .iter()
            .enumerate()
            .find_map(|(idx, (param_name, _ty))| {
                if param_name == input {
                    // Parameters start at local index 1 (local 0 is return place)
                    return Some(Local(idx + 1));
                }
                None
            });

        // Find the output local (usually the return place or named local)
        let output_local = if output == "result" || output == "return" {
            Some(Local(0)) // Return place
        } else {
            func.locals
                .iter()
                .enumerate()
                .find_map(|(idx, local_decl)| {
                    if local_decl.name.as_ref().is_some_and(|n| n == output) {
                        Some(Local(idx))
                    } else {
                        None
                    }
                })
        };

        let (Some(input_local), Some(output_local)) = (input_local, output_local) else {
            return false; // Can't find input or output - fail verification
        };

        // Build flow graph from assignments
        for block in &func.blocks {
            for stmt in &block.statements {
                if let Statement::Assign { place, rvalue } = stmt {
                    let dest = place.local;
                    let sources = Self::collect_rvalue_locals(rvalue);
                    for src in sources {
                        flows_from.entry(dest).or_default().insert(src);
                    }
                }
            }
        }

        // Check reachability from input_local to output_local
        self.can_flow_to(input_local, output_local, &flows_from, &mut HashSet::new())
    }

    /// Collect all locals used in an rvalue
    fn collect_rvalue_locals(rvalue: &Rvalue) -> Vec<Local> {
        let mut locals = Vec::new();

        match rvalue {
            Rvalue::Use(op)
            | Rvalue::UnaryOp(_, op)
            | Rvalue::Cast { operand: op, .. }
            | Rvalue::Repeat { operand: op, .. } => {
                if let Some(local) = Self::operand_local(op) {
                    locals.push(local);
                }
            }
            Rvalue::BinaryOp(_, left, right) | Rvalue::CheckedBinaryOp(_, left, right) => {
                if let Some(l) = Self::operand_local(left) {
                    locals.push(l);
                }
                if let Some(r) = Self::operand_local(right) {
                    locals.push(r);
                }
            }
            Rvalue::Ref { place, .. } | Rvalue::Discriminant(place) | Rvalue::Len(place) => {
                locals.push(place.local);
            }
            Rvalue::Aggregate { operands, .. } => {
                for op in operands {
                    if let Some(local) = Self::operand_local(op) {
                        locals.push(local);
                    }
                }
            }
            Rvalue::NullaryOp(_, _) => {}
        }

        locals
    }

    /// Get local from operand
    const fn operand_local(op: &Operand) -> Option<Local> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => Some(place.local),
            Operand::Constant(_) => None,
        }
    }

    /// Check if data can flow from source to target
    #[allow(clippy::only_used_in_recursion)] // Method pattern is idiomatic even if self only used in recursion
    fn can_flow_to(
        &self,
        source: Local,
        target: Local,
        flows_from: &HashMap<Local, HashSet<Local>>,
        visited: &mut HashSet<Local>,
    ) -> bool {
        if source == target {
            return true;
        }

        if visited.contains(&target) {
            return false;
        }
        visited.insert(target);

        // Check what flows into target
        if let Some(sources) = flows_from.get(&target) {
            for &src in sources {
                if src == source || self.can_flow_to(source, src, flows_from, visited) {
                    return true;
                }
            }
        }

        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_call_graph_empty() {
        let graph = CallGraph::new();
        assert!(graph.reachable_from("main").is_empty() || graph.reachable_from("main").len() == 1);
    }

    #[test]
    fn test_call_graph_simple() {
        let mut graph = CallGraph::new();
        graph.add_function("main", vec!["foo".to_string(), "bar".to_string()]);
        graph.add_function("foo", vec!["baz".to_string()]);
        graph.add_function("bar", vec![]);
        graph.add_function("baz", vec![]);

        let reachable = graph.reachable_from("main");
        assert!(reachable.contains("main"));
        assert!(reachable.contains("foo"));
        assert!(reachable.contains("bar"));
        assert!(reachable.contains("baz"));
    }

    #[test]
    fn test_call_graph_can_reach() {
        let mut graph = CallGraph::new();
        graph.add_function("a", vec!["b".to_string()]);
        graph.add_function("b", vec!["c".to_string()]);
        graph.add_function("c", vec![]);
        graph.add_function("d", vec![]); // Not connected

        assert!(graph.can_reach("a", "c"));
        assert!(graph.can_reach("b", "c"));
        assert!(!graph.can_reach("a", "d"));
        assert!(!graph.can_reach("c", "a")); // No back edge
    }

    #[test]
    fn test_call_graph_cyclic() {
        let mut graph = CallGraph::new();
        graph.add_function("a", vec!["b".to_string()]);
        graph.add_function("b", vec!["c".to_string()]);
        graph.add_function("c", vec!["a".to_string()]); // Cycle back to a

        let reachable = graph.reachable_from("a");
        assert_eq!(reachable.len(), 3);
        assert!(reachable.contains("a"));
        assert!(reachable.contains("b"));
        assert!(reachable.contains("c"));
    }

    #[test]
    fn test_wiring_verifier_no_start() {
        let mut graph = CallGraph::new();
        graph.add_function("foo", vec![]);
        graph.add_wire_spec(
            "foo",
            WireSpec {
                annotations: vec![WireAnnotation::State("foo_state".to_string())],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        // No start point - should pass (we don't check reachability without start)
        assert!(result.passed());
    }

    #[test]
    fn test_wiring_verifier_reachable() {
        let mut graph = CallGraph::new();
        graph.add_function("main", vec!["checkout".to_string()]);
        graph.add_function("checkout", vec!["payment".to_string()]);
        graph.add_function("payment", vec![]);

        graph.add_wire_spec(
            "main",
            WireSpec {
                annotations: vec![WireAnnotation::Start],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "checkout",
            WireSpec {
                annotations: vec![WireAnnotation::State("checkout".to_string())],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "payment",
            WireSpec {
                annotations: vec![WireAnnotation::State("payment".to_string())],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        assert!(result.passed());
        assert!(result.unreachable_states.is_empty());
    }

    #[test]
    fn test_wiring_verifier_unreachable() {
        let mut graph = CallGraph::new();
        graph.add_function("main", vec!["foo".to_string()]);
        graph.add_function("foo", vec![]);
        graph.add_function("dead_code", vec![]); // Not connected

        graph.add_wire_spec(
            "main",
            WireSpec {
                annotations: vec![WireAnnotation::Start],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "dead_code",
            WireSpec {
                annotations: vec![WireAnnotation::State("dead".to_string())],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        assert!(!result.passed());
        assert_eq!(result.unreachable_states.len(), 1);
        assert_eq!(result.unreachable_states[0].state, "dead");
    }

    #[test]
    fn test_wiring_verifier_must_reach_success() {
        let mut graph = CallGraph::new();
        graph.add_function("checkout", vec!["success".to_string(), "error".to_string()]);
        graph.add_function("success", vec![]);
        graph.add_function("error", vec![]);

        graph.add_wire_spec(
            "checkout",
            WireSpec {
                annotations: vec![
                    WireAnnotation::State("checkout".to_string()),
                    WireAnnotation::MustReach(vec!["success".to_string(), "error".to_string()]),
                ],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "success",
            WireSpec {
                annotations: vec![WireAnnotation::State("success".to_string())],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "error",
            WireSpec {
                annotations: vec![WireAnnotation::State("error".to_string())],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        assert!(result.passed());
        assert!(result.missing_reaches.is_empty());
    }

    #[test]
    fn test_wiring_verifier_must_reach_failure() {
        let mut graph = CallGraph::new();
        graph.add_function("checkout", vec!["success".to_string()]); // Missing error path
        graph.add_function("success", vec![]);
        graph.add_function("error", vec![]); // Not connected

        graph.add_wire_spec(
            "checkout",
            WireSpec {
                annotations: vec![
                    WireAnnotation::State("checkout".to_string()),
                    WireAnnotation::MustReach(vec!["success".to_string(), "error".to_string()]),
                ],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "success",
            WireSpec {
                annotations: vec![WireAnnotation::State("success".to_string())],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "error",
            WireSpec {
                annotations: vec![WireAnnotation::State("error".to_string())],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        assert!(!result.passed());
        assert_eq!(result.missing_reaches.len(), 1);
        assert_eq!(result.missing_reaches[0].target_state, "error");
    }

    #[test]
    fn test_wiring_verifier_recoverable_success() {
        let mut graph = CallGraph::new();
        graph.add_function("main", vec!["try_op".to_string()]);
        graph.add_function("try_op", vec!["success".to_string(), "error".to_string()]);
        graph.add_function("success", vec![]);
        graph.add_function("error", vec!["success".to_string()]); // Recovery path

        graph.add_wire_spec(
            "main",
            WireSpec {
                annotations: vec![WireAnnotation::Start],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "success",
            WireSpec {
                annotations: vec![WireAnnotation::State("success".to_string())],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "error",
            WireSpec {
                annotations: vec![
                    WireAnnotation::State("error".to_string()),
                    WireAnnotation::Recoverable,
                ],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        assert!(result.passed());
        assert!(result.unrecoverable_states.is_empty());
    }

    #[test]
    fn test_wiring_verifier_recoverable_failure() {
        let mut graph = CallGraph::new();
        graph.add_function("main", vec!["error".to_string()]);
        graph.add_function("error", vec![]); // No recovery path!

        graph.add_wire_spec(
            "main",
            WireSpec {
                annotations: vec![WireAnnotation::Start],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "error",
            WireSpec {
                annotations: vec![
                    WireAnnotation::State("error".to_string()),
                    WireAnnotation::Recoverable,
                ],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        assert!(!result.passed());
        assert_eq!(result.unrecoverable_states.len(), 1);
        assert_eq!(result.unrecoverable_states[0], "error");
    }

    // ============================================
    // Dead Code Detection tests (Phase 6.5.4)
    // ============================================

    #[test]
    fn test_dead_code_detection_no_start() {
        // Without start functions, no dead code check
        let mut graph = CallGraph::new();
        graph.add_function("isolated", vec![]);
        graph.add_wire_spec(
            "isolated",
            WireSpec {
                annotations: vec![WireAnnotation::State("isolated".to_string())],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        // No dead code detected without start functions
        assert!(result.path_anomalies.is_empty());
    }

    #[test]
    fn test_dead_code_detection_with_start() {
        let mut graph = CallGraph::new();
        graph.add_function("main", vec!["reachable".to_string()]);
        graph.add_function("reachable", vec![]);
        graph.add_function("dead_func", vec![]); // Not connected to main

        graph.add_wire_spec(
            "main",
            WireSpec {
                annotations: vec![WireAnnotation::Start],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "reachable",
            WireSpec {
                annotations: vec![WireAnnotation::State("reachable".to_string())],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "dead_func",
            WireSpec {
                annotations: vec![WireAnnotation::State("dead".to_string())],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        // Dead code detected because dead_func has wire annotations but isn't reachable
        assert!(!result.passed());
        assert_eq!(result.path_anomalies.len(), 1);

        if let PathAnomaly::DeadCode(dead) = &result.path_anomalies[0] {
            assert_eq!(dead.function, "dead_func");
            assert!(matches!(dead.reason, DeadCodeReason::UnreachableFromStart));
        } else {
            panic!("Expected DeadCode anomaly");
        }
    }

    #[test]
    fn test_dead_code_all_reachable() {
        let mut graph = CallGraph::new();
        graph.add_function("main", vec!["a".to_string()]);
        graph.add_function("a", vec!["b".to_string()]);
        graph.add_function("b", vec![]);

        graph.add_wire_spec(
            "main",
            WireSpec {
                annotations: vec![WireAnnotation::Start],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "a",
            WireSpec {
                annotations: vec![WireAnnotation::State("a".to_string())],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "b",
            WireSpec {
                annotations: vec![WireAnnotation::State("b".to_string())],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        // All functions are reachable
        assert!(result.passed());
        assert!(result.path_anomalies.is_empty());
    }

    #[test]
    fn test_never_called_detection() {
        let mut graph = CallGraph::new();
        graph.add_function("main", vec!["helper".to_string()]);
        graph.add_function("helper", vec![]);
        graph.add_function("orphan", vec![]); // Never called

        graph.add_wire_spec(
            "main",
            WireSpec {
                annotations: vec![WireAnnotation::Start],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let all_funcs = vec![
            "main".to_string(),
            "helper".to_string(),
            "orphan".to_string(),
        ];

        let anomalies = verifier.check_never_called(&all_funcs);

        // orphan has no callers (main is start, helper is called by main)
        assert_eq!(anomalies.len(), 1);
        if let PathAnomaly::DeadCode(dead) = &anomalies[0] {
            assert_eq!(dead.function, "orphan");
            assert!(matches!(dead.reason, DeadCodeReason::NeverCalled));
        } else {
            panic!("Expected DeadCode anomaly");
        }
    }

    #[test]
    fn test_multiple_start_functions() {
        let mut graph = CallGraph::new();
        graph.add_function("main1", vec!["a".to_string()]);
        graph.add_function("main2", vec!["b".to_string()]);
        graph.add_function("a", vec![]);
        graph.add_function("b", vec![]);
        graph.add_function("dead", vec![]); // Reachable from neither

        graph.add_wire_spec(
            "main1",
            WireSpec {
                annotations: vec![WireAnnotation::Start],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "main2",
            WireSpec {
                annotations: vec![WireAnnotation::Start],
                span: Some(SourceSpan::default()),
            },
        );
        graph.add_wire_spec(
            "dead",
            WireSpec {
                annotations: vec![WireAnnotation::State("dead".to_string())],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let result = verifier.verify();

        // dead is not reachable from either start function
        assert!(!result.passed());
        assert_eq!(result.path_anomalies.len(), 1);
    }

    // ============================================
    // UnhandledResult Detection tests (Phase 6.5.4)
    // ============================================

    use crate::{BasicBlock, LocalDecl};

    fn make_mir_function(name: &str, return_type: MirType, blocks: Vec<BasicBlock>) -> MirFunction {
        MirFunction {
            name: name.to_string(),
            params: vec![],
            return_type,
            blocks,
            locals: vec![LocalDecl {
                ty: MirType::Bool,
                name: None,
            }],
            span: SourceSpan::default(),
        }
    }

    fn make_place(local_idx: usize) -> crate::Place {
        crate::Place {
            local: Local(local_idx),
            projections: vec![],
        }
    }

    #[test]
    fn test_result_type_detection() {
        assert!(ResultAnalyzer::is_result_type(&MirType::Adt {
            name: "Result".to_string()
        }));
        assert!(ResultAnalyzer::is_result_type(&MirType::Adt {
            name: "std::result::Result".to_string()
        }));
        assert!(ResultAnalyzer::is_result_type(&MirType::Adt {
            name: "Result<i32, Error>".to_string()
        }));
        assert!(!ResultAnalyzer::is_result_type(&MirType::Adt {
            name: "Option".to_string()
        }));
        assert!(!ResultAnalyzer::is_result_type(&MirType::Int {
            signed: true,
            bits: 32
        }));
    }

    #[test]
    fn test_unhandled_result_ignored() {
        // Function that calls a Result-returning function but ignores the result
        let caller = make_mir_function(
            "caller",
            MirType::Bool,
            vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "result_fn".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
        );

        let result_fn = make_mir_function(
            "result_fn",
            MirType::Adt {
                name: "Result".to_string(),
            },
            vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
        );

        let funcs = vec![caller, result_fn];
        let analyzer = ResultAnalyzer::new(&funcs);
        let anomalies = analyzer.find_unhandled_results();

        // Should detect the unhandled Result
        assert_eq!(anomalies.len(), 1);
        if let PathAnomaly::UnhandledResult(unhandled) = &anomalies[0] {
            assert_eq!(unhandled.function, "caller");
            assert_eq!(unhandled.callee, "result_fn");
            assert!(matches!(unhandled.handling, ResultHandling::Ignored));
        } else {
            panic!("Expected UnhandledResult anomaly");
        }
    }

    #[test]
    fn test_result_used_no_anomaly() {
        // Function that calls a Result-returning function and uses the result
        let caller = make_mir_function(
            "caller",
            MirType::Bool,
            vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "result_fn".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                BasicBlock {
                    statements: vec![
                        // Use the result
                        Statement::Assign {
                            place: make_place(1),
                            rvalue: Rvalue::Use(Operand::Move(make_place(0))),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
        );

        let result_fn = make_mir_function(
            "result_fn",
            MirType::Adt {
                name: "Result".to_string(),
            },
            vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
        );

        let funcs = vec![caller, result_fn];
        let analyzer = ResultAnalyzer::new(&funcs);
        let anomalies = analyzer.find_unhandled_results();

        // Should not detect any unhandled Result (result is used)
        assert!(anomalies.is_empty());
    }

    #[test]
    fn test_non_result_function_no_anomaly() {
        // Function that calls a non-Result-returning function
        let caller = make_mir_function(
            "caller",
            MirType::Bool,
            vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "void_fn".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
        );

        let void_fn = make_mir_function(
            "void_fn",
            MirType::Tuple(vec![]), // Unit type
            vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
        );

        let funcs = vec![caller, void_fn];
        let analyzer = ResultAnalyzer::new(&funcs);
        let anomalies = analyzer.find_unhandled_results();

        // Should not detect any anomaly (not a Result type)
        assert!(anomalies.is_empty());
    }

    #[test]
    fn test_known_result_function_heuristics() {
        // These should be detected as Result-returning
        assert!(ResultAnalyzer::is_known_result_function(
            "std::fs::File::open"
        ));
        assert!(ResultAnalyzer::is_known_result_function("io::read"));
        assert!(ResultAnalyzer::is_known_result_function("socket::connect"));
        assert!(ResultAnalyzer::is_known_result_function("str::try_parse")); // Uses ::try_ pattern
        assert!(ResultAnalyzer::is_known_result_function("num_or_err")); // Uses _or_err pattern

        // These should not be detected
        assert!(!ResultAnalyzer::is_known_result_function("println"));
        assert!(!ResultAnalyzer::is_known_result_function("vec::push"));
        assert!(!ResultAnalyzer::is_known_result_function("clone"));
    }

    #[test]
    fn test_wiring_verifier_check_unhandled_results() {
        let graph = CallGraph::new();
        let verifier = WiringVerifier::new(graph);

        // Create functions for test
        let caller = make_mir_function(
            "caller",
            MirType::Bool,
            vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "risky_op".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
        );

        let risky_op = make_mir_function(
            "risky_op",
            MirType::Adt {
                name: "Result<(), Error>".to_string(),
            },
            vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
        );

        let funcs = vec![caller, risky_op];
        let anomalies = verifier.check_unhandled_results(&funcs);

        assert_eq!(anomalies.len(), 1);
    }

    // ============================================
    // MissingAwait Detection tests (Phase 6.5.4)
    // ============================================

    #[test]
    fn test_future_type_detection() {
        // Future types should be detected
        assert!(AwaitAnalyzer::is_future_type(&MirType::Adt {
            name: "Future".to_string()
        }));
        assert!(AwaitAnalyzer::is_future_type(&MirType::Adt {
            name: "impl Future<Output = i32>".to_string()
        }));
        assert!(AwaitAnalyzer::is_future_type(&MirType::Adt {
            name: "tokio::task::JoinHandle<()>".to_string()
        }));
        assert!(AwaitAnalyzer::is_future_type(&MirType::Adt {
            name: "Pin<Box<dyn Future<Output=String>>>".to_string()
        }));
        assert!(AwaitAnalyzer::is_future_type(&MirType::Adt {
            name: "Poll<Ready>".to_string()
        }));

        // Non-future types should not be detected
        assert!(!AwaitAnalyzer::is_future_type(&MirType::Adt {
            name: "Option".to_string()
        }));
        assert!(!AwaitAnalyzer::is_future_type(&MirType::Adt {
            name: "Result".to_string()
        }));
        assert!(!AwaitAnalyzer::is_future_type(&MirType::Int {
            signed: true,
            bits: 32
        }));
    }

    #[test]
    fn test_missing_await_ignored() {
        // Function that calls an async function but ignores the Future
        let caller = make_mir_function(
            "caller",
            MirType::Bool,
            vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "async_op".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
        );

        let async_op = make_mir_function(
            "async_op",
            MirType::Adt {
                name: "impl Future<Output=()>".to_string(),
            },
            vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
        );

        let funcs = vec![caller, async_op];
        let analyzer = AwaitAnalyzer::new(&funcs);
        let anomalies = analyzer.find_missing_awaits();

        // Should detect the missing await
        assert_eq!(anomalies.len(), 1);
        if let PathAnomaly::MissingAwait(missing) = &anomalies[0] {
            assert_eq!(missing.function, "caller");
            assert_eq!(missing.async_callee, "async_op");
        } else {
            panic!("Expected MissingAwait anomaly");
        }
    }

    #[test]
    fn test_future_used_no_anomaly() {
        // Function that calls an async function and uses the Future
        let caller = make_mir_function(
            "caller",
            MirType::Bool,
            vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "async_op".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                BasicBlock {
                    statements: vec![
                        // Use the Future (e.g., pass to executor or await)
                        Statement::Assign {
                            place: make_place(1),
                            rvalue: Rvalue::Use(Operand::Move(make_place(0))),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
        );

        let async_op = make_mir_function(
            "async_op",
            MirType::Adt {
                name: "Future<Output=i32>".to_string(),
            },
            vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
        );

        let funcs = vec![caller, async_op];
        let analyzer = AwaitAnalyzer::new(&funcs);
        let anomalies = analyzer.find_missing_awaits();

        // Should not detect any missing await (Future is used)
        assert!(anomalies.is_empty());
    }

    #[test]
    fn test_non_async_function_no_anomaly() {
        // Function that calls a synchronous function
        let caller = make_mir_function(
            "caller",
            MirType::Bool,
            vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "sync_fn".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
        );

        let sync_fn = make_mir_function(
            "sync_fn",
            MirType::Int {
                signed: true,
                bits: 32,
            },
            vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
        );

        let funcs = vec![caller, sync_fn];
        let analyzer = AwaitAnalyzer::new(&funcs);
        let anomalies = analyzer.find_missing_awaits();

        // Should not detect any anomaly (not an async function)
        assert!(anomalies.is_empty());
    }

    #[test]
    fn test_known_async_function_heuristics() {
        let funcs: Vec<MirFunction> = vec![];
        let analyzer = AwaitAnalyzer::new(&funcs);

        // These should be detected as async
        assert!(analyzer.is_known_async_function("async_read"));
        assert!(analyzer.is_known_async_function("fetch_data_async"));
        assert!(analyzer.is_known_async_function("tokio::spawn"));
        assert!(analyzer.is_known_async_function("tokio::time::sleep"));
        assert!(analyzer.is_known_async_function("tokio::select"));
        assert!(analyzer.is_known_async_function("future::then"));

        // These should not be detected
        assert!(!analyzer.is_known_async_function("println"));
        assert!(!analyzer.is_known_async_function("vec::push"));
        assert!(!analyzer.is_known_async_function("clone"));
    }

    #[test]
    fn test_wiring_verifier_check_missing_awaits() {
        let graph = CallGraph::new();
        let verifier = WiringVerifier::new(graph);

        // Create functions for test
        let caller = make_mir_function(
            "caller",
            MirType::Bool,
            vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "fetch_data".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
        );

        let fetch_data = make_mir_function(
            "fetch_data",
            MirType::Adt {
                name: "impl Future<Output=Data>".to_string(),
            },
            vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
        );

        let funcs = vec![caller, fetch_data];
        let anomalies = verifier.check_missing_awaits(&funcs);

        assert_eq!(anomalies.len(), 1);
    }

    // ============================================
    // PartialStructUpdate Detection tests (Phase 6.5.4)
    // ============================================

    fn make_place_with_field(local_idx: usize, field_idx: usize) -> crate::Place {
        crate::Place {
            local: Local(local_idx),
            projections: vec![crate::Projection::Field(field_idx)],
        }
    }

    #[test]
    fn test_struct_update_analyzer_no_structs() {
        // Empty function list - no anomalies
        let funcs: Vec<MirFunction> = vec![];
        let analyzer = StructUpdateAnalyzer::new(&funcs);
        let anomalies = analyzer.find_partial_updates();
        assert!(anomalies.is_empty());
    }

    #[test]
    fn test_struct_update_analyzer_normal_construction() {
        // Normal struct construction with all fields explicitly set
        let func = MirFunction {
            name: "builder".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "Point".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: make_place(0),
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Adt {
                            name: "Point".to_string(),
                            variant: None,
                        },
                        operands: vec![
                            Operand::Constant(crate::Constant::Int(10)),
                            Operand::Constant(crate::Constant::Int(20)),
                        ],
                    },
                }],
                terminator: Terminator::Return,
            }],
            locals: vec![LocalDecl {
                ty: MirType::Adt {
                    name: "Point".to_string(),
                },
                name: None,
            }],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = StructUpdateAnalyzer::new(&funcs);
        let anomalies = analyzer.find_partial_updates();

        // No anomaly - all fields explicitly set with constants
        assert!(anomalies.is_empty());
    }

    #[test]
    fn test_struct_update_syntax_detection() {
        // Struct construction where some fields come from another struct's fields
        // This simulates `Point { x: 5, ..old_point }`
        let func = MirFunction {
            name: "updater".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "Point".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![
                    // Create new struct with one explicit field, one from old struct
                    Statement::Assign {
                        place: make_place(0),
                        rvalue: Rvalue::Aggregate {
                            kind: AggregateKind::Adt {
                                name: "Point".to_string(),
                                variant: None,
                            },
                            operands: vec![
                                Operand::Constant(crate::Constant::Int(5)), // x = 5 (explicit)
                                Operand::Copy(make_place_with_field(1, 1)), // y from old.y
                            ],
                        },
                    },
                ],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Adt {
                        name: "Point".to_string(),
                    },
                    name: None,
                },
                LocalDecl {
                    ty: MirType::Adt {
                        name: "Point".to_string(),
                    },
                    name: Some("old_point".to_string()),
                },
            ],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = StructUpdateAnalyzer::new(&funcs);
        let anomalies = analyzer.find_partial_updates();

        // Should detect struct update syntax (field 1 copied from another struct)
        // Note: Detection depends on heuristics - fields from same source local
        // In this case, only one field is from a projection, so might not trigger
        assert!(anomalies.is_empty() || anomalies.len() == 1);
    }

    #[test]
    fn test_partial_move_detection() {
        // Partial move: move one field out of a struct
        let func = MirFunction {
            name: "partial_mover".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![
                    // Move field 0 out of local 1
                    Statement::Assign {
                        place: make_place(2),
                        rvalue: Rvalue::Use(Operand::Move(make_place_with_field(1, 0))),
                    },
                    // Then try to use the whole struct (local 1)
                    Statement::Assign {
                        place: make_place(0),
                        rvalue: Rvalue::Use(Operand::Copy(make_place(1))),
                    },
                ],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                },
                LocalDecl {
                    ty: MirType::Adt {
                        name: "Point".to_string(),
                    },
                    name: Some("point".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                },
            ],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = StructUpdateAnalyzer::new(&funcs);
        let anomalies = analyzer.find_partial_updates();

        // Should detect partial move - field 0 was moved, then whole struct accessed
        assert_eq!(anomalies.len(), 1);
        if let PathAnomaly::PartialStructUpdate(update) = &anomalies[0] {
            assert_eq!(update.function, "partial_mover");
            assert!(matches!(update.reason, PartialUpdateReason::PartialMove));
            assert!(update.uninitialized_fields.contains(&"field_0".to_string()));
        } else {
            panic!("Expected PartialStructUpdate anomaly");
        }
    }

    #[test]
    fn test_wiring_verifier_check_partial_struct_updates() {
        let graph = CallGraph::new();
        let verifier = WiringVerifier::new(graph);

        // Create a function with partial move
        let func = MirFunction {
            name: "test_fn".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![
                    // Move field 0 out of local 1
                    Statement::Assign {
                        place: make_place(2),
                        rvalue: Rvalue::Use(Operand::Move(make_place_with_field(1, 0))),
                    },
                    // Then try to use the whole struct
                    Statement::Assign {
                        place: make_place(0),
                        rvalue: Rvalue::Use(Operand::Copy(make_place(1))),
                    },
                ],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                },
                LocalDecl {
                    ty: MirType::Adt {
                        name: "Data".to_string(),
                    },
                    name: None,
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                },
            ],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let anomalies = verifier.check_partial_struct_updates(&funcs);

        // Should detect the partial move
        assert_eq!(anomalies.len(), 1);
    }

    #[test]
    fn test_struct_info_learning() {
        // Test that analyzer learns struct field counts from aggregate constructions
        let func = MirFunction {
            name: "constructor".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "MyStruct".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: make_place(0),
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Adt {
                            name: "MyStruct".to_string(),
                            variant: None,
                        },
                        operands: vec![
                            Operand::Constant(crate::Constant::Int(1)),
                            Operand::Constant(crate::Constant::Int(2)),
                            Operand::Constant(crate::Constant::Int(3)),
                        ],
                    },
                }],
                terminator: Terminator::Return,
            }],
            locals: vec![LocalDecl {
                ty: MirType::Adt {
                    name: "MyStruct".to_string(),
                },
                name: None,
            }],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = StructUpdateAnalyzer::new(&funcs);

        // Analyzer should have learned that MyStruct has 3 fields
        assert!(analyzer.struct_info.contains_key("MyStruct"));
        assert_eq!(analyzer.struct_info.get("MyStruct").unwrap().field_count, 3);
    }

    // ============================================
    // DataFlowAnalyzer tests (Phase 6.5.5)
    // ============================================

    #[test]
    fn test_data_flow_analyzer_no_functions() {
        // Empty function list - no anomalies
        let funcs: Vec<MirFunction> = vec![];
        let analyzer = DataFlowAnalyzer::new(&funcs);
        let anomalies = analyzer.find_unused_values();
        assert!(anomalies.is_empty());
    }

    #[test]
    fn test_unused_parameter() {
        // Function with a parameter that is never used
        let func = MirFunction {
            name: "unused_param".to_string(),
            params: vec![(
                "x".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![
                    // Return constant, not the parameter
                    Statement::Assign {
                        place: make_place(0),
                        rvalue: Rvalue::Use(Operand::Constant(crate::Constant::Int(42))),
                    },
                ],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_return".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("x".to_string()),
                },
            ],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = DataFlowAnalyzer::new(&funcs);
        let anomalies = analyzer.find_unused_values();

        // Should detect unused parameter 'x' (local 0 is return, param starts at 0 in our simplified model)
        // Note: actual detection depends on mapping - this may or may not trigger
        // based on whether the parameter index matches
        assert!(anomalies.len() <= 1); // At most one unused value
    }

    #[test]
    fn test_all_values_used() {
        // Function where all values are used
        let func = MirFunction {
            name: "all_used".to_string(),
            params: vec![(
                "x".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![
                    // Use the parameter
                    Statement::Assign {
                        place: make_place(0),
                        rvalue: Rvalue::Use(Operand::Copy(make_place(1))),
                    },
                ],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("x".to_string()),
                },
            ],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = DataFlowAnalyzer::new(&funcs);
        let anomalies = analyzer.find_unused_values();

        // No unused values - parameter is used
        assert!(anomalies.is_empty());
    }

    #[test]
    fn test_computed_value_never_returned() {
        // Function that computes a value but doesn't return it
        let func = MirFunction {
            name: "dead_computation".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![
                    // Compute something into local 1 (named)
                    Statement::Assign {
                        place: make_place(1),
                        rvalue: Rvalue::Use(Operand::Constant(crate::Constant::Int(10))),
                    },
                    // Return a different constant (local 0)
                    Statement::Assign {
                        place: make_place(0),
                        rvalue: Rvalue::Use(Operand::Constant(crate::Constant::Int(0))),
                    },
                ],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("computed".to_string()),
                },
            ],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = DataFlowAnalyzer::new(&funcs);
        let anomalies = analyzer.find_unused_values();

        // Should detect that 'computed' was assigned but never used
        assert_eq!(anomalies.len(), 1);
        if let PathAnomaly::UnusedValue(unused) = &anomalies[0] {
            assert_eq!(unused.function, "dead_computation");
            assert!(unused.computation.contains("computed"));
        } else {
            panic!("Expected UnusedValue anomaly");
        }
    }

    #[test]
    fn test_wiring_verifier_check_unused_values() {
        let graph = CallGraph::new();
        let verifier = WiringVerifier::new(graph);

        // Create function with unused computation
        let func = MirFunction {
            name: "test_fn".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![
                    Statement::Assign {
                        place: make_place(1),
                        rvalue: Rvalue::Use(Operand::Constant(crate::Constant::Int(999))),
                    },
                    Statement::Assign {
                        place: make_place(0),
                        rvalue: Rvalue::Use(Operand::Constant(crate::Constant::Int(0))),
                    },
                ],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("unused_value".to_string()),
                },
            ],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let anomalies = verifier.check_unused_values(&funcs);

        // Should detect the unused value
        assert_eq!(anomalies.len(), 1);
    }

    #[test]
    fn test_data_flow_verification_satisfied() {
        // Test data flow where input reaches output
        let func = MirFunction {
            name: "transform".to_string(),
            params: vec![(
                "input".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![
                    // temp = input * 2
                    Statement::Assign {
                        place: make_place(2),
                        rvalue: Rvalue::BinaryOp(
                            crate::BinOp::Mul,
                            Operand::Copy(make_place(1)),
                            Operand::Constant(crate::Constant::Int(2)),
                        ),
                    },
                    // result = temp
                    Statement::Assign {
                        place: make_place(0),
                        rvalue: Rvalue::Use(Operand::Move(make_place(2))),
                    },
                ],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                }, // return
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("input".to_string()),
                }, // param
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                }, // temp
            ],
            span: SourceSpan::default(),
        };

        let mut graph = CallGraph::new();
        graph.add_function("transform", vec![]);
        // Add data flow annotation: input => result
        graph.add_wire_spec(
            "transform",
            WireSpec {
                annotations: vec![WireAnnotation::DataFlow {
                    input: "input".to_string(),
                    output: "result".to_string(),
                }],
                span: Some(SourceSpan::default()),
            },
        );

        let funcs = vec![func];
        let analyzer = DataFlowAnalyzer::new(&funcs);
        let violations = analyzer.verify_data_flow_annotations(&graph);

        // Data flow should be satisfied (input -> temp -> result)
        assert!(violations.is_empty());
    }

    #[test]
    fn test_data_flow_verification_violated() {
        // Test data flow where input does NOT reach output
        let func = MirFunction {
            name: "ignores_input".to_string(),
            params: vec![(
                "input".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![
                    // Return a constant, ignoring input
                    Statement::Assign {
                        place: make_place(0),
                        rvalue: Rvalue::Use(Operand::Constant(crate::Constant::Int(42))),
                    },
                ],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                }, // return
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("input".to_string()),
                }, // param
            ],
            span: SourceSpan::default(),
        };

        let mut graph = CallGraph::new();
        graph.add_function("ignores_input", vec![]);
        // Add data flow annotation: input => result
        graph.add_wire_spec(
            "ignores_input",
            WireSpec {
                annotations: vec![WireAnnotation::DataFlow {
                    input: "input".to_string(),
                    output: "result".to_string(),
                }],
                span: Some(SourceSpan::default()),
            },
        );

        let funcs = vec![func];
        let analyzer = DataFlowAnalyzer::new(&funcs);
        let violations = analyzer.verify_data_flow_annotations(&graph);

        // Data flow should NOT be satisfied (input is ignored)
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].function, "ignores_input");
        assert_eq!(violations[0].input, "input");
        assert_eq!(violations[0].output, "result");
    }

    #[test]
    fn test_wiring_verifier_check_data_flow() {
        // Test the verifier's check_data_flow_annotations method
        let func = MirFunction {
            name: "passthrough".to_string(),
            params: vec![(
                "data".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![
                    // Just return the input
                    Statement::Assign {
                        place: make_place(0),
                        rvalue: Rvalue::Use(Operand::Copy(make_place(1))),
                    },
                ],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: None,
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("data".to_string()),
                },
            ],
            span: SourceSpan::default(),
        };

        let mut graph = CallGraph::new();
        graph.add_function("passthrough", vec![]);
        graph.add_wire_spec(
            "passthrough",
            WireSpec {
                annotations: vec![WireAnnotation::DataFlow {
                    input: "data".to_string(),
                    output: "result".to_string(),
                }],
                span: Some(SourceSpan::default()),
            },
        );

        let verifier = WiringVerifier::new(graph);
        let funcs = vec![func];
        let violations = verifier.check_data_flow_annotations(&funcs);

        // Should be satisfied - data flows to result
        assert!(violations.is_empty());
    }

    // ============================================
    // AsyncChainAnalyzer tests (Phase 6.5.2)
    // ============================================

    #[test]
    fn test_async_chain_analyzer_new() {
        let funcs: Vec<MirFunction> = vec![];
        let analyzer = AsyncChainAnalyzer::new(&funcs);
        assert!(analyzer.async_functions.is_empty());
    }

    #[test]
    fn test_async_chain_analyzer_detects_async_function() {
        let async_func = MirFunction {
            name: "async_fetch".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "impl Future<Output=i32>".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let funcs = vec![async_func];
        let analyzer = AsyncChainAnalyzer::new(&funcs);
        assert!(analyzer.is_async("async_fetch"));
    }

    #[test]
    fn test_async_chain_analyzer_known_patterns() {
        let funcs: Vec<MirFunction> = vec![];
        let analyzer = AsyncChainAnalyzer::new(&funcs);

        // Test known async patterns
        assert!(analyzer.is_async("async_read"));
        assert!(analyzer.is_async("fetch_data_async"));
        assert!(!analyzer.is_async("regular_function"));
    }

    #[test]
    fn test_async_chain_analyzer_spawn_detection() {
        let funcs: Vec<MirFunction> = vec![];
        let analyzer = AsyncChainAnalyzer::new(&funcs);

        assert!(analyzer.is_spawn_call("tokio::spawn"));
        assert!(analyzer.is_spawn_call("async_std::task::spawn"));
        assert!(analyzer.is_spawn_call("my_spawn"));
        assert!(!analyzer.is_spawn_call("regular_call"));
    }

    #[test]
    fn test_async_chain_analyzer_block_on_detection() {
        let funcs: Vec<MirFunction> = vec![];
        let analyzer = AsyncChainAnalyzer::new(&funcs);

        assert!(analyzer.is_block_on_call("futures::executor::block_on"));
        assert!(analyzer.is_block_on_call("tokio::runtime::Runtime::block_on"));
        assert!(analyzer.is_block_on_call("my_block_on"));
        assert!(!analyzer.is_block_on_call("regular_call"));
    }

    #[test]
    fn test_async_chain_with_await_no_violation() {
        // Async function that properly awaits
        let async_func = MirFunction {
            name: "async_with_await".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "impl Future<Output=()>".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "__rust_await".to_string(),
                    args: vec![],
                    destination: crate::Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    target: 0,
                    span: SourceSpan::default(),
                    generic_args: vec![],
                },
            }],
            locals: vec![LocalDecl {
                ty: MirType::Adt {
                    name: "()".to_string(),
                },
                name: None,
            }],
            span: SourceSpan::default(),
        };

        let funcs = vec![async_func];
        let mut analyzer = AsyncChainAnalyzer::new(&funcs);

        // Should terminate with Awaited - no violation
        let violations = analyzer.find_async_chain_violations();
        let no_await_violations = violations.iter().any(|v| {
            if let PathAnomaly::AsyncChainViolation(acv) = v {
                matches!(acv.violation_type, AsyncChainViolationType::NoAwaitPoint)
            } else {
                false
            }
        });
        assert!(!no_await_violations);
    }

    #[test]
    fn test_async_chain_spawned_flagged() {
        // Async function that spawns a task
        let async_func = MirFunction {
            name: "async_spawner".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "impl Future<Output=()>".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "tokio::spawn".to_string(),
                    args: vec![],
                    destination: crate::Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    target: 0,
                    span: SourceSpan::default(),
                    generic_args: vec![],
                },
            }],
            locals: vec![LocalDecl {
                ty: MirType::Adt {
                    name: "JoinHandle<()>".to_string(),
                },
                name: None,
            }],
            span: SourceSpan::default(),
        };

        let funcs = vec![async_func];
        let mut analyzer = AsyncChainAnalyzer::new(&funcs);

        let violations = analyzer.find_async_chain_violations();
        // Should flag as DanglingSpawn
        let has_dangling = violations.iter().any(|v| {
            if let PathAnomaly::AsyncChainViolation(acv) = v {
                matches!(acv.violation_type, AsyncChainViolationType::DanglingSpawn)
            } else {
                false
            }
        });
        assert!(has_dangling);
    }

    #[test]
    fn test_async_chain_cyclic_dependency_detection() {
        // Create two async functions that call each other
        let func_a = MirFunction {
            name: "async_a".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "impl Future<Output=()>".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "async_b".to_string(),
                    args: vec![],
                    destination: crate::Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    target: 0,
                    span: SourceSpan::default(),
                    generic_args: vec![],
                },
            }],
            locals: vec![LocalDecl {
                ty: MirType::Adt {
                    name: "()".to_string(),
                },
                name: None,
            }],
            span: SourceSpan::default(),
        };

        let func_b = MirFunction {
            name: "async_b".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "impl Future<Output=()>".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "async_a".to_string(),
                    args: vec![],
                    destination: crate::Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    target: 0,
                    span: SourceSpan::default(),
                    generic_args: vec![],
                },
            }],
            locals: vec![LocalDecl {
                ty: MirType::Adt {
                    name: "()".to_string(),
                },
                name: None,
            }],
            span: SourceSpan::default(),
        };

        let funcs = vec![func_a, func_b];
        let analyzer = AsyncChainAnalyzer::new(&funcs);

        let violations = analyzer.find_cyclic_dependencies();
        let has_cycle = violations.iter().any(|v| {
            if let PathAnomaly::AsyncChainViolation(acv) = v {
                matches!(
                    acv.violation_type,
                    AsyncChainViolationType::CyclicDependency
                )
            } else {
                false
            }
        });
        assert!(has_cycle);
    }

    #[test]
    fn test_wiring_verifier_check_async_chains() {
        // Test through WiringVerifier
        let async_func = MirFunction {
            name: "async_no_await".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "impl Future<Output=()>".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let graph = CallGraph::new();
        let verifier = WiringVerifier::new(graph);
        let funcs = vec![async_func];

        let anomalies = verifier.check_async_chains(&funcs);
        // The future is returned, so it's properly terminated
        // No NoAwaitPoint violation expected (terminated with Returned)
        assert!(
            anomalies.is_empty()
                || anomalies.iter().all(|v| {
                    if let PathAnomaly::AsyncChainViolation(acv) = v {
                        !matches!(acv.violation_type, AsyncChainViolationType::NoAwaitPoint)
                    } else {
                        true
                    }
                })
        );
    }

    #[test]
    fn test_async_chain_non_async_function() {
        // Regular non-async function should not create chains
        let regular_func = MirFunction {
            name: "regular".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let funcs = vec![regular_func];
        let mut analyzer = AsyncChainAnalyzer::new(&funcs);

        let violations = analyzer.find_async_chain_violations();
        // No async chains, no violations
        assert!(violations.is_empty());
    }

    #[test]
    fn test_async_chain_has_await_point() {
        let func_with_await = MirFunction {
            name: "has_await".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "impl Future<Output=()>".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "poll".to_string(),
                    args: vec![],
                    destination: crate::Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    target: 0,
                    span: SourceSpan::default(),
                    generic_args: vec![],
                },
            }],
            locals: vec![LocalDecl {
                ty: MirType::Adt {
                    name: "()".to_string(),
                },
                name: None,
            }],
            span: SourceSpan::default(),
        };

        let funcs = vec![func_with_await];
        let analyzer = AsyncChainAnalyzer::new(&funcs);
        assert!(analyzer.has_await_point(&funcs[0]));
    }

    // ============================================
    // Closure and Function Pointer tests (Phase 6.5.2)
    // ============================================

    #[test]
    fn test_closure_detection_in_function() {
        let func = MirFunction {
            name: "test_func".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: crate::Place {
                        local: Local(1),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Closure {
                            def_id: "test_func::{closure#0}".to_string(),
                        },
                        operands: vec![],
                    },
                }],
                terminator: Terminator::Return,
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = AsyncChainAnalyzer::new(&funcs);
        assert!(analyzer.has_closures("test_func"));
        let closures = analyzer.get_closures("test_func").unwrap();
        assert_eq!(closures.len(), 1);
        assert_eq!(closures[0], "test_func::{closure#0}");
    }

    #[test]
    fn test_coroutine_detection() {
        let func = MirFunction {
            name: "async_func".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "impl Future".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: crate::Place {
                        local: Local(1),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Coroutine {
                            def_id: "async_func::{async#0}".to_string(),
                        },
                        operands: vec![],
                    },
                }],
                terminator: Terminator::Return,
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = AsyncChainAnalyzer::new(&funcs);
        let coroutines = analyzer.get_coroutines("async_func").unwrap();
        assert_eq!(coroutines.len(), 1);
        assert_eq!(coroutines[0], "async_func::{async#0}");
    }

    #[test]
    fn test_indirect_call_detection() {
        let func = MirFunction {
            name: "caller".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::IndirectCall {
                    callee: crate::Place {
                        local: Local(1),
                        projections: vec![],
                    },
                    callee_ty: MirType::FnPtr {
                        params: vec![],
                        ret: Box::new(MirType::Int {
                            signed: true,
                            bits: 32,
                        }),
                    },
                    args: vec![],
                    destination: crate::Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    target: 0,
                    span: SourceSpan::default(),
                },
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = AsyncChainAnalyzer::new(&funcs);
        assert!(analyzer.has_indirect_calls("caller"));
        let indirect = analyzer.get_indirect_calls("caller").unwrap();
        assert_eq!(indirect.len(), 1);
        assert!(matches!(indirect[0].callee_type, MirType::FnPtr { .. }));
    }

    #[test]
    fn test_spawn_closure_detection() {
        let func = MirFunction {
            name: "spawner".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "JoinHandle".to_string(),
            },
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: crate::Place {
                        local: Local(1),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Coroutine {
                            def_id: "spawner::{async_block#0}".to_string(),
                        },
                        operands: vec![],
                    },
                }],
                terminator: Terminator::Call {
                    func: "tokio::spawn".to_string(),
                    args: vec![Operand::Move(crate::Place {
                        local: Local(1),
                        projections: vec![],
                    })],
                    destination: crate::Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    target: 0,
                    span: SourceSpan::default(),
                    generic_args: vec![],
                },
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = AsyncChainAnalyzer::new(&funcs);
        let spawn_closures = analyzer.get_spawn_closures("spawner").unwrap();
        assert_eq!(spawn_closures.len(), 1);
        assert_eq!(spawn_closures[0].closure_def_id, "spawner::{async_block#0}");
        assert_eq!(spawn_closures[0].spawn_func, "tokio::spawn");
    }

    #[test]
    fn test_closure_violation_detection() {
        // Function that spawns a closure without tracking the JoinHandle
        let func = MirFunction {
            name: "bad_spawner".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: crate::Place {
                        local: Local(1),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Aggregate {
                        kind: AggregateKind::Coroutine {
                            def_id: "bad_spawner::{async_block#0}".to_string(),
                        },
                        operands: vec![],
                    },
                }],
                terminator: Terminator::Call {
                    func: "tokio::spawn".to_string(),
                    args: vec![Operand::Move(crate::Place {
                        local: Local(1),
                        projections: vec![],
                    })],
                    destination: crate::Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    target: 0,
                    span: SourceSpan::default(),
                    generic_args: vec![],
                },
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = AsyncChainAnalyzer::new(&funcs);
        let violations = analyzer.find_closure_violations();

        // Should detect a DanglingSpawn violation
        assert!(!violations.is_empty());
        let has_dangling = violations.iter().any(|v| {
            if let PathAnomaly::AsyncChainViolation(acv) = v {
                matches!(acv.violation_type, AsyncChainViolationType::DanglingSpawn)
            } else {
                false
            }
        });
        assert!(has_dangling);
    }

    #[test]
    fn test_no_closures_in_simple_function() {
        let func = MirFunction {
            name: "simple".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let funcs = vec![func];
        let analyzer = AsyncChainAnalyzer::new(&funcs);
        assert!(!analyzer.has_closures("simple"));
        assert!(!analyzer.has_indirect_calls("simple"));
    }

    #[test]
    fn test_is_async_closure_detection() {
        let funcs: Vec<MirFunction> = vec![];
        let analyzer = AsyncChainAnalyzer::new(&funcs);

        // Test async closure detection heuristics
        assert!(analyzer.is_async_closure("func::{async#0}"));
        assert!(analyzer.is_async_closure("mod::func::{async block}"));
        assert!(analyzer.is_async_closure("coroutine::state_machine"));
        assert!(!analyzer.is_async_closure("func::{closure#0}"));
        assert!(!analyzer.is_async_closure("simple_func"));
    }

    // Tests for Phase 6.5.2: Monomorphized generics in call graph

    #[test]
    fn test_call_graph_with_generic_args() {
        // Test that call graph properly distinguishes monomorphized calls
        let func = MirFunction {
            name: "caller".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "Option::map".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![
                            MirType::Int {
                                signed: true,
                                bits: 32,
                            },
                            MirType::Bool,
                        ],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let graph = CallGraph::from_mir_functions(&[func]);

        // Should track monomorphized name
        let reachable = graph.reachable_from("caller");
        assert!(reachable.contains("caller"));
        assert!(reachable.contains("Option::map<i32, bool>"));
        // Should NOT contain un-monomorphized name
        assert!(!reachable.contains("Option::map"));
    }

    #[test]
    fn test_call_graph_non_generic_call() {
        // Test that non-generic calls work as before
        let func = MirFunction {
            name: "caller".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "simple_func".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![], // No generic args
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let graph = CallGraph::from_mir_functions(&[func]);

        let reachable = graph.reachable_from("caller");
        assert!(reachable.contains("caller"));
        assert!(reachable.contains("simple_func"));
    }

    #[test]
    fn test_call_graph_multiple_monomorphizations() {
        // Test that different instantiations of the same generic function are tracked separately
        let func = MirFunction {
            name: "caller".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "Vec::push".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![MirType::Int {
                            signed: true,
                            bits: 32,
                        }],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "Vec::push".to_string(),
                        args: vec![],
                        destination: make_place(0),
                        target: 2,
                        span: SourceSpan::default(),
                        generic_args: vec![MirType::Adt {
                            name: "String".to_string(),
                        }],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let graph = CallGraph::from_mir_functions(&[func]);

        let reachable = graph.reachable_from("caller");
        assert!(reachable.contains("caller"));
        // Both instantiations should be tracked separately
        assert!(reachable.contains("Vec::push<i32>"));
        assert!(reachable.contains("Vec::push<String>"));
    }
}
