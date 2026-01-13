//! Async State Machine Extraction (Phase 6.1)
//!
//! This module extracts implicit state machines from async Rust code.
//! Rust async functions compile to state machines where each `.await`
//! creates a new suspension point (yield point).
//!
//! The extracted state machines can be used for:
//! - Deadlock freedom verification
//! - Liveness property checking
//! - Protocol verification

use vc_ir::temporal::{AsyncStateKind, AsyncStateMachine, CapturedVariable};
use vc_ir::{SourceSpan, VcType};

use std::collections::HashMap;

/// Extracts async state machines from MIR function representations.
///
/// This extractor analyzes the structure of async functions to identify:
/// - Yield points (`.await` expressions)
/// - State transitions between yield points
/// - Variables captured across yield points
#[derive(Debug)]
pub struct AsyncStateMachineExtractor {
    /// Currently extracted state machines
    pub state_machines: Vec<AsyncStateMachine>,
    /// Options for extraction
    pub options: ExtractionOptions,
}

/// Options for state machine extraction
#[derive(Debug, Clone, Default)]
pub struct ExtractionOptions {
    /// Include source spans for debugging
    pub include_spans: bool,
    /// Track captured variables
    pub track_captured_variables: bool,
    /// Maximum states before aborting (0 = no limit)
    pub max_states: usize,
}

/// Result of state machine extraction
#[derive(Debug)]
pub struct ExtractionResult {
    /// The extracted state machine
    pub state_machine: AsyncStateMachine,
    /// Warnings during extraction
    pub warnings: Vec<ExtractionWarning>,
    /// Whether the extraction was complete
    pub complete: bool,
}

/// Warning during extraction
#[derive(Debug, Clone)]
pub struct ExtractionWarning {
    /// Warning message
    pub message: String,
    /// Associated source span (if any)
    pub span: Option<SourceSpan>,
}

/// Information about an async function for extraction
#[derive(Debug, Clone)]
pub struct AsyncFunctionInfo {
    /// Function name
    pub name: String,
    /// Whether the function is marked async
    pub is_async: bool,
    /// Return type (the Future's Output type)
    pub return_type: Option<VcType>,
    /// Parameters
    pub parameters: Vec<(String, VcType)>,
    /// Yield points in the function
    pub yield_points: Vec<YieldPointInfo>,
    /// Control flow graph blocks
    pub basic_blocks: Vec<BasicBlockInfo>,
    /// Source span of the function
    pub span: Option<SourceSpan>,
}

/// Information about a yield point (.await)
#[derive(Debug, Clone)]
pub struct YieldPointInfo {
    /// Index of the yield point
    pub index: usize,
    /// Block containing the yield
    pub block: usize,
    /// Awaited expression (if identifiable)
    pub awaited_expr: Option<String>,
    /// Type of the future being awaited
    pub future_type: Option<String>,
    /// Variables live across this yield point
    pub live_variables: Vec<String>,
    /// Source span
    pub span: Option<SourceSpan>,
}

/// Basic block information for control flow
#[derive(Debug, Clone)]
pub struct BasicBlockInfo {
    /// Block index
    pub index: usize,
    /// Kind of terminator
    pub terminator: BlockTerminator,
    /// Successor blocks
    pub successors: Vec<usize>,
    /// Is this block a yield point?
    pub is_yield: bool,
}

/// Block terminator kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockTerminator {
    /// Unconditional goto
    Goto,
    /// Conditional branch
    SwitchInt,
    /// Return from function
    Return,
    /// Yield (for async/generators)
    Yield,
    /// Function call
    Call,
    /// Drop
    Drop,
    /// Unreachable
    Unreachable,
    /// Resume from panic
    Resume,
    /// Abort
    Abort,
}

impl Default for AsyncStateMachineExtractor {
    fn default() -> Self {
        Self::new()
    }
}

impl AsyncStateMachineExtractor {
    /// Create a new extractor with default options
    #[must_use]
    pub fn new() -> Self {
        Self {
            state_machines: Vec::new(),
            options: ExtractionOptions::default(),
        }
    }

    /// Create a new extractor with custom options
    #[must_use]
    pub const fn with_options(options: ExtractionOptions) -> Self {
        Self {
            state_machines: Vec::new(),
            options,
        }
    }

    /// Extract a state machine from an async function
    pub fn extract(&mut self, func: &AsyncFunctionInfo) -> ExtractionResult {
        let mut warnings = Vec::new();

        if !func.is_async {
            warnings.push(ExtractionWarning {
                message: format!("Function '{}' is not async", func.name),
                span: func.span.clone(),
            });
        }

        let mut sm = AsyncStateMachine::new(&func.name);

        // If no yield points, the async function is trivial (no suspension)
        if func.yield_points.is_empty() {
            let end = sm.add_state("End", AsyncStateKind::End);
            sm.add_transition(0, end);

            return ExtractionResult {
                state_machine: sm,
                warnings,
                complete: true,
            };
        }

        // Build state machine from yield points and control flow
        let result = self.build_state_machine(&mut sm, func, &mut warnings);

        self.state_machines.push(sm.clone());

        ExtractionResult {
            state_machine: sm,
            warnings,
            complete: result,
        }
    }

    /// Build the state machine from function info
    fn build_state_machine(
        &self,
        sm: &mut AsyncStateMachine,
        func: &AsyncFunctionInfo,
        warnings: &mut Vec<ExtractionWarning>,
    ) -> bool {
        // Map from block index to state index
        let mut block_to_state: HashMap<usize, usize> = HashMap::new();
        block_to_state.insert(0, 0); // Entry block maps to Start state

        // Create states for yield points
        for (i, yp) in func.yield_points.iter().enumerate() {
            let state_name = format!("AfterAwait{i}");
            let state_idx = sm.add_state(&state_name, AsyncStateKind::Suspended);
            block_to_state.insert(yp.block, state_idx);

            // Track captured variables
            if self.options.track_captured_variables {
                for var in &yp.live_variables {
                    if let Some(idx) = sm.captured_variables.iter().position(|v| v.name == *var) {
                        sm.captured_variables[idx].live_across.push(i);
                    } else {
                        sm.captured_variables.push(CapturedVariable {
                            name: var.clone(),
                            ty: VcType::Abstract("_inferred".to_string()),
                            live_across: vec![i],
                            is_mutable: false,
                        });
                    }
                }
            }
        }

        // Create end state
        let end_state = sm.add_state("End", AsyncStateKind::End);

        // Create states for basic blocks that aren't yield points
        for block in &func.basic_blocks {
            use std::collections::hash_map::Entry;
            if let Entry::Vacant(entry) = block_to_state.entry(block.index) {
                // Check if this is a return block
                if block.terminator == BlockTerminator::Return {
                    entry.insert(end_state);
                } else {
                    // Create intermediate state
                    let state_name = format!("Block{}", block.index);
                    let state_idx = sm.add_state(&state_name, AsyncStateKind::Resumable);
                    entry.insert(state_idx);
                }
            }
        }

        // Check for state limit
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

        // Create transitions from basic block control flow
        for block in &func.basic_blocks {
            let from_state = *block_to_state.get(&block.index).unwrap_or(&0);

            for succ in &block.successors {
                let to_state = *block_to_state.get(succ).unwrap_or(&end_state);
                let t = sm.add_transition(from_state, to_state);
                t.is_yield = block.is_yield;

                if self.options.include_spans {
                    if let Some(bb_info) = func.basic_blocks.iter().find(|b| b.index == block.index)
                    {
                        // Would set span here if available
                        let _ = bb_info;
                    }
                }
            }
        }

        // Create yield points from yield point info
        for (i, yp) in func.yield_points.iter().enumerate() {
            let pre_state = *block_to_state.get(&yp.block).unwrap_or(&0);
            // Find the successor state (state after the yield)
            let post_block = func
                .basic_blocks
                .iter()
                .find(|b| b.index == yp.block)
                .and_then(|b| b.successors.first().copied())
                .unwrap_or(yp.block + 1);
            let post_state = *block_to_state.get(&post_block).unwrap_or(&end_state);

            let yp_idx = sm.add_yield_point(pre_state, post_state);
            sm.yield_points[yp_idx]
                .awaited_future
                .clone_from(&yp.awaited_expr);
            sm.yield_points[yp_idx]
                .future_type
                .clone_from(&yp.future_type);

            if self.options.include_spans {
                sm.yield_points[yp_idx].source_span.clone_from(&yp.span);
            }

            let _ = i; // Used for tracking
        }

        true
    }

    /// Extract state machine from a simple sequential async function
    ///
    /// This is a simplified extraction for functions like:
    /// ```text
    /// async fn foo() {
    ///     x.await;
    ///     y.await;
    ///     z.await;
    /// }
    /// ```
    pub fn extract_sequential(&mut self, name: &str, yield_count: usize) -> AsyncStateMachine {
        let mut sm = AsyncStateMachine::new(name);

        if yield_count == 0 {
            let end = sm.add_state("End", AsyncStateKind::End);
            sm.add_transition(0, end);
            self.state_machines.push(sm.clone());
            return sm;
        }

        let mut prev_state = 0; // Start state

        for i in 0..yield_count {
            // Create resumable state before await
            let resumable = sm.add_state(&format!("BeforeAwait{i}"), AsyncStateKind::Resumable);
            sm.add_transition(prev_state, resumable);

            // Create suspended state after await
            let suspended = sm.add_state(&format!("AfterAwait{i}"), AsyncStateKind::Suspended);
            {
                let t = sm.add_transition(resumable, suspended);
                t.is_yield = true;
            }

            // Track yield point
            sm.add_yield_point(resumable, suspended);

            prev_state = suspended;
        }

        // Final transition to end
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(prev_state, end);

        self.state_machines.push(sm.clone());
        sm
    }

    /// Extract state machine with branching (e.g., if/match)
    ///
    /// For functions like:
    /// ```text
    /// async fn foo(cond: bool) {
    ///     if cond {
    ///         x.await;
    ///     } else {
    ///         y.await;
    ///     }
    /// }
    /// ```
    pub fn extract_branching(
        &mut self,
        name: &str,
        branches: &[usize], // yield count per branch
    ) -> AsyncStateMachine {
        let mut sm = AsyncStateMachine::new(name);

        if branches.is_empty() || branches.iter().all(|&c| c == 0) {
            let end = sm.add_state("End", AsyncStateKind::End);
            sm.add_transition(0, end);
            self.state_machines.push(sm.clone());
            return sm;
        }

        let end = sm.add_state("End", AsyncStateKind::End);

        // Create branch states from start
        for (branch_idx, &yield_count) in branches.iter().enumerate() {
            let branch_start = sm.add_state(
                &format!("Branch{branch_idx}_Start"),
                AsyncStateKind::Resumable,
            );
            sm.add_transition(0, branch_start);

            let mut prev_state = branch_start;

            for i in 0..yield_count {
                let suspended = sm.add_state(
                    &format!("Branch{branch_idx}_Await{i}"),
                    AsyncStateKind::Suspended,
                );
                {
                    let t = sm.add_transition(prev_state, suspended);
                    t.is_yield = true;
                }
                sm.add_yield_point(prev_state, suspended);
                prev_state = suspended;
            }

            // Connect to end
            sm.add_transition(prev_state, end);
        }

        self.state_machines.push(sm.clone());
        sm
    }

    /// Clear all extracted state machines
    pub fn clear(&mut self) {
        self.state_machines.clear();
    }

    /// Get a state machine by function name
    #[must_use]
    pub fn get_by_name(&self, name: &str) -> Option<&AsyncStateMachine> {
        self.state_machines.iter().find(|sm| sm.name == name)
    }

    /// Get total yield point count across all extracted state machines
    #[must_use]
    pub fn total_yield_count(&self) -> usize {
        self.state_machines
            .iter()
            .map(AsyncStateMachine::yield_count)
            .sum()
    }

    /// Find all state machines with potential deadlocks
    #[must_use]
    pub fn find_deadlocking_machines(&self) -> Vec<(&AsyncStateMachine, Vec<usize>)> {
        self.state_machines
            .iter()
            .map(|sm| (sm, sm.find_deadlocks()))
            .filter(|(_, deadlocks)| !deadlocks.is_empty())
            .collect()
    }

    /// Find all state machines that cannot terminate
    #[must_use]
    pub fn find_non_terminating_machines(&self) -> Vec<&AsyncStateMachine> {
        self.state_machines
            .iter()
            .filter(|sm| !sm.can_terminate())
            .collect()
    }
}

// ============================================
// Phase 6.1: Wire to MIR (DIRECTIVE_TLA_EXTRACT)
// ============================================

use crate::{MirFunction, MirType, Terminator};

/// Detect if a MIR function is async (has yield/suspend points)
///
/// This checks for:
/// - Coroutine/Generator terminators (Yield)
/// - Functions with Coroutine return types
#[must_use]
pub fn is_async_function(func: &MirFunction) -> bool {
    // Check if any block has Coroutine-related patterns
    for block in &func.blocks {
        // Look for patterns that indicate async/generator
        // In real rustc, async functions compile to generators with Yield terminators

        // Check for call targets that suggest awaiting
        if let Terminator::Call { func: callee, .. } = &block.terminator {
            let callee_lower = callee.to_lowercase();
            if callee_lower.contains("poll")
                || callee_lower.contains("future")
                || callee_lower.contains("await")
            {
                return true;
            }
        }
    }

    // Check return type for Future/Generator patterns
    if let MirType::Adt { name } = &func.return_type {
        let name_lower = name.to_lowercase();
        if name_lower.contains("future")
            || name_lower.contains("generator")
            || name_lower.contains("coroutine")
        {
            return true;
        }
    }

    // Check function name patterns
    let name_lower = func.name.to_lowercase();
    if name_lower.starts_with("async_") || name_lower.contains("_async") {
        return true;
    }

    false
}

/// Result of extracting state machines from MIR functions
#[derive(Debug)]
pub struct MirExtractionResult {
    /// Extracted state machines for async functions
    pub state_machines: Vec<AsyncStateMachine>,
    /// Functions detected as async
    pub async_functions: Vec<String>,
    /// Analysis results
    pub analysis: AsyncAnalysisResult,
    /// Warnings during extraction
    pub warnings: Vec<ExtractionWarning>,
}

impl AsyncStateMachineExtractor {
    /// Extract state machines from MIR functions
    ///
    /// This is the main entry point for Phase 6.1: wiring the extractor
    /// to the compiler. It processes all functions and extracts state
    /// machines from those detected as async.
    ///
    /// # Arguments
    /// * `funcs` - Slice of MIR functions to analyze
    ///
    /// # Returns
    /// MirExtractionResult containing all extracted state machines
    pub fn extract_from_mir(&mut self, funcs: &[MirFunction]) -> MirExtractionResult {
        let mut result = MirExtractionResult {
            state_machines: Vec::new(),
            async_functions: Vec::new(),
            analysis: AsyncAnalysisResult::default(),
            warnings: Vec::new(),
        };

        for func in funcs {
            if is_async_function(func) {
                result.async_functions.push(func.name.clone());

                // Convert MirFunction to AsyncFunctionInfo
                let func_info = Self::mir_to_async_function_info(func);

                // Extract state machine
                let extraction = self.extract(&func_info);

                if !extraction.complete {
                    result.warnings.push(ExtractionWarning {
                        message: format!("Incomplete extraction for {}", func.name),
                        span: None,
                    });
                }
                result.warnings.extend(extraction.warnings);
                result.state_machines.push(extraction.state_machine);
            }
        }

        result.analysis = self.analyze();
        result
    }

    /// Convert MirFunction to AsyncFunctionInfo for extraction
    fn mir_to_async_function_info(func: &MirFunction) -> AsyncFunctionInfo {
        let mut yield_points = Vec::new();
        let mut basic_blocks = Vec::new();

        // Convert MIR basic blocks to AsyncFunctionInfo format
        for (block_idx, block) in func.blocks.iter().enumerate() {
            let (terminator, is_yield) = match &block.terminator {
                Terminator::Return => (BlockTerminator::Return, false),
                // Goto and Assert both use Goto terminator
                Terminator::Goto { .. } | Terminator::Assert { .. } => {
                    (BlockTerminator::Goto, false)
                }
                Terminator::Call { .. } => {
                    // Check if this call is an await point (poll call pattern)
                    if let Terminator::Call { func: callee, .. } = &block.terminator {
                        let callee_lower = callee.to_lowercase();
                        if callee_lower.contains("poll") || callee_lower.contains("await") {
                            // This is a yield point
                            yield_points.push(YieldPointInfo {
                                index: yield_points.len(),
                                block: block_idx,
                                awaited_expr: Some(callee.clone()),
                                future_type: None,
                                live_variables: vec![], // Would need liveness analysis
                                span: None,
                            });
                            (BlockTerminator::Yield, true)
                        } else {
                            (BlockTerminator::Call, false)
                        }
                    } else {
                        (BlockTerminator::Call, false)
                    }
                }
                Terminator::SwitchInt { .. } => (BlockTerminator::SwitchInt, false),
                Terminator::IndirectCall { .. } => (BlockTerminator::Call, false),
                Terminator::Unreachable => (BlockTerminator::Unreachable, false),
            };

            // Extract successors
            let successors = match &block.terminator {
                // All terminators with a single target successor
                Terminator::Goto { target }
                | Terminator::Call { target, .. }
                | Terminator::IndirectCall { target, .. }
                | Terminator::Assert { target, .. } => vec![*target],
                Terminator::SwitchInt {
                    targets, otherwise, ..
                } => {
                    let mut succs: Vec<usize> = targets.iter().map(|(_, t)| *t).collect();
                    succs.push(*otherwise);
                    succs
                }
                Terminator::Return | Terminator::Unreachable => vec![],
            };

            basic_blocks.push(BasicBlockInfo {
                index: block_idx,
                terminator,
                successors,
                is_yield,
            });
        }

        // Convert parameters
        let parameters = func
            .params
            .iter()
            .map(|(name, ty)| (name.clone(), mir_type_to_vc_type(ty)))
            .collect();

        AsyncFunctionInfo {
            name: func.name.clone(),
            is_async: true,
            return_type: Some(mir_type_to_vc_type(&func.return_type)),
            parameters,
            yield_points,
            basic_blocks,
            span: None,
        }
    }
}

/// Convert MirType to VcType for use in AsyncFunctionInfo
fn mir_type_to_vc_type(ty: &MirType) -> VcType {
    match ty {
        MirType::Bool => VcType::Bool,
        MirType::Int { signed, bits } => VcType::Int {
            signed: *signed,
            bits: *bits,
        },
        MirType::Float { bits } => VcType::Float { bits: *bits },
        MirType::Ref { inner, .. } => mir_type_to_vc_type(inner),
        MirType::Array { elem, len } => VcType::Array {
            elem: Box::new(mir_type_to_vc_type(elem)),
            len: Some(*len),
        },
        MirType::Tuple(elems) => VcType::Tuple(elems.iter().map(mir_type_to_vc_type).collect()),
        MirType::Adt { name } => VcType::Abstract(name.clone()),
        MirType::Closure { def_id, .. } => VcType::Abstract(def_id.clone()),
        MirType::FnPtr { .. } => VcType::Abstract("fn_ptr".to_string()),
        MirType::FnDef { name } => VcType::Abstract(format!("fn#{name}")),
    }
}

// ============================================
// Analysis Results
// ============================================

/// Analysis results for async state machines
#[derive(Debug, Default)]
pub struct AsyncAnalysisResult {
    /// Number of state machines analyzed
    pub machine_count: usize,
    /// Total states across all machines
    pub total_states: usize,
    /// Total transitions across all machines
    pub total_transitions: usize,
    /// Total yield points across all machines
    pub total_yield_points: usize,
    /// Machines with potential deadlocks
    pub deadlock_risks: Vec<String>,
    /// Machines that may not terminate
    pub non_terminating: Vec<String>,
    /// Complexity metrics
    pub complexity: AsyncComplexity,
}

/// Complexity metrics for async code
#[derive(Debug, Default)]
pub struct AsyncComplexity {
    /// Maximum states in any single machine
    pub max_states: usize,
    /// Maximum transitions in any single machine
    pub max_transitions: usize,
    /// Maximum yield points in any single machine
    pub max_yield_points: usize,
    /// Number of branching machines (non-sequential)
    pub branching_count: usize,
}

impl AsyncStateMachineExtractor {
    /// Analyze all extracted state machines
    #[must_use]
    pub fn analyze(&self) -> AsyncAnalysisResult {
        let mut result = AsyncAnalysisResult {
            machine_count: self.state_machines.len(),
            ..Default::default()
        };

        for sm in &self.state_machines {
            result.total_states += sm.states.len();
            result.total_transitions += sm.transitions.len();
            result.total_yield_points += sm.yield_count();

            result.complexity.max_states = result.complexity.max_states.max(sm.states.len());
            result.complexity.max_transitions =
                result.complexity.max_transitions.max(sm.transitions.len());
            result.complexity.max_yield_points =
                result.complexity.max_yield_points.max(sm.yield_count());

            if !sm.is_sequential() {
                result.complexity.branching_count += 1;
            }

            let deadlocks = sm.find_deadlocks();
            if !deadlocks.is_empty() {
                result.deadlock_risks.push(sm.name.clone());
            }

            if !sm.can_terminate() {
                result.non_terminating.push(sm.name.clone());
            }
        }

        result
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
    fn test_extractor_with_options() {
        let options = ExtractionOptions {
            include_spans: true,
            track_captured_variables: true,
            max_states: 100,
        };
        let extractor = AsyncStateMachineExtractor::with_options(options.clone());
        assert!(extractor.options.include_spans);
        assert!(extractor.options.track_captured_variables);
        assert_eq!(extractor.options.max_states, 100);
    }

    #[test]
    fn test_extract_sequential_empty() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let sm = extractor.extract_sequential("empty_async", 0);

        assert_eq!(sm.states.len(), 2); // Start + End
        assert_eq!(sm.yield_count(), 0);
        assert!(sm.can_terminate());
    }

    #[test]
    fn test_extract_sequential_one_yield() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let sm = extractor.extract_sequential("single_await", 1);

        assert_eq!(sm.yield_count(), 1);
        assert!(sm.can_terminate());
        assert!(sm.find_deadlocks().is_empty());
    }

    #[test]
    fn test_extract_sequential_multiple_yields() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let sm = extractor.extract_sequential("multi_await", 3);

        assert_eq!(sm.yield_count(), 3);
        assert!(sm.can_terminate());
        assert!(sm.is_sequential());
    }

    #[test]
    fn test_extract_branching_empty() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let sm = extractor.extract_branching("empty_branch", &[]);

        assert!(sm.can_terminate());
    }

    #[test]
    fn test_extract_branching_simple() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let sm = extractor.extract_branching("if_await", &[1, 1]);

        // Start + End + 2 branches with 2 states each = 6 states
        assert!(sm.states.len() >= 4);
        assert!(!sm.is_sequential()); // Has branches
        assert!(sm.can_terminate());
    }

    #[test]
    fn test_extract_branching_asymmetric() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let sm = extractor.extract_branching("asymmetric", &[2, 1, 3]);

        assert!(!sm.is_sequential());
        assert!(sm.can_terminate());
        assert_eq!(sm.yield_count(), 6); // 2 + 1 + 3
    }

    #[test]
    fn test_get_by_name() {
        let mut extractor = AsyncStateMachineExtractor::new();
        extractor.extract_sequential("func_a", 1);
        extractor.extract_sequential("func_b", 2);

        assert!(extractor.get_by_name("func_a").is_some());
        assert!(extractor.get_by_name("func_b").is_some());
        assert!(extractor.get_by_name("func_c").is_none());
    }

    #[test]
    fn test_total_yield_count() {
        let mut extractor = AsyncStateMachineExtractor::new();
        extractor.extract_sequential("func_a", 2);
        extractor.extract_sequential("func_b", 3);

        assert_eq!(extractor.total_yield_count(), 5);
    }

    #[test]
    fn test_clear() {
        let mut extractor = AsyncStateMachineExtractor::new();
        extractor.extract_sequential("func", 1);
        assert_eq!(extractor.state_machines.len(), 1);

        extractor.clear();
        assert!(extractor.state_machines.is_empty());
    }

    #[test]
    fn test_extract_from_async_function_info() {
        let mut extractor = AsyncStateMachineExtractor::new();

        let func = AsyncFunctionInfo {
            name: "fetch_data".to_string(),
            is_async: true,
            return_type: None,
            parameters: vec![],
            yield_points: vec![YieldPointInfo {
                index: 0,
                block: 1,
                awaited_expr: Some("fetch()".to_string()),
                future_type: Some("impl Future<Output=Data>".to_string()),
                live_variables: vec!["url".to_string()],
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

    #[test]
    fn test_extract_non_async_warning() {
        let mut extractor = AsyncStateMachineExtractor::new();

        let func = AsyncFunctionInfo {
            name: "sync_func".to_string(),
            is_async: false,
            return_type: None,
            parameters: vec![],
            yield_points: vec![],
            basic_blocks: vec![],
            span: None,
        };

        let result = extractor.extract(&func);
        assert!(!result.warnings.is_empty());
        assert!(result.warnings[0].message.contains("not async"));
    }

    #[test]
    fn test_analyze_empty() {
        let extractor = AsyncStateMachineExtractor::new();
        let result = extractor.analyze();

        assert_eq!(result.machine_count, 0);
        assert_eq!(result.total_states, 0);
    }

    #[test]
    fn test_analyze_multiple() {
        let mut extractor = AsyncStateMachineExtractor::new();
        extractor.extract_sequential("func_a", 2);
        extractor.extract_branching("func_b", &[1, 2]);

        let result = extractor.analyze();
        assert_eq!(result.machine_count, 2);
        assert!(result.total_states > 0);
        assert!(result.total_yield_points > 0);
        assert!(result.complexity.branching_count >= 1);
    }

    #[test]
    fn test_find_deadlocking_machines() {
        let mut extractor = AsyncStateMachineExtractor::new();
        // Sequential machines shouldn't have deadlocks
        extractor.extract_sequential("safe", 2);

        let deadlocks = extractor.find_deadlocking_machines();
        assert!(deadlocks.is_empty());
    }

    #[test]
    fn test_find_non_terminating_machines() {
        let mut extractor = AsyncStateMachineExtractor::new();
        extractor.extract_sequential("safe", 2);

        let non_term = extractor.find_non_terminating_machines();
        assert!(non_term.is_empty());
    }

    #[test]
    fn test_extraction_options_default() {
        let options = ExtractionOptions::default();
        assert!(!options.include_spans);
        assert!(!options.track_captured_variables);
        assert_eq!(options.max_states, 0);
    }

    #[test]
    fn test_block_terminator_equality() {
        assert_eq!(BlockTerminator::Goto, BlockTerminator::Goto);
        assert_ne!(BlockTerminator::Goto, BlockTerminator::Return);
        assert_ne!(BlockTerminator::Yield, BlockTerminator::Call);
    }

    // ============================================
    // Phase 6.1: MIR Extraction Tests
    // ============================================

    #[test]
    fn test_is_async_function_by_name() {
        use crate::{BasicBlock, MirFunction, MirType, Terminator};

        let async_func = MirFunction {
            name: "async_fetch_data".to_string(),
            params: vec![],
            return_type: MirType::Bool,
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        assert!(is_async_function(&async_func));

        let sync_func = MirFunction {
            name: "sync_compute".to_string(),
            params: vec![],
            return_type: MirType::Bool,
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        assert!(!is_async_function(&sync_func));
    }

    #[test]
    fn test_is_async_function_by_return_type() {
        use crate::{BasicBlock, MirFunction, MirType, Terminator};

        let future_func = MirFunction {
            name: "some_func".to_string(),
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

        assert!(is_async_function(&future_func));
    }

    #[test]
    fn test_is_async_function_by_poll_call() {
        use crate::{BasicBlock, Local, MirFunction, MirType, Place, Terminator};

        let poll_func = MirFunction {
            name: "run".to_string(),
            params: vec![],
            return_type: MirType::Bool,
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Call {
                    func: "Future::poll".to_string(),
                    args: vec![],
                    destination: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    target: 1,
                    span: SourceSpan::default(),
                    generic_args: vec![],
                },
            }],
            locals: vec![],
            span: SourceSpan::default(),
        };

        assert!(is_async_function(&poll_func));
    }

    #[test]
    fn test_extract_from_mir_empty() {
        let mut extractor = AsyncStateMachineExtractor::new();
        let funcs: Vec<MirFunction> = vec![];

        let result = extractor.extract_from_mir(&funcs);

        assert!(result.state_machines.is_empty());
        assert!(result.async_functions.is_empty());
    }

    #[test]
    fn test_extract_from_mir_async_function() {
        use crate::{BasicBlock, Local, MirFunction, MirType, Place, Terminator};

        let mut extractor = AsyncStateMachineExtractor::new();

        // Simulate an async function with poll calls
        let async_func = MirFunction {
            name: "async_handler".to_string(),
            params: vec![],
            return_type: MirType::Adt {
                name: "impl Future<Output=()>".to_string(),
            },
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "poll_future".to_string(),
                        args: vec![],
                        destination: Place {
                            local: Local(0),
                            projections: vec![],
                        },
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
            locals: vec![],
            span: SourceSpan::default(),
        };

        let result = extractor.extract_from_mir(&[async_func]);

        assert_eq!(result.async_functions.len(), 1);
        assert_eq!(result.async_functions[0], "async_handler");
        assert_eq!(result.state_machines.len(), 1);
    }

    #[test]
    fn test_mir_to_vc_type_conversion() {
        use crate::MirType;

        assert!(matches!(mir_type_to_vc_type(&MirType::Bool), VcType::Bool));
        assert!(matches!(
            mir_type_to_vc_type(&MirType::Int {
                signed: true,
                bits: 32
            }),
            VcType::Int {
                signed: true,
                bits: 32
            }
        ));
        assert!(matches!(
            mir_type_to_vc_type(&MirType::Adt {
                name: "MyStruct".to_string()
            }),
            VcType::Abstract(_)
        ));
    }
}
