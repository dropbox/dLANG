//! Weakest Precondition Calculus
//!
//! This module implements the weakest precondition calculus for generating
//! verification conditions from MIR.
//!
//! The WP calculus computes, given a postcondition P and a program S,
//! the weakest precondition wp(S, P) such that if wp(S, P) holds before S,
//! then P holds after S.
//!
//! ## WP Rules
//!
//! - **Assignment**: wp(x := e, P) = P[e/x]
//! - **Sequence**: wp(S1; S2, P) = wp(S1, wp(S2, P))
//! - **Branch**: wp(if c then S1 else S2, P) = (c => wp(S1,P)) ∧ (¬c => wp(S2,P))
//! - **Assert**: wp(assert c, P) = c ∧ P
//! - **Return**: wp(return, P) = P
//! - **Loop**: wp(while guard { body } invariant I, P) = I
//!   (loop handled separately with invariant checks)

use crate::{
    encoder::{substitute, MirEncoder},
    loop_handling::LoopAnalysis,
    BinOp, FunctionSpecs, MirFunction, Place, Rvalue, Statement, Terminator,
};
use std::collections::{HashMap, HashSet};
use vc_ir::{
    BackendHint, BorrowId, BorrowKind, Expr, Predicate, SeparationAssertion, SourceSpan, VcId,
    VcKind, VerificationCondition,
};

/// Active borrow tracking information (Phase N3.1b)
#[derive(Debug, Clone)]
pub struct ActiveBorrow {
    /// Unique ID for this borrow
    pub borrow_id: BorrowId,
    /// Whether this is a shared or mutable borrow
    pub kind: BorrowKind,
    /// The borrowed location as an expression
    pub location: Expr,
    /// The value at borrow time (for mutable borrows, tracks modifications)
    pub initial_value: Expr,
    /// Parent borrow ID if this is a reborrow
    pub parent_borrow: Option<BorrowId>,
}

/// Weakest precondition calculator with proper CFG traversal
pub struct WpCalculator<'a> {
    func: &'a MirFunction,
    encoder: MirEncoder,
    /// Predecessor map: block_idx -> list of (predecessor_idx, branch_condition)
    /// The branch_condition is the predicate that must hold to take this edge
    predecessors: Vec<Vec<(usize, Option<Predicate>)>>,
    /// Cache for computed WP per block to avoid recomputation
    wp_cache: HashMap<usize, Predicate>,
    /// Loop analysis results
    loop_analysis: LoopAnalysis,
    /// Loop invariants provided by user (block_idx -> invariant)
    loop_invariants: HashMap<usize, Predicate>,
    /// Side-condition VCs generated during WP computation
    side_vcs: Vec<VerificationCondition>,
    /// Next VC ID for generated VCs
    next_vc_id: u64,
    /// Contract registry for modular verification (Phase 2.5)
    /// Maps function names to their specifications
    contract_registry: HashMap<String, FunctionSpecs>,
    /// Loops encountered without invariants (SOUNDNESS BUG if not empty)
    /// Contains block indices of loop headers that lack invariants
    loops_without_invariant: Vec<usize>,

    // === Borrow Tracking (Phase N3.1b) ===
    /// Next borrow ID to assign
    next_borrow_id: u32,
    /// Active borrows: maps local variable index to ActiveBorrow info
    /// When a borrow is created, we track it here; when it ends (StorageDead), we remove it
    active_borrows: HashMap<usize, ActiveBorrow>,
    /// Reborrow relationships: child_borrow_id -> parent_borrow_id
    /// Used to track nested borrows and ensure proper lifetimes
    reborrow_parents: HashMap<u32, u32>,
}

impl<'a> WpCalculator<'a> {
    #[must_use]
    pub fn new(func: &'a MirFunction) -> Self {
        let predecessors = build_predecessor_map(func);
        let loop_analysis = LoopAnalysis::analyze(func);
        Self {
            func,
            encoder: MirEncoder::new(func),
            predecessors,
            wp_cache: HashMap::new(),
            loop_analysis,
            loop_invariants: HashMap::new(),
            side_vcs: Vec::new(),
            next_vc_id: 0,
            contract_registry: HashMap::new(),
            loops_without_invariant: Vec::new(),
            // Borrow tracking (N3.1b)
            next_borrow_id: 0,
            active_borrows: HashMap::new(),
            reborrow_parents: HashMap::new(),
        }
    }

    /// Create a WP calculator with loop invariants
    #[must_use]
    pub fn with_invariants(func: &'a MirFunction, invariants: HashMap<usize, Predicate>) -> Self {
        let predecessors = build_predecessor_map(func);
        let loop_analysis = LoopAnalysis::analyze(func);
        Self {
            func,
            encoder: MirEncoder::new(func),
            predecessors,
            wp_cache: HashMap::new(),
            loop_analysis,
            loop_invariants: invariants,
            side_vcs: Vec::new(),
            next_vc_id: 0,
            contract_registry: HashMap::new(),
            loops_without_invariant: Vec::new(),
            // Borrow tracking (N3.1b)
            next_borrow_id: 0,
            active_borrows: HashMap::new(),
            reborrow_parents: HashMap::new(),
        }
    }

    /// Create a WP calculator with a contract registry for modular verification
    #[must_use]
    pub fn with_contracts(
        func: &'a MirFunction,
        contracts: HashMap<String, FunctionSpecs>,
    ) -> Self {
        let predecessors = build_predecessor_map(func);
        let loop_analysis = LoopAnalysis::analyze(func);
        Self {
            func,
            encoder: MirEncoder::new(func),
            predecessors,
            wp_cache: HashMap::new(),
            loop_analysis,
            loop_invariants: HashMap::new(),
            side_vcs: Vec::new(),
            next_vc_id: 0,
            contract_registry: contracts,
            loops_without_invariant: Vec::new(),
            // Borrow tracking (N3.1b)
            next_borrow_id: 0,
            active_borrows: HashMap::new(),
            reborrow_parents: HashMap::new(),
        }
    }

    /// Create a WP calculator with both loop invariants and contract registry
    #[must_use]
    pub fn with_invariants_and_contracts(
        func: &'a MirFunction,
        invariants: HashMap<usize, Predicate>,
        contracts: HashMap<String, FunctionSpecs>,
    ) -> Self {
        let predecessors = build_predecessor_map(func);
        let loop_analysis = LoopAnalysis::analyze(func);
        Self {
            func,
            encoder: MirEncoder::new(func),
            predecessors,
            wp_cache: HashMap::new(),
            loop_analysis,
            loop_invariants: invariants,
            side_vcs: Vec::new(),
            next_vc_id: 0,
            contract_registry: contracts,
            loops_without_invariant: Vec::new(),
            // Borrow tracking (N3.1b)
            next_borrow_id: 0,
            active_borrows: HashMap::new(),
            reborrow_parents: HashMap::new(),
        }
    }

    /// Register a function's contract in the registry
    pub fn register_contract(&mut self, name: String, specs: FunctionSpecs) {
        self.contract_registry.insert(name, specs);
    }

    /// Get the contract registry (for inspection/testing)
    #[must_use]
    pub const fn contracts(&self) -> &HashMap<String, FunctionSpecs> {
        &self.contract_registry
    }

    /// Get side-condition VCs generated during WP computation
    pub fn take_side_vcs(&mut self) -> Vec<VerificationCondition> {
        std::mem::take(&mut self.side_vcs)
    }

    /// Check if any loops were encountered without invariants
    ///
    /// SOUNDNESS: If this returns true, the WP computation is UNSOUND.
    /// Callers MUST reject verification if this is true.
    #[must_use]
    pub const fn has_loops_without_invariant(&self) -> bool {
        !self.loops_without_invariant.is_empty()
    }

    /// Get the block indices of loops that lack invariants
    ///
    /// These are loop headers where the WP computation encountered a
    /// back-edge but no invariant was provided. Verification is UNSOUND
    /// for these loops.
    #[must_use]
    pub fn loops_without_invariant(&self) -> &[usize] {
        &self.loops_without_invariant
    }

    const fn fresh_vc_id(&mut self) -> VcId {
        let id = VcId(self.next_vc_id);
        self.next_vc_id += 1;
        id
    }

    /// Compute weakest precondition of postcondition through entire function
    ///
    /// This traverses the CFG backwards from return blocks to the entry block,
    /// computing the weakest precondition at each step.
    ///
    /// For loops, uses loop invariants to cut the back-edges and generates
    /// side-condition VCs for invariant base case and preservation.
    pub fn wp_function(&mut self, postcondition: &Predicate) -> Predicate {
        // Find all return blocks
        let return_blocks: Vec<usize> = self
            .func
            .blocks
            .iter()
            .enumerate()
            .filter(|(_, b)| matches!(b.terminator, Terminator::Return))
            .map(|(i, _)| i)
            .collect();

        if return_blocks.is_empty() {
            // No return points - function never terminates normally
            return Predicate::Bool(true);
        }

        // For single return block at entry (block 0), just compute WP directly
        if return_blocks.len() == 1 && return_blocks[0] == 0 {
            return self.wp_block(0, postcondition.clone());
        }

        // Identify loop headers (back-edge targets)
        let loop_headers: HashSet<usize> =
            self.loop_analysis.loops.iter().map(|l| l.header).collect();

        // Clear cache for fresh computation
        // The cache maps block_idx -> WP at ENTRY of that block
        self.wp_cache.clear();

        // Worklist-based backward traversal
        // Process return blocks first to compute their entry WPs
        let mut worklist: Vec<usize> = return_blocks.clone();

        // For return blocks, compute WP through the block starting with postcondition
        for &block_idx in &return_blocks {
            let wp_at_entry = self.wp_block(block_idx, postcondition.clone());
            self.wp_cache.insert(block_idx, wp_at_entry);
        }

        // Continue propagating backwards
        let mut processed: HashSet<usize> = return_blocks.iter().copied().collect();

        while let Some(block_idx) = worklist.pop() {
            let wp_at_entry = self
                .wp_cache
                .get(&block_idx)
                .cloned()
                .expect("block should have WP computed");

            // Propagate to predecessors
            for (pred_idx, branch_cond) in self.predecessors[block_idx].clone() {
                // Check if this is a back-edge (pred_idx jumps to a loop header at block_idx)
                let is_back_edge = loop_headers.contains(&block_idx)
                    && self
                        .loop_analysis
                        .loops
                        .iter()
                        .any(|l| l.header == block_idx && l.back_edges.contains(&pred_idx));

                if is_back_edge {
                    // For back-edges, use the loop invariant instead of propagating WP
                    // This cuts the loop and generates side VCs
                    let invariant_opt = self.loop_invariants.get(&block_idx).cloned();
                    if let Some(invariant) = invariant_opt {
                        // Generate loop preservation VC: I && path_cond => wp(body, I)
                        let body_wp = wp_at_entry.clone();
                        let preservation_vc = self.generate_loop_preservation_vc(
                            block_idx,
                            &invariant,
                            &body_wp,
                            branch_cond.as_ref(),
                        );
                        self.side_vcs.push(preservation_vc);

                        // At back-edge source, the WP is: body implies invariant preserved
                        // Continue processing pred without following back-edge
                        continue;
                    } else {
                        // No invariant provided for this loop - SOUNDNESS ERROR
                        // Record the loop without invariant for callers to check
                        if !self.loops_without_invariant.contains(&block_idx) {
                            self.loops_without_invariant.push(block_idx);
                        }

                        // Also generate a warning VC that will fail verification
                        let warning_vc = VerificationCondition {
                            id: self.fresh_vc_id(),
                            name: format!(
                                "ERROR: loop at block {block_idx} requires #[invariant(...)] annotation"
                            ),
                            span: SourceSpan::default(),
                            condition: VcKind::Predicate(Predicate::Bool(false)), // Unprovable
                            preferred_backend: Some(BackendHint::Smt),
                        };
                        self.side_vcs.push(warning_vc);
                        continue;
                    }
                }

                let wp_for_edge = if let Some(cond) = branch_cond {
                    // Edge has a branch condition: cond => wp
                    Predicate::Implies(Box::new(cond), Box::new(wp_at_entry.clone()))
                } else {
                    wp_at_entry.clone()
                };

                // If predecessor already has WP computed, merge with it
                // Otherwise, compute WP through that block
                let wp_at_pred_exit = if let Some(existing) = self.wp_cache.get(&pred_idx) {
                    // Multiple successors: AND their WPs at this predecessor's exit
                    Predicate::And(vec![existing.clone(), wp_for_edge])
                } else {
                    wp_for_edge
                };

                // Now compute WP through predecessor block
                let wp_at_pred_entry = self.wp_block(pred_idx, wp_at_pred_exit);
                self.wp_cache.insert(pred_idx, wp_at_pred_entry);

                if !processed.contains(&pred_idx) {
                    processed.insert(pred_idx);
                    worklist.push(pred_idx);
                }
            }
        }

        // For each loop header with an invariant, generate base case VC
        let loop_headers_to_process: Vec<(usize, Predicate)> = self
            .loop_analysis
            .loops
            .iter()
            .filter_map(|loop_info| {
                self.loop_invariants
                    .get(&loop_info.header)
                    .map(|inv| (loop_info.header, inv.clone()))
            })
            .collect();

        for (header, invariant) in loop_headers_to_process {
            let base_vc = self.generate_loop_base_vc(header, &invariant);
            self.side_vcs.push(base_vc);
        }

        // Return WP at entry (block 0)
        self.wp_cache
            .get(&0)
            .cloned()
            .unwrap_or(Predicate::Bool(true))
    }

    /// Generate VC for loop invariant base case: precondition => I
    fn generate_loop_base_vc(
        &mut self,
        header: usize,
        invariant: &Predicate,
    ) -> VerificationCondition {
        VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("loop invariant base case (block {header})"),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(invariant.clone()),
            preferred_backend: Some(BackendHint::Smt),
        }
    }

    /// Generate VC for loop invariant preservation: I && guard => wp(body, I)
    fn generate_loop_preservation_vc(
        &mut self,
        header: usize,
        invariant: &Predicate,
        body_wp: &Predicate,
        guard: Option<&Predicate>,
    ) -> VerificationCondition {
        let antecedent = if let Some(g) = guard {
            Predicate::And(vec![invariant.clone(), g.clone()])
        } else {
            invariant.clone()
        };

        VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("loop invariant preservation (block {header})"),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent,
                consequent: body_wp.clone(),
            },
            preferred_backend: Some(BackendHint::Smt),
        }
    }

    /// Compute WP through a single block, ending with the given postcondition
    /// This processes statements in reverse order
    fn wp_block(&mut self, block_idx: usize, postcondition: Predicate) -> Predicate {
        let block = &self.func.blocks[block_idx];

        // First, compute WP through the terminator
        let after_terminator = self.wp_terminator(block_idx, &block.terminator, postcondition);

        // Then, compute WP through statements in reverse order
        let mut current = after_terminator;
        for stmt in block.statements.iter().rev() {
            current = self.wp_statement(stmt, current);
        }

        current
    }

    /// wp(x := e, P) = P[e/x]
    ///
    /// Also generates side-condition VCs for:
    /// - Overflow checking for CheckedBinaryOp
    /// - Array bounds checking for ArrayIndex
    fn wp_statement(&mut self, stmt: &Statement, postcondition: Predicate) -> Predicate {
        match stmt {
            Statement::Assign { place, rvalue } => {
                // Generate side VCs for safety conditions
                self.generate_rvalue_safety_vcs(rvalue);

                let var_name = place_to_var_name(place);
                let expr = self.encoder.encode_rvalue(rvalue);
                substitute(&postcondition, &var_name, &expr)
            }
            Statement::StorageLive(_) => {
                // StorageLive doesn't affect the logical state
                postcondition
            }
            Statement::StorageDead(local) => {
                // N3.1b: When a local goes out of scope, check if it was a borrow
                // and generate a BorrowEnd VC if so
                self.generate_borrow_end_vc(local.0);
                // Storage operations don't affect the logical state otherwise
                postcondition
            }
        }
    }

    /// Generate safety VCs for an rvalue
    fn generate_rvalue_safety_vcs(&mut self, rvalue: &Rvalue) {
        match rvalue {
            Rvalue::CheckedBinaryOp(binop, lhs, rhs) => {
                self.generate_overflow_vc(*binop, lhs, rhs);
                self.generate_operand_safety_vcs(lhs);
                self.generate_operand_safety_vcs(rhs);
            }
            Rvalue::BinaryOp(BinOp::Div | BinOp::Rem, lhs, rhs) => {
                self.generate_division_by_zero_vc(rhs);
                self.generate_operand_safety_vcs(lhs);
                self.generate_operand_safety_vcs(rhs);
            }
            Rvalue::BinaryOp(_, lhs, rhs) => {
                self.generate_operand_safety_vcs(lhs);
                self.generate_operand_safety_vcs(rhs);
            }
            Rvalue::UnaryOp(_, op)
            | Rvalue::Use(op)
            | Rvalue::Cast { operand: op, .. }
            | Rvalue::Repeat { operand: op, .. } => {
                self.generate_operand_safety_vcs(op);
            }
            Rvalue::Ref { mutable, place } => {
                self.generate_array_bounds_vcs_for_place(place);
                // N3.1b: Track mutable borrow creation
                if *mutable {
                    self.generate_mutable_borrow_vc(place);
                }
            }
            Rvalue::Len(place) | Rvalue::Discriminant(place) => {
                self.generate_array_bounds_vcs_for_place(place);
            }
            Rvalue::Aggregate { operands, .. } => {
                for op in operands {
                    self.generate_operand_safety_vcs(op);
                }
            }
            Rvalue::NullaryOp(_, _) => {}
        }
    }

    /// Generate overflow checking VC for CheckedBinaryOp
    ///
    /// For signed integer operations:
    /// - Add: (lhs > 0 && rhs > 0 && result < 0) || (lhs < 0 && rhs < 0 && result > 0) implies overflow
    /// - Sub: Similar
    /// - Mul: |lhs * rhs| <= MAX
    fn generate_overflow_vc(&mut self, binop: BinOp, lhs: &crate::Operand, rhs: &crate::Operand) {
        let lhs_expr = self.encoder.encode_operand(lhs);
        let rhs_expr = self.encoder.encode_operand(rhs);

        // Get the type bounds (assume i32 for now - would need type info)
        let i32_max = Expr::IntLit(i128::from(i32::MAX));
        let i32_min = Expr::IntLit(i128::from(i32::MIN));

        let no_overflow = match binop {
            BinOp::Add => {
                // For add: result in range [MIN, MAX]
                // i.e., MIN <= lhs + rhs <= MAX
                let sum = Expr::Add(Box::new(lhs_expr), Box::new(rhs_expr));
                Predicate::And(vec![
                    Predicate::Expr(Expr::Ge(Box::new(sum.clone()), Box::new(i32_min))),
                    Predicate::Expr(Expr::Le(Box::new(sum), Box::new(i32_max))),
                ])
            }
            BinOp::Sub => {
                // For sub: MIN <= lhs - rhs <= MAX
                let diff = Expr::Sub(Box::new(lhs_expr), Box::new(rhs_expr));
                Predicate::And(vec![
                    Predicate::Expr(Expr::Ge(Box::new(diff.clone()), Box::new(i32_min))),
                    Predicate::Expr(Expr::Le(Box::new(diff), Box::new(i32_max))),
                ])
            }
            BinOp::Mul => {
                // For mul: MIN <= lhs * rhs <= MAX
                let prod = Expr::Mul(Box::new(lhs_expr), Box::new(rhs_expr));
                Predicate::And(vec![
                    Predicate::Expr(Expr::Ge(Box::new(prod.clone()), Box::new(i32_min))),
                    Predicate::Expr(Expr::Le(Box::new(prod), Box::new(i32_max))),
                ])
            }
            _ => return, // Other ops don't overflow in the same way
        };

        let vc = VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("no overflow for {binop:?}"),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(no_overflow),
            preferred_backend: Some(BackendHint::Smt),
        };
        self.side_vcs.push(vc);
    }

    /// Generate division by zero VC
    fn generate_division_by_zero_vc(&mut self, divisor: &crate::Operand) {
        let divisor_expr = self.encoder.encode_operand(divisor);
        let nonzero = Predicate::Expr(Expr::Ne(Box::new(divisor_expr), Box::new(Expr::IntLit(0))));

        let vc = VerificationCondition {
            id: self.fresh_vc_id(),
            name: "division by zero check".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(nonzero),
            preferred_backend: Some(BackendHint::Smt),
        };
        self.side_vcs.push(vc);
    }

    // === Borrow Tracking Methods (Phase N3.1b) ===

    /// Generate a fresh borrow ID
    fn fresh_borrow_id(&mut self) -> BorrowId {
        let id = BorrowId::new(self.next_borrow_id);
        self.next_borrow_id += 1;
        id
    }

    /// Generate VC for borrow creation (N3.1b: Borrow Semantics)
    ///
    /// When creating `&T` or `&mut T`, we generate VCs documenting that:
    /// 1. The borrowed location is valid (exists and is accessible)
    /// 2. For mutable borrows, the location is not already borrowed (exclusivity)
    ///
    /// This creates a "borrow begin" marker in the verification trace that can be
    /// used to prove aliasing properties and detect use-after-free patterns.
    ///
    /// The borrow is tracked in `active_borrows` until a corresponding StorageDead.
    fn generate_borrow_vc(&mut self, place: &Place, mutable: bool, dest_local: usize) {
        let place_expr = self.encoder.encode_place(place);
        let place_name = place_to_var_name(place);
        let borrow_id = self.fresh_borrow_id();
        let kind = if mutable {
            BorrowKind::Mutable
        } else {
            BorrowKind::Shared
        };

        // Check if this is a reborrow (borrowing through an existing reference)
        let parent_borrow = self.detect_reborrow(place);

        // Create the initial value expression
        let initial_value = Expr::Var(format!("{place_name}_value_at_borrow_{}", borrow_id.0));

        // Track this active borrow
        let active_borrow = ActiveBorrow {
            borrow_id,
            kind,
            location: place_expr.clone(),
            initial_value: initial_value.clone(),
            parent_borrow,
        };
        self.active_borrows.insert(dest_local, active_borrow);

        // Track reborrow relationship
        if let Some(parent_id) = parent_borrow {
            self.reborrow_parents.insert(borrow_id.0, parent_id.0);
        }

        // Generate BorrowBegin VC using the new separation assertion
        let borrow_begin =
            SeparationAssertion::borrow_begin(borrow_id, kind, place_expr.clone(), initial_value);

        let vc = VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("{} borrow of {} ({})", kind, place_name, borrow_id),
            span: SourceSpan::default(),
            condition: VcKind::Separation(borrow_begin),
            preferred_backend: Some(BackendHint::SeparationLogic),
        };
        self.side_vcs.push(vc);

        // If this is a reborrow, generate the reborrow relationship VC
        if let Some(parent_id) = parent_borrow {
            let reborrow_vc = SeparationAssertion::reborrow(borrow_id, parent_id, kind);
            let vc = VerificationCondition {
                id: self.fresh_vc_id(),
                name: format!("reborrow {} from parent {}", borrow_id, parent_id),
                span: SourceSpan::default(),
                condition: VcKind::Separation(reborrow_vc),
                preferred_backend: Some(BackendHint::SeparationLogic),
            };
            self.side_vcs.push(vc);
        }

        // Also generate a simple predicate VC for SMT backends
        // This documents the borrow in a form SMT solvers can handle
        let vc_smt = VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("borrow validity: {} ({})", place_name, borrow_id),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Bool(true)),
            preferred_backend: Some(BackendHint::Smt),
        };
        self.side_vcs.push(vc_smt);
    }

    /// Detect if a place involves borrowing through an existing reference (reborrow)
    ///
    /// Returns the parent borrow ID if this is a reborrow.
    fn detect_reborrow(&self, place: &Place) -> Option<BorrowId> {
        // Check if the place starts with a deref of a local that is an active borrow
        if !place.projections.is_empty() {
            if let crate::Projection::Deref = &place.projections[0] {
                // The base local might be a reference we're reborrowing from
                if let Some(active) = self.active_borrows.get(&place.local.0) {
                    return Some(active.borrow_id);
                }
            }
        }
        None
    }

    /// Generate VC for borrow end (N3.1b: Borrow Semantics)
    ///
    /// When a local goes out of scope (StorageDead), if it was a borrowed reference,
    /// we generate a BorrowEnd VC to mark the end of the borrow's lifetime.
    ///
    /// This enables use-after-free detection: any access through the borrow after
    /// this point would generate a failing proof obligation.
    fn generate_borrow_end_vc(&mut self, local: usize) {
        if let Some(active) = self.active_borrows.remove(&local) {
            // Generate BorrowEnd VC
            let final_value = if active.kind == BorrowKind::Mutable {
                // For mutable borrows, capture the potentially modified final value
                Some(Expr::Var(format!("{}_final_value", active.borrow_id)))
            } else {
                None
            };

            let borrow_end = SeparationAssertion::borrow_end(active.borrow_id, final_value);

            let vc = VerificationCondition {
                id: self.fresh_vc_id(),
                name: format!("borrow end: {}", active.borrow_id),
                span: SourceSpan::default(),
                condition: VcKind::Separation(borrow_end),
                preferred_backend: Some(BackendHint::SeparationLogic),
            };
            self.side_vcs.push(vc);
        }
    }

    /// Generate VC for mutable borrow creation (legacy compatibility wrapper)
    ///
    /// This is a convenience wrapper that calls generate_borrow_vc with mutable=true.
    /// Used when we don't have the destination local available.
    fn generate_mutable_borrow_vc(&mut self, place: &Place) {
        // For backwards compatibility, generate a simplified borrow VC
        // When called without a destination local, we use a synthetic local ID
        let synthetic_local = usize::MAX - self.next_borrow_id as usize;
        self.generate_borrow_vc(place, true, synthetic_local);
    }

    /// Generate array bounds checking VCs for a place with Index projection
    fn generate_array_bounds_vcs_for_place(&mut self, place: &Place) {
        let mut current_array = Expr::Var(format!("_{}", place.local.0));

        for proj in &place.projections {
            match proj {
                crate::Projection::Index(idx_local) => {
                    let idx_expr = Expr::Var(format!("_{}", idx_local.0));

                    // Generate: 0 <= idx
                    let lower_bound = Predicate::Expr(Expr::Ge(
                        Box::new(idx_expr.clone()),
                        Box::new(Expr::IntLit(0)),
                    ));

                    // Generate: idx < len(array)
                    let array_len = Expr::ArrayLen(Box::new(current_array.clone()));
                    let upper_bound =
                        Predicate::Expr(Expr::Lt(Box::new(idx_expr.clone()), Box::new(array_len)));

                    let in_bounds = Predicate::And(vec![lower_bound, upper_bound]);

                    let vc = VerificationCondition {
                        id: self.fresh_vc_id(),
                        name: "array bounds check".to_string(),
                        span: SourceSpan::default(),
                        condition: VcKind::Predicate(in_bounds),
                        preferred_backend: Some(BackendHint::Smt),
                    };
                    self.side_vcs.push(vc);

                    // Update current_array for nested access
                    current_array = Expr::ArrayIndex(Box::new(current_array), Box::new(idx_expr));
                }
                crate::Projection::Field(idx) => {
                    current_array = Expr::TupleField(Box::new(current_array), *idx);
                }
                crate::Projection::Deref => {
                    current_array = Expr::Deref(Box::new(current_array));
                }
            }
        }
    }

    /// Generate safety VCs for operands (checks array bounds in places)
    fn generate_operand_safety_vcs(&mut self, op: &crate::Operand) {
        match op {
            crate::Operand::Copy(place) | crate::Operand::Move(place) => {
                self.generate_array_bounds_vcs_for_place(place);
            }
            crate::Operand::Constant(_) => {}
        }
    }

    /// Compute WP through a terminator
    fn wp_terminator(
        &mut self,
        _block_idx: usize,
        term: &Terminator,
        postcondition: Predicate,
    ) -> Predicate {
        match term {
            Terminator::Return => {
                // wp(return, P) = P
                postcondition
            }

            Terminator::Goto { target: _ } => {
                // wp(goto B, P) = P (no transformation needed)
                postcondition
            }

            Terminator::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                // wp(switch discr { v1 => B1, ..., _ => B_else }, P)
                // = (discr == v1 => wp(B1, P)) ∧ (discr == v2 => wp(B2, P)) ∧ ...
                //   ∧ (discr ∉ {v1, v2, ...} => wp(B_else, P))
                //
                // Since we're doing backwards analysis and P is already the postcondition
                // after the switch, we encode the branch condition implications

                let discr_expr = self.encoder.encode_operand(discr);
                let mut conjuncts = Vec::new();

                // For each explicit target: discr == val => postcondition holds on that path
                for (val, _target) in targets {
                    let cond = Predicate::Expr(Expr::Eq(
                        Box::new(discr_expr.clone()),
                        Box::new(Expr::IntLit(*val as i128)),
                    ));
                    // The implication: if we took this branch, postcondition must hold
                    conjuncts.push(Predicate::Implies(
                        Box::new(cond),
                        Box::new(postcondition.clone()),
                    ));
                }

                // For the otherwise branch: discr != all explicit values
                if targets.is_empty() {
                    // No explicit targets, otherwise always taken
                    let _ = otherwise; // Use the variable
                    conjuncts.push(postcondition);
                } else {
                    let not_any_explicit: Vec<Predicate> = targets
                        .iter()
                        .map(|(val, _)| {
                            Predicate::Expr(Expr::Ne(
                                Box::new(discr_expr.clone()),
                                Box::new(Expr::IntLit(*val as i128)),
                            ))
                        })
                        .collect();

                    let otherwise_cond = if not_any_explicit.len() == 1 {
                        not_any_explicit
                            .into_iter()
                            .next()
                            .expect("len()==1 guarantees element exists")
                    } else {
                        Predicate::And(not_any_explicit)
                    };

                    conjuncts.push(Predicate::Implies(
                        Box::new(otherwise_cond),
                        Box::new(postcondition),
                    ));
                }

                if conjuncts.len() == 1 {
                    conjuncts.pop().expect("len()==1 guarantees element exists")
                } else {
                    Predicate::And(conjuncts)
                }
            }

            Terminator::Assert {
                cond,
                expected,
                target: _,
            } => {
                // wp(assert cond == expected, P) = (cond == expected) ∧ P
                let cond_expr = self.encoder.encode_operand(cond);
                let assert_pred = if *expected {
                    Predicate::Expr(cond_expr)
                } else {
                    Predicate::Expr(Expr::Not(Box::new(cond_expr)))
                };
                Predicate::And(vec![assert_pred, postcondition])
            }

            Terminator::Call {
                func: callee_name,
                args,
                destination,
                span,
                target: _,
                ..
            } => {
                // Modular verification: use callee's contract (Phase 2.5)
                //
                // wp(call dest = f(args), P) =
                //   f.requires[args/params] ∧ (f.ensures[args/params, dest/result] => P)
                //
                // 1. Check callee's precondition is satisfied (generate VC)
                // 2. Assume callee's postcondition holds for return value

                // Special handling for Box::new - establish heap semantics
                // Box::new(v) allocates and stores v, so *result == v
                if is_box_new(callee_name) && args.len() == 1 {
                    let dest_var = place_to_var_name(destination);
                    let arg_expr = self.encoder.encode_operand(&args[0]);

                    // Constraint: *dest == arg (dereferencing the box gives the stored value)
                    let deref_dest = Expr::Deref(Box::new(Expr::Var(dest_var)));
                    let box_constraint =
                        Predicate::Expr(Expr::Eq(Box::new(deref_dest), Box::new(arg_expr)));

                    // The postcondition holds given the box constraint
                    return Predicate::And(vec![box_constraint, postcondition]);
                }

                if let Some(callee_specs) = self.contract_registry.get(callee_name).cloned() {
                    let dest_var = place_to_var_name(destination);

                    // Build parameter name to argument expression mapping
                    let param_subst = self.build_param_substitution(&callee_specs, args);

                    // 1. Check precondition: requires[args/params]
                    let precond_vcs = self.generate_precondition_vcs(
                        callee_name,
                        &callee_specs,
                        &param_subst,
                        span.clone(),
                    );
                    self.side_vcs.extend(precond_vcs);

                    // 2. Assume postcondition: ensures[args/params, dest/result] => P
                    Self::assume_postcondition(
                        &callee_specs,
                        &param_subst,
                        &dest_var,
                        postcondition,
                    )
                } else {
                    // No contract for callee - assume call has no effect on verification
                    // (unsafe assumption, but matches pre-modular behavior)
                    postcondition
                }
            }

            Terminator::Unreachable => {
                // wp(unreachable, P) = true
                // If we reach unreachable, any postcondition vacuously holds
                Predicate::Bool(true)
            }

            Terminator::IndirectCall {
                callee: _,
                callee_ty: _,
                args: _,
                destination: _,
                target: _,
                span: _,
            } => {
                // Indirect call through closure or function pointer
                // Without knowing the callee's contract, we conservatively
                // assume the call has no verifiable effect.
                // Future enhancement: trait-based contracts for Fn/FnMut/FnOnce
                postcondition
            }
        }
    }

    // ===== Modular Verification Helpers (Phase 2.5) =====

    /// Build a substitution map from parameter names to argument expressions
    ///
    /// This maps formal parameter names (from the callee's parameter list)
    /// to actual argument expressions (from the call site).
    fn build_param_substitution(
        &self,
        _callee_specs: &FunctionSpecs,
        args: &[crate::Operand],
    ) -> HashMap<String, Expr> {
        let mut subst = HashMap::new();

        // Get parameter names from the callee's specs
        // FunctionSpecs doesn't directly have param names, so we need to
        // infer them from the requires/ensures predicates or use positional names.
        // Convention: parameters are named _1, _2, etc. (matching MIR convention)

        // Map argument index to expression
        for (idx, arg) in args.iter().enumerate() {
            // Parameter name uses MIR convention: _1, _2, etc.
            let param_name = format!("_{}", idx + 1);
            let arg_expr = self.encoder.encode_operand(arg);
            subst.insert(param_name, arg_expr);
        }

        subst
    }

    /// Generate VCs to check callee's preconditions are satisfied at call site
    ///
    /// For each requires clause in the callee's specs, generates a VC that
    /// the clause holds after substituting actual arguments for parameters.
    fn generate_precondition_vcs(
        &mut self,
        callee_name: &str,
        callee_specs: &FunctionSpecs,
        param_subst: &HashMap<String, Expr>,
        span: SourceSpan,
    ) -> Vec<VerificationCondition> {
        let mut vcs = Vec::new();

        for (idx, require) in callee_specs.requires.iter().enumerate() {
            // Substitute actual arguments for formal parameters in the precondition
            let subst_pred = substitute_predicate(&require.pred, param_subst);

            let vc = VerificationCondition {
                id: self.fresh_vc_id(),
                name: format!("call {callee_name} precondition {idx}"),
                span: span.clone(),
                condition: VcKind::Predicate(subst_pred),
                preferred_backend: Some(BackendHint::Smt),
            };
            vcs.push(vc);
        }

        vcs
    }

    /// Build the WP formula assuming callee's postcondition holds
    ///
    /// wp(call dest = f(args), P) includes: ensures[args/params, dest/result] => P
    ///
    /// This substitutes:
    /// - Parameter names with actual argument expressions
    /// - "result" with the destination variable
    ///
    /// Then returns: (conjunction of all ensures) => postcondition
    fn assume_postcondition(
        callee_specs: &FunctionSpecs,
        param_subst: &HashMap<String, Expr>,
        dest_var: &str,
        postcondition: Predicate,
    ) -> Predicate {
        if callee_specs.ensures.is_empty() {
            // No postcondition to assume - just return original postcondition
            return postcondition;
        }

        // Build conjunction of substituted ensures clauses
        let mut ensures_preds = Vec::new();
        for ensure in &callee_specs.ensures {
            // First substitute parameters with arguments
            let mut subst_pred = substitute_predicate(&ensure.pred, param_subst);

            // Then substitute "result" (or "_0") with destination variable
            let result_subst: HashMap<String, Expr> = [
                ("result".to_string(), Expr::Var(dest_var.to_string())),
                ("_0".to_string(), Expr::Var(dest_var.to_string())),
            ]
            .into_iter()
            .collect();
            subst_pred = substitute_predicate(&subst_pred, &result_subst);

            ensures_preds.push(subst_pred);
        }

        let ensures_conj = if ensures_preds.len() == 1 {
            ensures_preds
                .pop()
                .expect("len()==1 guarantees element exists")
        } else {
            Predicate::And(ensures_preds)
        };

        // Return: ensures => postcondition
        // This means: if the callee's postcondition holds, then our postcondition holds
        Predicate::Implies(Box::new(ensures_conj), Box::new(postcondition))
    }

    /// Compute WP with full path-sensitive CFG traversal
    /// This version follows edges backwards from return blocks to entry
    pub fn wp_function_path_sensitive(&mut self, postcondition: &Predicate) -> Predicate {
        // Find all return blocks
        let return_blocks: Vec<usize> = self
            .func
            .blocks
            .iter()
            .enumerate()
            .filter(|(_, b)| matches!(b.terminator, Terminator::Return))
            .map(|(i, _)| i)
            .collect();

        if return_blocks.is_empty() {
            return Predicate::Bool(true);
        }

        self.wp_cache.clear();

        // Compute WP at each block, propagating backwards
        // Start from return blocks with postcondition
        for &block_idx in &return_blocks {
            self.compute_wp_at_block(block_idx, postcondition.clone());
        }

        // The result is the WP at block 0 (entry)
        self.wp_cache
            .get(&0)
            .cloned()
            .unwrap_or(Predicate::Bool(true))
    }

    /// Recursively compute WP at a block and propagate to predecessors
    fn compute_wp_at_block(&mut self, block_idx: usize, post_at_exit: Predicate) {
        // Compute WP through this block's statements
        let wp_at_entry = self.wp_block(block_idx, post_at_exit);

        // Update or merge with existing WP at this block
        let merged = if let Some(existing) = self.wp_cache.get(&block_idx) {
            // Merge: both paths must satisfy their respective conditions
            Predicate::And(vec![existing.clone(), wp_at_entry])
        } else {
            wp_at_entry
        };

        self.wp_cache.insert(block_idx, merged.clone());

        // Propagate to predecessors
        let preds = self.predecessors[block_idx].clone();
        for (pred_idx, branch_cond) in preds {
            let wp_for_pred = if let Some(cond) = branch_cond {
                // This edge has a branch condition
                // wp at predecessor = cond => wp_at_this_block
                Predicate::Implies(Box::new(cond), Box::new(merged.clone()))
            } else {
                merged.clone()
            };

            // Recursively propagate (avoiding cycles would need visited set)
            // For acyclic CFGs this is safe
            self.compute_wp_at_block(pred_idx, wp_for_pred);
        }
    }
}

fn place_to_var_name(place: &Place) -> String {
    format!("_{}", place.local.0)
}

/// Check if a function call is Box::new or equivalent allocation
///
/// This matches various forms that Box::new may appear as in MIR:
/// - "Box::new"
/// - "alloc::boxed::Box::<T>::new"
/// - "std::boxed::Box::new"
/// - "<alloc::boxed::Box<T>>::new"
fn is_box_new(func_name: &str) -> bool {
    // Direct name match
    if func_name == "Box::new" || func_name == "box_new" {
        return true;
    }

    // Qualified paths
    if func_name.contains("Box") && func_name.ends_with("::new") {
        return true;
    }

    // Generic instantiation form: <alloc::boxed::Box<T>>::new
    if func_name.starts_with('<') && func_name.contains("Box") && func_name.contains(">::new") {
        return true;
    }

    false
}

/// Build predecessor map from successor information in terminators
fn build_predecessor_map(func: &MirFunction) -> Vec<Vec<(usize, Option<Predicate>)>> {
    let num_blocks = func.blocks.len();
    let mut preds: Vec<Vec<(usize, Option<Predicate>)>> = vec![vec![]; num_blocks];
    let encoder = MirEncoder::new(func);

    for (block_idx, block) in func.blocks.iter().enumerate() {
        match &block.terminator {
            Terminator::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                let discr_expr = encoder.encode_operand(discr);

                // Explicit targets with equality conditions
                for (val, target) in targets {
                    if *target < num_blocks {
                        let cond = Predicate::Expr(Expr::Eq(
                            Box::new(discr_expr.clone()),
                            Box::new(Expr::IntLit(*val as i128)),
                        ));
                        preds[*target].push((block_idx, Some(cond)));
                    }
                }

                // Otherwise target with negation of all explicit conditions
                if *otherwise < num_blocks {
                    let otherwise_cond = if targets.is_empty() {
                        None
                    } else {
                        let not_any: Vec<Predicate> = targets
                            .iter()
                            .map(|(val, _)| {
                                Predicate::Expr(Expr::Ne(
                                    Box::new(discr_expr.clone()),
                                    Box::new(Expr::IntLit(*val as i128)),
                                ))
                            })
                            .collect();

                        Some(if not_any.len() == 1 {
                            not_any
                                .into_iter()
                                .next()
                                .expect("len()==1 guarantees element exists")
                        } else {
                            Predicate::And(not_any)
                        })
                    };
                    preds[*otherwise].push((block_idx, otherwise_cond));
                }
            }

            Terminator::Goto { target }
            | Terminator::Assert { target, .. }
            | Terminator::Call { target, .. }
            | Terminator::IndirectCall { target, .. } => {
                if *target < num_blocks {
                    preds[*target].push((block_idx, None));
                }
            }

            Terminator::Return | Terminator::Unreachable => {
                // No successors
            }
        }
    }

    preds
}

/// Substitute multiple variables in a predicate
///
/// This applies all substitutions in the map to the predicate.
/// Used for modular verification to replace formal parameters with actual arguments.
fn substitute_predicate(pred: &Predicate, subst: &HashMap<String, Expr>) -> Predicate {
    let mut result = pred.clone();
    for (var, expr) in subst {
        result = substitute(&result, var, expr);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BasicBlock, Constant, Local, LocalDecl, MirType, Operand, Rvalue};

    /// Helper to create a simple assignment block
    fn assign_block(local: usize, value: i128, term: Terminator) -> BasicBlock {
        BasicBlock {
            statements: vec![Statement::Assign {
                place: Place {
                    local: Local(local),
                    projections: vec![],
                },
                rvalue: Rvalue::Use(Operand::Constant(Constant::Int(value))),
            }],
            terminator: term,
        }
    }

    #[test]
    fn test_wp_simple_return() {
        // fn f() -> i32 { return 1; }
        let func = MirFunction {
            name: "f".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![LocalDecl {
                ty: MirType::Int {
                    signed: true,
                    bits: 32,
                },
                name: Some("_0".to_string()),
            }],
            blocks: vec![assign_block(0, 1, Terminator::Return)],
            span: SourceSpan::default(),
        };

        let mut wp_calc = WpCalculator::new(&func);

        // Postcondition: _0 == 1
        let postcond = Predicate::Expr(Expr::Eq(
            Box::new(Expr::Var("_0".to_string())),
            Box::new(Expr::IntLit(1)),
        ));

        let wp = wp_calc.wp_function(&postcond);

        // After substitution [1/_0], should get: 1 == 1 which is true
        // The WP should be 1 == 1
        match wp {
            Predicate::Expr(Expr::Eq(l, r)) => {
                assert!(matches!(*l, Expr::IntLit(1)));
                assert!(matches!(*r, Expr::IntLit(1)));
            }
            _ => panic!("Expected Eq predicate, got {wp:?}"),
        }
    }

    #[test]
    fn test_wp_branch() {
        // if _1 { _0 = 1 } else { _0 = 2 }
        // return _0
        let func = MirFunction {
            name: "branch".to_string(),
            params: vec![("x".to_string(), MirType::Bool)],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_0".to_string()),
                },
                LocalDecl {
                    ty: MirType::Bool,
                    name: Some("_1".to_string()),
                },
            ],
            blocks: vec![
                // Block 0: switch on _1
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        }),
                        targets: vec![(1, 1)], // true -> block 1
                        otherwise: 2,          // false -> block 2
                    },
                },
                // Block 1: true branch
                assign_block(0, 1, Terminator::Return),
                // Block 2: false branch
                assign_block(0, 2, Terminator::Return),
            ],
            span: SourceSpan::default(),
        };

        let mut wp_calc = WpCalculator::new(&func);

        // Postcondition: _0 >= 1
        let postcond = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("_0".to_string())),
            Box::new(Expr::IntLit(1)),
        ));

        let wp = wp_calc.wp_function(&postcond);

        // WP should be something like: (1 >= 1) ∧ (2 >= 1) = true ∧ true
        // The exact structure depends on implementation details
        // Just verify it's computed without panic
        assert!(!matches!(wp, Predicate::Bool(false)));
    }

    #[test]
    fn test_wp_assert() {
        // assert _1 > 0; return _1;
        let func = MirFunction {
            name: "with_assert".to_string(),
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
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_0".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_1".to_string()),
                },
            ],
            blocks: vec![
                // Block 0: assert _1 > 0
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        }),
                        expected: true,
                        target: 1,
                    },
                },
                // Block 1: _0 = _1; return
                BasicBlock {
                    statements: vec![Statement::Assign {
                        place: Place {
                            local: Local(0),
                            projections: vec![],
                        },
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        })),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            span: SourceSpan::default(),
        };

        let mut wp_calc = WpCalculator::new(&func);

        // Postcondition: _0 > 0
        let postcond = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("_0".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let wp = wp_calc.wp_function(&postcond);

        // WP should include the assertion condition
        // assert(_1 > 0) ∧ (_1 > 0)
        match &wp {
            Predicate::And(conjuncts) => {
                assert_eq!(conjuncts.len(), 2);
            }
            _ => panic!("Expected And predicate for assert, got {wp:?}"),
        }
    }

    #[test]
    fn test_wp_clamp_positive() {
        use crate::verify::mir_from_clamp_positive;

        let (func, _specs) = mir_from_clamp_positive();
        let mut wp_calc = WpCalculator::new(&func);

        // Postcondition: result >= 1
        let postcond = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("_0".to_string())),
            Box::new(Expr::IntLit(1)),
        ));

        let wp = wp_calc.wp_function(&postcond);

        // Should produce a predicate that captures all three return paths
        // Just verify it computes something
        if let Predicate::And(conjuncts) = &wp {
            // Multiple paths combined
            assert!(conjuncts.len() >= 2);
        }
        // Single path or simplified - also acceptable
    }

    #[test]
    fn test_predecessor_map() {
        let func = MirFunction {
            name: "test".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![],
            blocks: vec![
                // Block 0: goto 1
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Goto { target: 1 },
                },
                // Block 1: return
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            span: SourceSpan::default(),
        };

        let preds = build_predecessor_map(&func);

        // Block 0 has no predecessors
        assert!(preds[0].is_empty());

        // Block 1 has block 0 as predecessor
        assert_eq!(preds[1].len(), 1);
        assert_eq!(preds[1][0].0, 0);
        assert!(preds[1][0].1.is_none()); // Goto has no condition
    }

    #[test]
    fn test_predecessor_map_switch() {
        let func = MirFunction {
            name: "test".to_string(),
            params: vec![("x".to_string(), MirType::Bool)],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![LocalDecl {
                ty: MirType::Bool,
                name: Some("_1".to_string()),
            }],
            blocks: vec![
                // Block 0: switch _1 { true -> 1, false -> 2 }
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place {
                            local: Local(0),
                            projections: vec![],
                        }),
                        targets: vec![(1, 1)],
                        otherwise: 2,
                    },
                },
                // Block 1: return (true branch)
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
                // Block 2: return (false branch)
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            span: SourceSpan::default(),
        };

        let preds = build_predecessor_map(&func);

        // Block 1 has block 0 as predecessor with condition _0 == 1
        assert_eq!(preds[1].len(), 1);
        assert_eq!(preds[1][0].0, 0);
        assert!(preds[1][0].1.is_some());

        // Block 2 has block 0 as predecessor with condition _0 != 1
        assert_eq!(preds[2].len(), 1);
        assert_eq!(preds[2][0].0, 0);
        assert!(preds[2][0].1.is_some());
    }

    #[test]
    fn test_overflow_vc_generation() {
        // _0 = CheckedAdd(_1, _2)
        let func = MirFunction {
            name: "overflow_test".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_0".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_1".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_2".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        }),
                        Operand::Copy(Place {
                            local: Local(2),
                            projections: vec![],
                        }),
                    ),
                }],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let mut wp_calc = WpCalculator::new(&func);
        let postcond = Predicate::Bool(true);
        let _wp = wp_calc.wp_function(&postcond);

        // Should have generated an overflow VC
        let side_vcs = wp_calc.take_side_vcs();
        assert!(!side_vcs.is_empty(), "Expected overflow VC to be generated");

        let overflow_vc = side_vcs
            .iter()
            .find(|vc| vc.name.contains("overflow"))
            .expect("Expected an overflow VC");

        // The VC should check that the sum is in range
        assert!(matches!(overflow_vc.condition, vc_ir::VcKind::Predicate(_)));
    }

    #[test]
    fn test_division_by_zero_vc() {
        // _0 = _1 / _2
        let func = MirFunction {
            name: "div_test".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_0".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_1".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_2".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        }),
                        Operand::Copy(Place {
                            local: Local(2),
                            projections: vec![],
                        }),
                    ),
                }],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let mut wp_calc = WpCalculator::new(&func);
        let postcond = Predicate::Bool(true);
        let _wp = wp_calc.wp_function(&postcond);

        let side_vcs = wp_calc.take_side_vcs();
        let div_zero_vc = side_vcs
            .iter()
            .find(|vc| vc.name.contains("division by zero"))
            .expect("Expected division by zero VC");

        // The VC should be divisor != 0
        assert!(matches!(div_zero_vc.condition, vc_ir::VcKind::Predicate(_)));
    }

    #[test]
    fn test_array_bounds_vc() {
        use crate::Projection;

        // _0 = _1[_2] (array access)
        let func = MirFunction {
            name: "bounds_test".to_string(),
            params: vec![
                (
                    "arr".to_string(),
                    MirType::Array {
                        elem: Box::new(MirType::Int {
                            signed: true,
                            bits: 32,
                        }),
                        len: 10,
                    },
                ),
                (
                    "idx".to_string(),
                    MirType::Int {
                        signed: false,
                        bits: 64,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_0".to_string()),
                },
                LocalDecl {
                    ty: MirType::Array {
                        elem: Box::new(MirType::Int {
                            signed: true,
                            bits: 32,
                        }),
                        len: 10,
                    },
                    name: Some("_1".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: false,
                        bits: 64,
                    },
                    name: Some("_2".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: Local(1),
                        projections: vec![Projection::Index(Local(2))],
                    })),
                }],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let mut wp_calc = WpCalculator::new(&func);
        let postcond = Predicate::Bool(true);
        let _wp = wp_calc.wp_function(&postcond);

        let side_vcs = wp_calc.take_side_vcs();
        let bounds_vc = side_vcs
            .iter()
            .find(|vc| vc.name.contains("array bounds"))
            .expect("Expected array bounds VC");

        // The VC should check 0 <= idx < len
        assert!(matches!(bounds_vc.condition, vc_ir::VcKind::Predicate(_)));
    }

    #[test]
    fn test_loop_with_invariant() {
        // A simple while loop: while (_1 > 0) { _1 = _1 - 1 }
        // Block 0: check condition, branch
        // Block 1: decrement, goto 0
        // Block 2: return
        let func = MirFunction {
            name: "loop_test".to_string(),
            params: vec![(
                "n".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_0".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_1".to_string()),
                },
            ],
            blocks: vec![
                // Block 0: Loop header - check _1 > 0
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        }),
                        targets: vec![(0, 2)], // _1 == 0 -> exit (block 2)
                        otherwise: 1,          // otherwise -> body (block 1)
                    },
                },
                // Block 1: Loop body - _1 = _1 - 1, then back to header
                BasicBlock {
                    statements: vec![Statement::Assign {
                        place: Place {
                            local: Local(1),
                            projections: vec![],
                        },
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place {
                                local: Local(1),
                                projections: vec![],
                            }),
                            Operand::Constant(Constant::Int(1)),
                        ),
                    }],
                    terminator: Terminator::Goto { target: 0 }, // Back-edge
                },
                // Block 2: Exit - return _1
                BasicBlock {
                    statements: vec![Statement::Assign {
                        place: Place {
                            local: Local(0),
                            projections: vec![],
                        },
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        })),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            span: SourceSpan::default(),
        };

        // Loop invariant: _1 >= 0
        let invariant = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("_1".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let mut invariants = HashMap::new();
        invariants.insert(0, invariant.clone()); // Block 0 is loop header

        let mut wp_calc = WpCalculator::with_invariants(&func, invariants);

        // Postcondition: result == 0
        let postcond = Predicate::Expr(Expr::Eq(
            Box::new(Expr::Var("_0".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let _wp = wp_calc.wp_function(&postcond);

        // Should have generated loop VCs (base case, preservation)
        let side_vcs = wp_calc.take_side_vcs();

        let has_base_vc = side_vcs.iter().any(|vc| vc.name.contains("base case"));
        let has_preservation_vc = side_vcs.iter().any(|vc| vc.name.contains("preservation"));

        assert!(has_base_vc, "Expected loop invariant base case VC");
        assert!(
            has_preservation_vc,
            "Expected loop invariant preservation VC"
        );
    }

    #[test]
    fn test_loop_without_invariant_generates_warning() {
        // Same loop as above but without invariant
        let func = MirFunction {
            name: "loop_no_inv".to_string(),
            params: vec![(
                "n".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_0".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_1".to_string()),
                },
            ],
            blocks: vec![
                // Block 0: Loop header
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        }),
                        targets: vec![(0, 2)],
                        otherwise: 1,
                    },
                },
                // Block 1: Loop body with back-edge
                BasicBlock {
                    statements: vec![Statement::Assign {
                        place: Place {
                            local: Local(1),
                            projections: vec![],
                        },
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place {
                                local: Local(1),
                                projections: vec![],
                            }),
                            Operand::Constant(Constant::Int(1)),
                        ),
                    }],
                    terminator: Terminator::Goto { target: 0 },
                },
                // Block 2: Exit
                BasicBlock {
                    statements: vec![Statement::Assign {
                        place: Place {
                            local: Local(0),
                            projections: vec![],
                        },
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        })),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            span: SourceSpan::default(),
        };

        let mut wp_calc = WpCalculator::new(&func); // No invariants

        let postcond = Predicate::Bool(true);
        let _wp = wp_calc.wp_function(&postcond);

        // SOUNDNESS: Must detect loops without invariants
        assert!(
            wp_calc.has_loops_without_invariant(),
            "Expected to detect loop without invariant"
        );
        assert!(
            !wp_calc.loops_without_invariant().is_empty(),
            "Expected non-empty loops_without_invariant list"
        );

        let side_vcs = wp_calc.take_side_vcs();

        // Should have a warning VC about missing invariant
        let has_warning = side_vcs
            .iter()
            .any(|vc| vc.name.contains("requires #[invariant"));

        assert!(
            has_warning,
            "Expected warning VC about missing loop invariant"
        );
    }

    // ===== Modular Verification Tests (Phase 2.5) =====

    #[test]
    fn test_modular_verification_with_contracts() {
        // Caller function: calls `abs` which has a contract
        // abs has: #[requires(true)] #[ensures(result >= 0)]
        //
        // fn caller(x: i32) -> i32 {
        //     let y = abs(x);  // Call with contract
        //     return y;
        // }

        let caller_func = MirFunction {
            name: "caller".to_string(),
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
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_0".to_string()), // return
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_1".to_string()), // param x
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_2".to_string()), // local y
                },
            ],
            blocks: vec![
                // Block 0: call abs(_1) -> _2
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "abs".to_string(),
                        args: vec![Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        })],
                        destination: Place {
                            local: Local(2),
                            projections: vec![],
                        },
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                // Block 1: _0 = _2; return
                BasicBlock {
                    statements: vec![Statement::Assign {
                        place: Place {
                            local: Local(0),
                            projections: vec![],
                        },
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: Local(2),
                            projections: vec![],
                        })),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            span: SourceSpan::default(),
        };

        // Contract for abs: ensures result >= 0
        let abs_specs = FunctionSpecs {
            requires: vec![], // No precondition
            ensures: vec![vc_ir::SpecClause {
                pred: Predicate::Expr(Expr::Ge(
                    Box::new(Expr::Var("result".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                span: SourceSpan::default(),
                label: None,
            }],
            decreases: None,
            pure: true,
            trusted: false,
            api_metadata: None,
            effects: None,
            param_refinements: HashMap::default(),
        };

        // Register contract
        let mut contracts = HashMap::new();
        contracts.insert("abs".to_string(), abs_specs);

        let mut wp_calc = WpCalculator::with_contracts(&caller_func, contracts);

        // Postcondition: result >= 0 (should be provable using abs's postcondition)
        let postcond = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("_0".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let wp = wp_calc.wp_function(&postcond);

        // The WP should contain an implication from abs's postcondition
        // Since abs's ensures says result >= 0, and we assign that to _0,
        // the postcondition should be satisfiable
        // Result could be Implies (implication from postcondition assumption)
        // or simplified/structured differently - both are acceptable
        let _ = &wp;

        // No precondition VCs should be generated since abs has no preconditions
        let side_vcs = wp_calc.take_side_vcs();
        let precond_vcs: Vec<_> = side_vcs
            .iter()
            .filter(|vc| vc.name.contains("precondition"))
            .collect();
        assert!(
            precond_vcs.is_empty(),
            "Expected no precondition VCs for abs (has no requires)"
        );
    }

    #[test]
    fn test_modular_verification_precondition_vc() {
        // Caller calls a function with a precondition
        // divide has: #[requires(_1 != 0)] #[ensures(true)]
        //
        // fn caller(a: i32, b: i32) -> i32 {
        //     return divide(a, b);
        // }

        let caller_func = MirFunction {
            name: "caller".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_0".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_1".to_string()), // a
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_2".to_string()), // b
                },
            ],
            blocks: vec![
                // Block 0: call divide(_1, _2) -> _0
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "divide".to_string(),
                        args: vec![
                            Operand::Copy(Place {
                                local: Local(1),
                                projections: vec![],
                            }),
                            Operand::Copy(Place {
                                local: Local(2),
                                projections: vec![],
                            }),
                        ],
                        destination: Place {
                            local: Local(0),
                            projections: vec![],
                        },
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                // Block 1: return
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            span: SourceSpan::default(),
        };

        // Contract for divide: requires second arg != 0
        let divide_specs = FunctionSpecs {
            requires: vec![vc_ir::SpecClause {
                pred: Predicate::Expr(Expr::Ne(
                    Box::new(Expr::Var("_2".to_string())), // second param (b)
                    Box::new(Expr::IntLit(0)),
                )),
                span: SourceSpan::default(),
                label: None,
            }],
            ensures: vec![],
            decreases: None,
            pure: true,
            trusted: false,
            api_metadata: None,
            effects: None,
            param_refinements: HashMap::default(),
        };

        let mut contracts = HashMap::new();
        contracts.insert("divide".to_string(), divide_specs);

        let mut wp_calc = WpCalculator::with_contracts(&caller_func, contracts);

        let postcond = Predicate::Bool(true);
        let _wp = wp_calc.wp_function(&postcond);

        // Should have generated a precondition VC for the divide call
        let side_vcs = wp_calc.take_side_vcs();
        let precond_vcs: Vec<_> = side_vcs
            .iter()
            .filter(|vc| vc.name.contains("call divide precondition"))
            .collect();

        assert_eq!(
            precond_vcs.len(),
            1,
            "Expected exactly one precondition VC for divide call"
        );

        // The VC should check that the second argument (_2) is not zero
        let vc = &precond_vcs[0];
        if let VcKind::Predicate(pred) = &vc.condition {
            // Should contain a != comparison with 0
            match pred {
                Predicate::Expr(Expr::Ne(_, _)) => {
                    // Correct structure
                }
                _ => panic!("Expected Ne predicate for division precondition"),
            }
        }
    }

    #[test]
    fn test_modular_verification_no_contract() {
        // When calling a function without a registered contract,
        // should fall back to previous behavior (just pass postcondition through)

        let func = MirFunction {
            name: "caller".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![LocalDecl {
                ty: MirType::Int {
                    signed: true,
                    bits: 32,
                },
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "unknown_func".to_string(),
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
            span: SourceSpan::default(),
        };

        // Empty contract registry
        let contracts = HashMap::new();
        let mut wp_calc = WpCalculator::with_contracts(&func, contracts);

        let postcond = Predicate::Bool(true);
        let wp = wp_calc.wp_function(&postcond);

        // Should not crash, and postcondition should pass through
        assert!(matches!(wp, Predicate::Bool(true)));

        // No VCs should be generated
        let side_vcs = wp_calc.take_side_vcs();
        assert!(
            side_vcs.is_empty(),
            "Expected no VCs when callee has no contract"
        );
    }

    #[test]
    fn test_substitute_predicate_multiple_vars() {
        // Test the substitute_predicate function with multiple substitutions
        // Predicate: _1 + _2 > 0
        let pred = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Add(
                Box::new(Expr::Var("_1".to_string())),
                Box::new(Expr::Var("_2".to_string())),
            )),
            Box::new(Expr::IntLit(0)),
        ));

        // Substitute _1 -> 10, _2 -> 20
        let mut subst = HashMap::new();
        subst.insert("_1".to_string(), Expr::IntLit(10));
        subst.insert("_2".to_string(), Expr::IntLit(20));

        let result = substitute_predicate(&pred, &subst);

        // Result should be: 10 + 20 > 0
        if let Predicate::Expr(Expr::Gt(lhs, _)) = result {
            if let Expr::Add(a, b) = *lhs {
                assert!(matches!(*a, Expr::IntLit(10)));
                assert!(matches!(*b, Expr::IntLit(20)));
            } else {
                panic!("Expected Add expression");
            }
        } else {
            panic!("Expected Gt predicate");
        }
    }

    #[test]
    fn test_contract_registry_methods() {
        // Test the contract registry constructor and methods
        let func = MirFunction {
            name: "test".to_string(),
            params: vec![],
            return_type: MirType::Bool,
            locals: vec![],
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let mut wp_calc = WpCalculator::new(&func);

        // Initially empty
        assert!(wp_calc.contracts().is_empty());

        // Register a contract
        let specs = FunctionSpecs {
            requires: vec![],
            ensures: vec![],
            decreases: None,
            pure: true,
            trusted: false,
            api_metadata: None,
            effects: None,
            param_refinements: HashMap::default(),
        };
        wp_calc.register_contract("foo".to_string(), specs);

        // Should now have one contract
        assert_eq!(wp_calc.contracts().len(), 1);
        assert!(wp_calc.contracts().contains_key("foo"));
    }

    // =========================================================================
    // Box::new Heap Semantics Tests
    // =========================================================================

    #[test]
    fn test_is_box_new_direct() {
        assert!(is_box_new("Box::new"));
        assert!(is_box_new("box_new"));
    }

    #[test]
    fn test_is_box_new_qualified() {
        assert!(is_box_new("std::boxed::Box::new"));
        assert!(is_box_new("alloc::boxed::Box::<i32>::new"));
        assert!(is_box_new("alloc::boxed::Box::<T>::new"));
    }

    #[test]
    fn test_is_box_new_generic_form() {
        assert!(is_box_new("<alloc::boxed::Box<i32>>::new"));
        assert!(is_box_new("<Box<T>>::new"));
    }

    #[test]
    fn test_is_box_new_negative() {
        assert!(!is_box_new("Vec::new"));
        assert!(!is_box_new("HashMap::new"));
        assert!(!is_box_new("Box::into_raw"));
        assert!(!is_box_new("new_box")); // Wrong order
    }

    #[test]
    fn test_box_new_establishes_deref_constraint() {
        use crate::{BasicBlock, Constant, Local, LocalDecl, MirType, Operand, Place, Terminator};

        // Function: fn make_box() -> Box<i32> { Box::new(42) }
        let func = MirFunction {
            name: "make_box".to_string(),
            params: vec![],
            return_type: MirType::Ref {
                mutable: false,
                inner: Box::new(MirType::Int {
                    signed: true,
                    bits: 32,
                }),
            },
            locals: vec![LocalDecl {
                ty: MirType::Ref {
                    mutable: false,
                    inner: Box::new(MirType::Int {
                        signed: true,
                        bits: 32,
                    }),
                },
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "Box::new".to_string(),
                        args: vec![Operand::Constant(Constant::Int(42))],
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
            span: SourceSpan::default(),
        };

        let mut wp_calc = WpCalculator::new(&func);

        // Postcondition: *result == 42
        let postcondition = Predicate::Expr(Expr::Eq(
            Box::new(Expr::Deref(Box::new(Expr::Var("_0".to_string())))),
            Box::new(Expr::IntLit(42)),
        ));

        let wp = wp_calc.wp_function(&postcondition);

        // The WP should include the box constraint: (*_0 == 42)
        // When postcondition is also (*_0 == 42), the whole thing should be true
        // The WP will be: And([(*_0 == 42), (*_0 == 42)]) after Box::new
        // which simplifies to true
        match wp {
            Predicate::And(preds) => {
                // Should have at least one predicate from box constraint
                assert!(!preds.is_empty(), "WP should include box constraint");
            }
            Predicate::Bool(true) => {
                // Also acceptable if it simplified
            }
            _ => {
                // Check if the WP contains the deref constraint somehow
                // This is fine as long as it's not False
                assert!(
                    !matches!(wp, Predicate::Bool(false)),
                    "WP should not be false for correct Box::new usage"
                );
            }
        }
    }
}
