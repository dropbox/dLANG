//! Symbolic Execution for VC Generation
//!
//! An alternative to WP calculus: forward symbolic execution that collects
//! path conditions and generates VCs at assertions and function exits.

use crate::{encoder::MirEncoder, MirFunction, Statement, Terminator};
use std::collections::HashMap;
use vc_ir::{BackendHint, Expr, Predicate, SourceSpan, VcId, VcKind, VerificationCondition};

/// Symbolic state during execution
#[derive(Clone)]
pub struct SymbolicState {
    /// Map from variable names to their symbolic values
    pub variables: HashMap<String, Expr>,
    /// Path condition (conjunction of branch conditions to reach here)
    pub path_condition: Vec<Predicate>,
    /// Current block index
    pub block: usize,
    /// Statement index within block
    pub stmt: usize,
}

impl Default for SymbolicState {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolicState {
    #[must_use]
    pub fn new() -> Self {
        Self {
            variables: HashMap::new(),
            path_condition: vec![],
            block: 0,
            stmt: 0,
        }
    }

    #[must_use]
    pub fn with_path_condition(&self, cond: Predicate) -> Self {
        let mut new_state = self.clone();
        new_state.path_condition.push(cond);
        new_state
    }
}

/// Symbolic executor
pub struct SymbolicExecutor<'a> {
    func: &'a MirFunction,
    encoder: MirEncoder,
    vcs: Vec<VerificationCondition>,
    next_vc_id: u64,
}

impl<'a> SymbolicExecutor<'a> {
    #[must_use]
    pub fn new(func: &'a MirFunction) -> Self {
        Self {
            func,
            encoder: MirEncoder::new(func),
            vcs: vec![],
            next_vc_id: 0,
        }
    }

    const fn fresh_vc_id(&mut self) -> VcId {
        let id = VcId(self.next_vc_id);
        self.next_vc_id += 1;
        id
    }

    /// Execute symbolically and collect VCs
    #[must_use]
    pub fn execute(mut self, postcondition: &Predicate) -> Vec<VerificationCondition> {
        let initial_state = SymbolicState::new();
        self.execute_from_state(initial_state, postcondition);
        self.vcs
    }

    fn execute_from_state(&mut self, state: SymbolicState, postcondition: &Predicate) {
        if state.block >= self.func.blocks.len() {
            return;
        }

        let block = &self.func.blocks[state.block];

        // Execute statements
        let mut current_state = state;
        for (idx, stmt) in block.statements.iter().enumerate() {
            if idx < current_state.stmt {
                continue;
            }
            current_state = self.execute_statement(&current_state, stmt);
        }

        // Execute terminator
        self.execute_terminator(current_state, &block.terminator, postcondition);
    }

    fn execute_statement(&self, state: &SymbolicState, stmt: &Statement) -> SymbolicState {
        match stmt {
            Statement::Assign { place, rvalue } => {
                let var_name = format!("_{}", place.local.0);
                let value = self.encoder.encode_rvalue(rvalue);
                let mut new_state = state.clone();
                new_state.variables.insert(var_name, value);
                new_state
            }
            Statement::StorageLive(_) | Statement::StorageDead(_) => state.clone(),
        }
    }

    fn execute_terminator(
        &mut self,
        state: SymbolicState,
        term: &Terminator,
        postcondition: &Predicate,
    ) {
        match term {
            Terminator::Return => {
                // Generate VC: path_condition => postcondition
                let path_cond = if state.path_condition.is_empty() {
                    Predicate::Bool(true)
                } else {
                    Predicate::And(state.path_condition)
                };

                let vc = VerificationCondition {
                    id: self.fresh_vc_id(),
                    name: "postcondition at return".to_string(),
                    span: SourceSpan::default(),
                    condition: VcKind::Implies {
                        antecedent: path_cond,
                        consequent: postcondition.clone(),
                    },
                    preferred_backend: Some(BackendHint::Smt),
                };
                self.vcs.push(vc);
            }

            Terminator::Goto { target }
            | Terminator::Call { target, .. }
            | Terminator::IndirectCall { target, .. } => {
                let mut new_state = state;
                new_state.block = *target;
                new_state.stmt = 0;
                self.execute_from_state(new_state, postcondition);
            }

            Terminator::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                let cond_expr = self.encoder.encode_operand(discr);

                // Fork execution for each target
                for (val, target) in targets {
                    let branch_cond = Predicate::Expr(Expr::Eq(
                        Box::new(cond_expr.clone()),
                        Box::new(Expr::IntLit(*val as i128)),
                    ));
                    let mut branch_state = state.with_path_condition(branch_cond);
                    branch_state.block = *target;
                    branch_state.stmt = 0;
                    self.execute_from_state(branch_state, postcondition);
                }

                // Otherwise branch
                let otherwise_cond = Predicate::And(
                    targets
                        .iter()
                        .map(|(val, _)| {
                            Predicate::Expr(Expr::Ne(
                                Box::new(cond_expr.clone()),
                                Box::new(Expr::IntLit(*val as i128)),
                            ))
                        })
                        .collect(),
                );
                let mut otherwise_state = state.with_path_condition(otherwise_cond);
                otherwise_state.block = *otherwise;
                otherwise_state.stmt = 0;
                self.execute_from_state(otherwise_state, postcondition);
            }

            Terminator::Assert {
                cond,
                expected,
                target,
            } => {
                let cond_expr = self.encoder.encode_operand(cond);
                let assert_pred = if *expected {
                    Predicate::Expr(cond_expr)
                } else {
                    Predicate::Expr(Expr::Not(Box::new(cond_expr)))
                };

                // Generate VC for assertion
                let path_cond = if state.path_condition.is_empty() {
                    Predicate::Bool(true)
                } else {
                    Predicate::And(state.path_condition.clone())
                };

                let vc = VerificationCondition {
                    id: self.fresh_vc_id(),
                    name: "assertion".to_string(),
                    span: SourceSpan::default(),
                    condition: VcKind::Implies {
                        antecedent: path_cond,
                        consequent: assert_pred.clone(),
                    },
                    preferred_backend: Some(BackendHint::Smt),
                };
                self.vcs.push(vc);

                // Continue with assertion as path condition
                let mut new_state = state.with_path_condition(assert_pred);
                new_state.block = *target;
                new_state.stmt = 0;
                self.execute_from_state(new_state, postcondition);
            }

            Terminator::Unreachable => {
                // Generate VC that path condition is false (unreachable)
                let path_cond = if state.path_condition.is_empty() {
                    Predicate::Bool(true)
                } else {
                    Predicate::And(state.path_condition)
                };

                let vc = VerificationCondition {
                    id: self.fresh_vc_id(),
                    name: "unreachable".to_string(),
                    span: SourceSpan::default(),
                    condition: VcKind::Implies {
                        antecedent: path_cond,
                        consequent: Predicate::Bool(false),
                    },
                    preferred_backend: Some(BackendHint::Smt),
                };
                self.vcs.push(vc);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BasicBlock, BinOp, Constant, Local, LocalDecl, MirType, Operand, Place, Rvalue};

    // ===== Test helpers =====

    fn make_test_func(blocks: Vec<BasicBlock>) -> MirFunction {
        MirFunction {
            name: "test_func".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            blocks,
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: None,
            }],
            span: SourceSpan::default(),
        }
    }

    fn make_block(terminator: Terminator) -> BasicBlock {
        BasicBlock {
            statements: vec![],
            terminator,
        }
    }

    fn make_block_with_stmts(stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock {
            statements: stmts,
            terminator,
        }
    }

    fn simple_place(local: usize) -> Place {
        Place {
            local: Local(local),
            projections: vec![],
        }
    }

    // ===== SymbolicState tests =====

    #[test]
    fn test_symbolic_state_new() {
        let state = SymbolicState::new();
        assert!(state.variables.is_empty());
        assert!(state.path_condition.is_empty());
        assert_eq!(state.block, 0);
        assert_eq!(state.stmt, 0);
    }

    #[test]
    fn test_symbolic_state_default() {
        let state = SymbolicState::default();
        assert!(state.variables.is_empty());
        assert!(state.path_condition.is_empty());
        assert_eq!(state.block, 0);
        assert_eq!(state.stmt, 0);
    }

    #[test]
    fn test_symbolic_state_with_path_condition() {
        let state = SymbolicState::new();
        let cond = Predicate::Bool(true);
        let new_state = state.with_path_condition(cond.clone());

        // Original state unchanged
        assert!(state.path_condition.is_empty());
        // New state has the condition
        assert_eq!(new_state.path_condition.len(), 1);
        assert!(matches!(new_state.path_condition[0], Predicate::Bool(true)));
    }

    #[test]
    fn test_symbolic_state_multiple_conditions() {
        let state = SymbolicState::new();
        let state = state.with_path_condition(Predicate::Bool(true));
        let state = state.with_path_condition(Predicate::Bool(false));

        assert_eq!(state.path_condition.len(), 2);
    }

    #[test]
    fn test_symbolic_state_clone_preserves_variables() {
        let mut state = SymbolicState::new();
        state.variables.insert("x".to_string(), Expr::IntLit(42));
        let cloned = state.clone();

        assert!(cloned.variables.contains_key("x"));
        assert!(matches!(cloned.variables.get("x"), Some(Expr::IntLit(42))));
    }

    // ===== SymbolicExecutor tests =====

    #[test]
    fn test_executor_simple_return() {
        // Simple function that just returns
        let func = make_test_func(vec![make_block(Terminator::Return)]);

        let executor = SymbolicExecutor::new(&func);
        let postcond = Predicate::Bool(true);
        let vcs = executor.execute(&postcond);

        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].name, "postcondition at return");
        assert!(matches!(
            &vcs[0].condition,
            VcKind::Implies { consequent, .. } if matches!(consequent, Predicate::Bool(true))
        ));
    }

    #[test]
    fn test_executor_goto_chain() {
        // Block 0 -> Block 1 -> Return
        let func = make_test_func(vec![
            make_block(Terminator::Goto { target: 1 }),
            make_block(Terminator::Return),
        ]);

        let executor = SymbolicExecutor::new(&func);
        let postcond = Predicate::Bool(true);
        let vcs = executor.execute(&postcond);

        // Should generate one VC at the return
        assert_eq!(vcs.len(), 1);
    }

    #[test]
    fn test_executor_assert_generates_vc() {
        let func = make_test_func(vec![
            make_block(Terminator::Assert {
                cond: Operand::Constant(Constant::Bool(true)),
                expected: true,
                target: 1,
            }),
            make_block(Terminator::Return),
        ]);

        let executor = SymbolicExecutor::new(&func);
        let postcond = Predicate::Bool(true);
        let vcs = executor.execute(&postcond);

        // Should generate 2 VCs: assertion + postcondition
        assert_eq!(vcs.len(), 2);
        assert_eq!(vcs[0].name, "assertion");
        assert_eq!(vcs[1].name, "postcondition at return");
    }

    #[test]
    fn test_executor_unreachable() {
        let func = make_test_func(vec![make_block(Terminator::Unreachable)]);

        let executor = SymbolicExecutor::new(&func);
        let postcond = Predicate::Bool(true);
        let vcs = executor.execute(&postcond);

        assert_eq!(vcs.len(), 1);
        assert_eq!(vcs[0].name, "unreachable");
        // Unreachable should prove false
        assert!(matches!(
            &vcs[0].condition,
            VcKind::Implies { consequent, .. } if matches!(consequent, Predicate::Bool(false))
        ));
    }

    #[test]
    fn test_executor_switch_forks() {
        // SwitchInt with two targets plus otherwise
        let func = make_test_func(vec![
            make_block(Terminator::SwitchInt {
                discr: Operand::Constant(Constant::Int(0)),
                targets: vec![(0, 1), (1, 2)],
                otherwise: 3,
            }),
            make_block(Terminator::Return), // target 1
            make_block(Terminator::Return), // target 2
            make_block(Terminator::Return), // otherwise
        ]);

        let executor = SymbolicExecutor::new(&func);
        let postcond = Predicate::Bool(true);
        let vcs = executor.execute(&postcond);

        // Should generate 3 VCs (one per return path)
        assert_eq!(vcs.len(), 3);
    }

    #[test]
    fn test_executor_out_of_bounds_block() {
        // Execute with block >= blocks.len() does nothing
        let func = make_test_func(vec![make_block(Terminator::Return)]);
        let mut executor = SymbolicExecutor::new(&func);
        let mut state = SymbolicState::new();
        state.block = 100; // Way out of bounds

        executor.execute_from_state(state, &Predicate::Bool(true));
        // Should not panic, and should not generate VCs
        assert!(executor.vcs.is_empty());
    }

    #[test]
    fn test_executor_assign_statement() {
        // Test that assignment updates symbolic state
        let func = make_test_func(vec![make_block_with_stmts(
            vec![Statement::Assign {
                place: simple_place(1),
                rvalue: Rvalue::Use(Operand::Constant(Constant::Int(42))),
            }],
            Terminator::Return,
        )]);

        let executor = SymbolicExecutor::new(&func);
        let postcond = Predicate::Bool(true);
        let vcs = executor.execute(&postcond);

        // Should still generate the postcondition VC
        assert_eq!(vcs.len(), 1);
    }

    #[test]
    fn test_executor_storage_statements() {
        // StorageLive/StorageDead should not affect execution
        let func = make_test_func(vec![make_block_with_stmts(
            vec![
                Statement::StorageLive(Local(1)),
                Statement::StorageDead(Local(1)),
            ],
            Terminator::Return,
        )]);

        let executor = SymbolicExecutor::new(&func);
        let postcond = Predicate::Bool(true);
        let vcs = executor.execute(&postcond);

        assert_eq!(vcs.len(), 1);
    }

    #[test]
    fn test_executor_call_continues() {
        let func = make_test_func(vec![
            make_block(Terminator::Call {
                func: "other_func".to_string(),
                args: vec![],
                destination: simple_place(0),
                target: 1,
                span: SourceSpan::default(),
                generic_args: vec![],
            }),
            make_block(Terminator::Return),
        ]);

        let executor = SymbolicExecutor::new(&func);
        let postcond = Predicate::Bool(true);
        let vcs = executor.execute(&postcond);

        // Should generate postcondition VC at return
        assert_eq!(vcs.len(), 1);
    }

    #[test]
    fn test_executor_indirect_call_continues() {
        let func = make_test_func(vec![
            make_block(Terminator::IndirectCall {
                callee: simple_place(1),
                callee_ty: MirType::FnPtr {
                    params: vec![],
                    ret: Box::new(MirType::Tuple(vec![])),
                },
                args: vec![],
                destination: simple_place(0),
                target: 1,
                span: SourceSpan::default(),
            }),
            make_block(Terminator::Return),
        ]);

        let executor = SymbolicExecutor::new(&func);
        let postcond = Predicate::Bool(true);
        let vcs = executor.execute(&postcond);

        assert_eq!(vcs.len(), 1);
    }

    #[test]
    fn test_executor_fresh_vc_ids() {
        // Multiple VCs should have unique IDs
        let func = make_test_func(vec![
            make_block(Terminator::Assert {
                cond: Operand::Constant(Constant::Bool(true)),
                expected: true,
                target: 1,
            }),
            make_block(Terminator::Assert {
                cond: Operand::Constant(Constant::Bool(true)),
                expected: true,
                target: 2,
            }),
            make_block(Terminator::Return),
        ]);

        let executor = SymbolicExecutor::new(&func);
        let vcs = executor.execute(&Predicate::Bool(true));

        // Should have 3 VCs with IDs 0, 1, 2
        assert_eq!(vcs.len(), 3);
        assert_eq!(vcs[0].id, VcId(0));
        assert_eq!(vcs[1].id, VcId(1));
        assert_eq!(vcs[2].id, VcId(2));
    }

    #[test]
    fn test_executor_path_condition_in_vc() {
        // Execution through a branch should include path condition
        let func = make_test_func(vec![
            make_block(Terminator::SwitchInt {
                discr: Operand::Constant(Constant::Int(1)),
                targets: vec![(1, 1)],
                otherwise: 2,
            }),
            make_block(Terminator::Return),
            make_block(Terminator::Return),
        ]);

        let executor = SymbolicExecutor::new(&func);
        let vcs = executor.execute(&Predicate::Bool(true));

        // Both paths should have path conditions in their VCs
        assert_eq!(vcs.len(), 2);
        // The first VC should have path condition for discr == 1
        // The second VC should have path condition for discr != 1
    }

    #[test]
    fn test_executor_assert_with_negated_expected() {
        let func = make_test_func(vec![
            make_block(Terminator::Assert {
                cond: Operand::Constant(Constant::Bool(false)),
                expected: false, // Expecting false (assert that !cond)
                target: 1,
            }),
            make_block(Terminator::Return),
        ]);

        let executor = SymbolicExecutor::new(&func);
        let vcs = executor.execute(&Predicate::Bool(true));

        assert_eq!(vcs.len(), 2);
        // The assertion VC should be for Not(cond)
    }

    #[test]
    fn test_dummy_span() {
        let span = SourceSpan::default();
        assert_eq!(span.file.as_ref(), "<unknown>");
        assert_eq!(span.line_start, 0);
        assert_eq!(span.line_end, 0);
        assert_eq!(span.col_start, 0);
        assert_eq!(span.col_end, 0);
    }

    #[test]
    fn test_executor_binary_op_rvalue() {
        // Test assignment with binary operation
        let func = make_test_func(vec![make_block_with_stmts(
            vec![Statement::Assign {
                place: simple_place(1),
                rvalue: Rvalue::BinaryOp(
                    BinOp::Add,
                    Operand::Constant(Constant::Int(1)),
                    Operand::Constant(Constant::Int(2)),
                ),
            }],
            Terminator::Return,
        )]);

        let executor = SymbolicExecutor::new(&func);
        let vcs = executor.execute(&Predicate::Bool(true));

        assert_eq!(vcs.len(), 1);
    }
}
