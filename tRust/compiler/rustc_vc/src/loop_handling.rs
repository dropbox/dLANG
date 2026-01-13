//! Loop Handling for Verification
//!
//! Loops require special treatment in verification:
//! 1. Loop invariants must be provided or inferred
//! 2. Termination requires a decreasing measure
//! 3. The invariant must be inductive

use crate::{MirFunction, Terminator};
use vc_ir::{BackendHint, Expr, Predicate, SourceSpan, VcId, VcKind, VerificationCondition};

/// Information about a loop in the CFG
#[derive(Debug, Clone)]
pub struct LoopInfo {
    /// Header block (entry point, contains back-edge target)
    pub header: usize,
    /// Back-edge sources (blocks that jump back to header)
    pub back_edges: Vec<usize>,
    /// All blocks in the loop body
    pub body: Vec<usize>,
    /// Exit blocks (successors outside the loop)
    pub exits: Vec<usize>,
}

/// Loop analysis result
pub struct LoopAnalysis {
    pub loops: Vec<LoopInfo>,
}

impl LoopAnalysis {
    /// Analyze a function to find all loops
    #[must_use]
    pub fn analyze(func: &MirFunction) -> Self {
        let mut loops = vec![];

        // Simple back-edge detection
        // A back-edge is an edge from B to A where A dominates B
        // For simplicity, we detect self-loops and simple while-loops

        for (idx, block) in func.blocks.iter().enumerate() {
            match &block.terminator {
                Terminator::Goto { target } if *target <= idx => {
                    // Back-edge found
                    loops.push(LoopInfo {
                        header: *target,
                        back_edges: vec![idx],
                        body: (*target..=idx).collect(),
                        exits: vec![], // Would need more analysis
                    });
                }
                Terminator::SwitchInt {
                    targets, otherwise, ..
                } => {
                    for (_, target) in targets {
                        if *target <= idx {
                            loops.push(LoopInfo {
                                header: *target,
                                back_edges: vec![idx],
                                body: (*target..=idx).collect(),
                                exits: vec![],
                            });
                        }
                    }
                    if *otherwise <= idx {
                        loops.push(LoopInfo {
                            header: *otherwise,
                            back_edges: vec![idx],
                            body: (*otherwise..=idx).collect(),
                            exits: vec![],
                        });
                    }
                }
                _ => {}
            }
        }

        Self { loops }
    }
}

/// Generate VCs for a loop with invariant
pub struct LoopVcGenerator {
    next_vc_id: u64,
}

impl LoopVcGenerator {
    #[must_use]
    pub const fn new(start_id: u64) -> Self {
        Self {
            next_vc_id: start_id,
        }
    }

    const fn fresh_vc_id(&mut self) -> VcId {
        let id = VcId(self.next_vc_id);
        self.next_vc_id += 1;
        id
    }

    /// Generate VCs for proving a loop invariant
    ///
    /// For a loop with invariant I:
    /// 1. Base case: precondition => I (invariant holds on entry)
    /// 2. Inductive case: I && guard => wp(body, I) (invariant preserved)
    /// 3. Use case: I && !guard => postcondition (invariant implies post on exit)
    pub fn generate_loop_vcs(
        &mut self,
        loop_info: &LoopInfo,
        invariant: &Predicate,
        precondition: &Predicate,
        postcondition: &Predicate,
        guard: Option<&Predicate>,
    ) -> Vec<VerificationCondition> {
        let mut vcs = vec![];

        // VC 1: Base case - precondition implies invariant
        vcs.push(VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("loop invariant base case (block {})", loop_info.header),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: precondition.clone(),
                consequent: invariant.clone(),
            },
            preferred_backend: Some(BackendHint::Smt),
        });

        // VC 2: Inductive case - invariant && guard implies wp(body, invariant)
        // For now, simplified: just check that invariant is preserved
        let inductive_pre = if let Some(g) = guard {
            Predicate::And(vec![invariant.clone(), g.clone()])
        } else {
            invariant.clone()
        };

        vcs.push(VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("loop invariant inductive case (block {})", loop_info.header),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: inductive_pre,
                consequent: invariant.clone(), // Would be wp(body, invariant)
            },
            preferred_backend: Some(BackendHint::Smt),
        });

        // VC 3: Use case - invariant && !guard implies postcondition
        let exit_pre = if let Some(g) = guard {
            Predicate::And(vec![invariant.clone(), g.clone().not()])
        } else {
            invariant.clone()
        };

        vcs.push(VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("loop invariant use case (block {})", loop_info.header),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: exit_pre,
                consequent: postcondition.clone(),
            },
            preferred_backend: Some(BackendHint::Smt),
        });

        vcs
    }

    /// Generate termination VC for a loop
    ///
    /// Requires a decreasing measure (variant) that:
    /// 1. Is non-negative at loop entry
    /// 2. Decreases on each iteration
    /// 3. When it reaches 0, the loop must exit
    pub fn generate_termination_vc(
        &mut self,
        loop_info: &LoopInfo,
        invariant: &Predicate,
        variant: &Expr,
        guard: Option<&Predicate>,
    ) -> Vec<VerificationCondition> {
        let mut vcs = vec![];

        // VC: variant >= 0
        vcs.push(VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("loop variant non-negative (block {})", loop_info.header),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: invariant.clone(),
                consequent: Predicate::Expr(Expr::Ge(
                    Box::new(variant.clone()),
                    Box::new(Expr::IntLit(0)),
                )),
            },
            preferred_backend: Some(BackendHint::Smt),
        });

        // VC: variant decreases on each iteration
        // variant' < variant (where variant' is value after one iteration)
        let variant_prime = Expr::Var("variant_prime".to_string()); // Placeholder
        let decreases_pre = if let Some(g) = guard {
            Predicate::And(vec![invariant.clone(), g.clone()])
        } else {
            invariant.clone()
        };

        vcs.push(VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("loop variant decreases (block {})", loop_info.header),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: decreases_pre,
                consequent: Predicate::Expr(Expr::Lt(
                    Box::new(variant_prime),
                    Box::new(variant.clone()),
                )),
            },
            preferred_backend: Some(BackendHint::Smt),
        });

        vcs
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BasicBlock, Constant, LocalDecl, MirType, Operand};

    // Helper to create a minimal MirFunction for testing
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

    // Helper to create a basic block with a terminator
    fn make_block(terminator: Terminator) -> BasicBlock {
        BasicBlock {
            statements: vec![],
            terminator,
        }
    }

    // ===== LoopInfo tests =====
    #[test]
    fn test_loop_info_creation() {
        let info = LoopInfo {
            header: 0,
            back_edges: vec![2],
            body: vec![0, 1, 2],
            exits: vec![3],
        };
        assert_eq!(info.header, 0);
        assert_eq!(info.back_edges, vec![2]);
        assert_eq!(info.body.len(), 3);
        assert_eq!(info.exits, vec![3]);
    }

    #[test]
    fn test_loop_info_clone() {
        let info = LoopInfo {
            header: 1,
            back_edges: vec![3, 4],
            body: vec![1, 2, 3, 4],
            exits: vec![5],
        };
        let cloned = info.clone();
        assert_eq!(cloned.header, info.header);
        assert_eq!(cloned.back_edges, info.back_edges);
    }

    // ===== LoopAnalysis tests =====
    #[test]
    fn test_loop_analysis_no_loops() {
        // Linear function: block0 -> block1 -> return
        let func = make_test_func(vec![
            make_block(Terminator::Goto { target: 1 }),
            make_block(Terminator::Return),
        ]);

        let analysis = LoopAnalysis::analyze(&func);
        assert!(analysis.loops.is_empty());
    }

    #[test]
    fn test_loop_analysis_simple_loop() {
        // Simple while loop: block0 -> block1 -> block0 (back edge)
        let func = make_test_func(vec![
            make_block(Terminator::Goto { target: 1 }),
            make_block(Terminator::Goto { target: 0 }), // Back edge to block 0
        ]);

        let analysis = LoopAnalysis::analyze(&func);
        assert_eq!(analysis.loops.len(), 1);
        assert_eq!(analysis.loops[0].header, 0);
        assert_eq!(analysis.loops[0].back_edges, vec![1]);
    }

    #[test]
    fn test_loop_analysis_self_loop() {
        // Self loop: block0 jumps to itself
        let func = make_test_func(vec![make_block(Terminator::Goto { target: 0 })]);

        let analysis = LoopAnalysis::analyze(&func);
        assert_eq!(analysis.loops.len(), 1);
        assert_eq!(analysis.loops[0].header, 0);
        assert_eq!(analysis.loops[0].back_edges, vec![0]);
        assert_eq!(analysis.loops[0].body, vec![0]);
    }

    #[test]
    fn test_loop_analysis_switch_int_loop() {
        // Loop with conditional: block0 -> block1, block1 switches back to block0
        let func = make_test_func(vec![
            make_block(Terminator::Goto { target: 1 }),
            make_block(Terminator::SwitchInt {
                discr: Operand::Constant(Constant::Bool(true)),
                targets: vec![(0, 0)], // Back edge to block 0
                otherwise: 2,
            }),
            make_block(Terminator::Return),
        ]);

        let analysis = LoopAnalysis::analyze(&func);
        assert_eq!(analysis.loops.len(), 1);
        assert_eq!(analysis.loops[0].header, 0);
    }

    #[test]
    fn test_loop_analysis_switch_int_otherwise_loop() {
        // Loop where otherwise branch goes back
        let func = make_test_func(vec![
            make_block(Terminator::Goto { target: 1 }),
            make_block(Terminator::SwitchInt {
                discr: Operand::Constant(Constant::Bool(true)),
                targets: vec![(1, 2)],
                otherwise: 0, // Back edge via otherwise
            }),
            make_block(Terminator::Return),
        ]);

        let analysis = LoopAnalysis::analyze(&func);
        assert_eq!(analysis.loops.len(), 1);
    }

    #[test]
    fn test_loop_analysis_no_back_edge() {
        // Forward-only control flow
        let func = make_test_func(vec![
            make_block(Terminator::SwitchInt {
                discr: Operand::Constant(Constant::Bool(true)),
                targets: vec![(0, 1)],
                otherwise: 2,
            }),
            make_block(Terminator::Goto { target: 2 }),
            make_block(Terminator::Return),
        ]);

        let analysis = LoopAnalysis::analyze(&func);
        assert!(analysis.loops.is_empty());
    }

    // ===== LoopVcGenerator tests =====
    #[test]
    fn test_loop_vc_generator_new() {
        let gen = LoopVcGenerator::new(100);
        assert_eq!(gen.next_vc_id, 100);
    }

    #[test]
    fn test_loop_vc_generator_fresh_id() {
        let mut gen = LoopVcGenerator::new(0);
        let id1 = gen.fresh_vc_id();
        let id2 = gen.fresh_vc_id();
        let id3 = gen.fresh_vc_id();
        assert_eq!(id1.0, 0);
        assert_eq!(id2.0, 1);
        assert_eq!(id3.0, 2);
    }

    #[test]
    fn test_generate_loop_vcs_basic() {
        let mut gen = LoopVcGenerator::new(0);
        let loop_info = LoopInfo {
            header: 0,
            back_edges: vec![1],
            body: vec![0, 1],
            exits: vec![2],
        };
        let invariant = Predicate::Bool(true);
        let precondition = Predicate::Bool(true);
        let postcondition = Predicate::Bool(true);

        let vcs =
            gen.generate_loop_vcs(&loop_info, &invariant, &precondition, &postcondition, None);

        // Should generate 3 VCs: base, inductive, use
        assert_eq!(vcs.len(), 3);
        assert!(vcs[0].name.contains("base case"));
        assert!(vcs[1].name.contains("inductive case"));
        assert!(vcs[2].name.contains("use case"));
    }

    #[test]
    fn test_generate_loop_vcs_with_guard() {
        let mut gen = LoopVcGenerator::new(0);
        let loop_info = LoopInfo {
            header: 0,
            back_edges: vec![1],
            body: vec![0, 1],
            exits: vec![2],
        };
        let invariant = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("n".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let precondition = Predicate::Bool(true);
        let postcondition = Predicate::Bool(true);
        let guard = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("n".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let vcs = gen.generate_loop_vcs(
            &loop_info,
            &invariant,
            &precondition,
            &postcondition,
            Some(&guard),
        );

        assert_eq!(vcs.len(), 3);
        // Inductive case should include guard in antecedent
        if let VcKind::Implies { antecedent, .. } = &vcs[1].condition {
            assert!(matches!(antecedent, Predicate::And(_)));
        } else {
            panic!("Expected Implies");
        }
    }

    #[test]
    fn test_generate_loop_vcs_vc_ids() {
        let mut gen = LoopVcGenerator::new(100);
        let loop_info = LoopInfo {
            header: 0,
            back_edges: vec![1],
            body: vec![0, 1],
            exits: vec![],
        };
        let inv = Predicate::Bool(true);
        let pre = Predicate::Bool(true);
        let post = Predicate::Bool(true);

        let vcs = gen.generate_loop_vcs(&loop_info, &inv, &pre, &post, None);

        assert_eq!(vcs[0].id.0, 100);
        assert_eq!(vcs[1].id.0, 101);
        assert_eq!(vcs[2].id.0, 102);
    }

    #[test]
    fn test_generate_loop_vcs_backend_hint() {
        let mut gen = LoopVcGenerator::new(0);
        let loop_info = LoopInfo {
            header: 0,
            back_edges: vec![],
            body: vec![0],
            exits: vec![],
        };
        let inv = Predicate::Bool(true);
        let pre = Predicate::Bool(true);
        let post = Predicate::Bool(true);

        let vcs = gen.generate_loop_vcs(&loop_info, &inv, &pre, &post, None);

        for vc in &vcs {
            assert_eq!(vc.preferred_backend, Some(BackendHint::Smt));
        }
    }

    #[test]
    fn test_generate_termination_vc() {
        let mut gen = LoopVcGenerator::new(0);
        let loop_info = LoopInfo {
            header: 0,
            back_edges: vec![1],
            body: vec![0, 1],
            exits: vec![2],
        };
        let invariant = Predicate::Bool(true);
        let variant = Expr::Var("n".to_string());

        let vcs = gen.generate_termination_vc(&loop_info, &invariant, &variant, None);

        // Should generate 2 VCs: non-negative and decreases
        assert_eq!(vcs.len(), 2);
        assert!(vcs[0].name.contains("non-negative"));
        assert!(vcs[1].name.contains("decreases"));
    }

    #[test]
    fn test_generate_termination_vc_with_guard() {
        let mut gen = LoopVcGenerator::new(0);
        let loop_info = LoopInfo {
            header: 0,
            back_edges: vec![1],
            body: vec![0, 1],
            exits: vec![2],
        };
        let invariant = Predicate::Bool(true);
        let variant = Expr::Var("n".to_string());
        let guard = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("n".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let vcs = gen.generate_termination_vc(&loop_info, &invariant, &variant, Some(&guard));

        assert_eq!(vcs.len(), 2);
        // The decreases VC should have guard in its antecedent
        if let VcKind::Implies { antecedent, .. } = &vcs[1].condition {
            assert!(matches!(antecedent, Predicate::And(_)));
        } else {
            panic!("Expected Implies for decreases VC");
        }
    }

    #[test]
    fn test_generate_termination_vc_ids() {
        let mut gen = LoopVcGenerator::new(50);
        let loop_info = LoopInfo {
            header: 0,
            back_edges: vec![],
            body: vec![0],
            exits: vec![],
        };
        let inv = Predicate::Bool(true);
        let var = Expr::IntLit(10);

        let vcs = gen.generate_termination_vc(&loop_info, &inv, &var, None);

        assert_eq!(vcs[0].id.0, 50);
        assert_eq!(vcs[1].id.0, 51);
    }

    // ===== dummy_span tests =====
    #[test]
    fn test_dummy_span() {
        let span = SourceSpan::default();
        assert_eq!(span.file.as_ref(), "<unknown>");
        assert_eq!(span.line_start, 0);
        assert_eq!(span.line_end, 0);
        assert_eq!(span.col_start, 0);
        assert_eq!(span.col_end, 0);
    }

    // ===== Integration-style tests =====
    #[test]
    fn test_analyze_and_generate_vcs() {
        // Create a function with a simple loop
        let func = make_test_func(vec![
            make_block(Terminator::Goto { target: 1 }),
            make_block(Terminator::SwitchInt {
                discr: Operand::Constant(Constant::Bool(true)),
                targets: vec![(1, 2)],
                otherwise: 0, // Back edge
            }),
            make_block(Terminator::Return),
        ]);

        // Analyze to find loops
        let analysis = LoopAnalysis::analyze(&func);
        assert!(!analysis.loops.is_empty());

        // Generate VCs for the first loop
        let mut gen = LoopVcGenerator::new(0);
        let inv = Predicate::Bool(true);
        let pre = Predicate::Bool(true);
        let post = Predicate::Bool(true);

        let vcs = gen.generate_loop_vcs(&analysis.loops[0], &inv, &pre, &post, None);
        assert_eq!(vcs.len(), 3);
    }
}
