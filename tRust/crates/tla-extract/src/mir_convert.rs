//! Conversion from MIR state machine extraction results to TLA2Model
//!
//! This module converts the raw MIR state machine data extracted by rustc_verify
//! into the portable TLA2Model format for temporal property verification.
//!
//! Phase 5 of DIRECTIVE_TLA_EXTRACT.

use crate::model::{
    ActionId, Assignment, BinOp, CompareOp, Expr, Predicate, StateId, TLA2Model, Transition,
    VarType, Variable,
};

/// MIR state machine result from compiler extraction (Phase 4)
///
/// This mirrors the types defined in rustc_verify/src/lib.rs
#[derive(Debug, Clone)]
pub struct MirStateMachineResult {
    /// Name of the coroutine/async function
    pub name: String,
    /// Basic blocks from MIR
    pub blocks: Vec<MirBasicBlockInfo>,
    /// Yield points (suspension points)
    pub yield_points: Vec<MirYieldPoint>,
    /// Captured variables
    pub captured_vars: Vec<MirCapturedVar>,
    /// Total state count
    pub state_count: usize,
    /// Total transition count
    pub transition_count: usize,
}

/// Basic block information from MIR
#[derive(Debug, Clone)]
pub struct MirBasicBlockInfo {
    /// Block index
    pub index: usize,
    /// Terminator kind as string
    pub terminator_kind: String,
    /// Successor block indices
    pub successors: Vec<usize>,
    /// Is this a yield point?
    pub is_yield: bool,
    /// Guard condition from SwitchInt (if any)
    pub guard: Option<String>,
    /// Statement count
    pub statement_count: usize,
}

/// Yield point (suspension point) information
#[derive(Debug, Clone)]
pub struct MirYieldPoint {
    /// Block containing the yield
    pub block: usize,
    /// Resume block
    pub resume_block: usize,
    /// Drop block (cleanup)
    pub drop_block: Option<usize>,
    /// Yielded value type
    pub yielded_type: String,
}

/// Captured variable information
#[derive(Debug, Clone)]
pub struct MirCapturedVar {
    /// Variable name
    pub name: String,
    /// Type as string
    pub ty: String,
    /// Is mutably captured?
    pub is_mut: bool,
}

/// Convert MIR state machine result to TLA2Model
///
/// This function:
/// 1. Creates TLA2 VARIABLES from captured variables + state variable
/// 2. Creates TLA2 transitions from basic blocks with guards
/// 3. Identifies initial and terminal states
/// 4. Sets up the INIT predicate
#[must_use]
pub fn convert_mir_to_tla2(mir: &MirStateMachineResult) -> TLA2Model {
    let mut model = TLA2Model::new(&mir.name);

    // 1. Convert captured variables to TLA2 VARIABLES
    for cv in &mir.captured_vars {
        model.variables.push(Variable {
            name: cv.name.clone(),
            ty: parse_type_string(&cv.ty),
            invariant: None,
            initial_value: None,
        });
    }

    // Add implicit _state variable (current basic block / state discriminant)
    model.variables.push(Variable {
        name: "_state".to_string(),
        ty: VarType::Int {
            bits: 32,
            signed: false,
        },
        invariant: Some(Predicate::And(vec![
            Predicate::Compare {
                left: Box::new(Expr::Var("_state".to_string())),
                op: CompareOp::Ge,
                right: Box::new(Expr::Int(0)),
            },
            Predicate::Compare {
                left: Box::new(Expr::Var("_state".to_string())),
                op: CompareOp::Lt,
                right: Box::new(Expr::Int(mir.state_count as i64)),
            },
        ])),
        initial_value: Some(Expr::Int(0)),
    });

    // Add _pc (program counter / current block) variable
    model.variables.push(Variable {
        name: "_pc".to_string(),
        ty: VarType::Int {
            bits: 32,
            signed: false,
        },
        invariant: None,
        initial_value: Some(Expr::Int(0)),
    });

    // 2. Set initial state
    model.initial_state = StateId(0);

    // 3. Build INIT predicate
    model.init = build_mir_init_predicate(mir);

    // 4. Convert blocks to transitions
    let mut action_counter: u64 = 0;
    for block in &mir.blocks {
        for &succ in &block.successors {
            let transition = convert_block_to_transition(block, succ, mir, &mut action_counter);
            model.transitions.push(transition);
        }
    }

    // 5. Identify terminal states (Return terminators)
    for block in &mir.blocks {
        if block.terminator_kind == "Return" || block.terminator_kind == "Unreachable" {
            model.terminal_states.push(StateId(block.index));
        }
    }

    model
}

/// Build the INIT predicate from MIR
fn build_mir_init_predicate(mir: &MirStateMachineResult) -> Predicate {
    let mut conjuncts = vec![];

    // _state = 0 (initial state discriminant)
    conjuncts.push(Predicate::Compare {
        left: Box::new(Expr::Var("_state".to_string())),
        op: CompareOp::Eq,
        right: Box::new(Expr::Int(0)),
    });

    // _pc = 0 (start at block 0)
    conjuncts.push(Predicate::Compare {
        left: Box::new(Expr::Var("_pc".to_string())),
        op: CompareOp::Eq,
        right: Box::new(Expr::Int(0)),
    });

    // Add type constraints for captured variables
    for cv in &mir.captured_vars {
        if let Some(constraint) = type_constraint(&cv.name, &cv.ty) {
            conjuncts.push(constraint);
        }
    }

    if conjuncts.len() == 1 {
        // SAFETY: We just checked len() == 1, so pop() returns Some
        conjuncts.pop().unwrap()
    } else {
        Predicate::And(conjuncts)
    }
}

/// Generate a type constraint predicate for a variable
fn type_constraint(name: &str, ty: &str) -> Option<Predicate> {
    // Extract bounds from integer types
    if let Some(bits) = ty.strip_prefix("i").and_then(|s| s.parse::<u32>().ok()) {
        if bits == 0 {
            return None;
        }
        let (min, max) = if bits >= 64 {
            (i64::MIN, i64::MAX)
        } else {
            let shift = bits - 1;
            let min = -(1i64 << shift);
            let max = (1i64 << shift) - 1;
            (min, max)
        };
        return Some(Predicate::And(vec![
            Predicate::Compare {
                left: Box::new(Expr::Var(name.to_string())),
                op: CompareOp::Ge,
                right: Box::new(Expr::Int(min)),
            },
            Predicate::Compare {
                left: Box::new(Expr::Var(name.to_string())),
                op: CompareOp::Le,
                right: Box::new(Expr::Int(max)),
            },
        ]));
    }

    if let Some(bits) = ty.strip_prefix("u").and_then(|s| s.parse::<u32>().ok()) {
        if bits == 0 {
            return Some(Predicate::Compare {
                left: Box::new(Expr::Var(name.to_string())),
                op: CompareOp::Eq,
                right: Box::new(Expr::Int(0)),
            });
        }
        let max = if bits >= 63 {
            i64::MAX
        } else {
            (1i64 << bits) - 1
        };
        return Some(Predicate::And(vec![
            Predicate::Compare {
                left: Box::new(Expr::Var(name.to_string())),
                op: CompareOp::Ge,
                right: Box::new(Expr::Int(0)),
            },
            Predicate::Compare {
                left: Box::new(Expr::Var(name.to_string())),
                op: CompareOp::Le,
                right: Box::new(Expr::Int(max)),
            },
        ]));
    }

    None
}

/// Convert a basic block transition to TLA2 Transition
fn convert_block_to_transition(
    block: &MirBasicBlockInfo,
    successor: usize,
    mir: &MirStateMachineResult,
    action_counter: &mut u64,
) -> Transition {
    let action_id = ActionId(*action_counter);
    *action_counter += 1;

    // Build guard predicate
    let mut guard_conjuncts = vec![];

    // Guard: current PC must be this block
    guard_conjuncts.push(Predicate::Compare {
        left: Box::new(Expr::Var("_pc".to_string())),
        op: CompareOp::Eq,
        right: Box::new(Expr::Int(block.index as i64)),
    });

    // Add SwitchInt guard if present
    if let Some(guard_str) = &block.guard {
        if let Some(guard_pred) = parse_guard_string(guard_str, successor) {
            guard_conjuncts.push(guard_pred);
        }
    }

    let guard = if guard_conjuncts.len() == 1 {
        // SAFETY: We just checked len() == 1, so pop() returns Some
        guard_conjuncts.pop().unwrap()
    } else {
        Predicate::And(guard_conjuncts)
    };

    // Build assignments
    let mut assignments = vec![];

    // Always update _pc to successor
    assignments.push(Assignment {
        variable: "_pc".to_string(),
        value: Expr::Int(successor as i64),
    });

    // Check if this is a yield point - update _state
    let is_yield = mir.yield_points.iter().any(|yp| yp.block == block.index);
    if is_yield {
        // After yield, state advances
        // Note: The actual state discriminant is managed by SwitchInt guards
        assignments.push(Assignment {
            variable: "_state".to_string(),
            value: Expr::BinOp {
                left: Box::new(Expr::Var("_state".to_string())),
                op: BinOp::Add,
                right: Box::new(Expr::Int(1)),
            },
        });
    }

    // Determine transition name based on terminator
    let name = format!(
        "{}_{}_to_{}",
        block.terminator_kind.to_lowercase(),
        block.index,
        successor
    );

    Transition {
        action_id,
        name,
        from: Some(StateId(block.index)),
        to: Some(StateId(successor)),
        guard,
        assignments,
        is_yield,
        is_poll: block.terminator_kind == "Call",
    }
}

/// Parse a guard string from SwitchInt into a Predicate
///
/// Format: "discr == N" or "discr: N1, N2, ..."
fn parse_guard_string(guard_str: &str, target_successor: usize) -> Option<Predicate> {
    // Simple parsing for common patterns
    if guard_str.contains("==") {
        let parts: Vec<&str> = guard_str.split("==").collect();
        if parts.len() == 2 {
            let var = parts[0].trim();
            if let Ok(val) = parts[1].trim().parse::<i64>() {
                return Some(Predicate::Compare {
                    left: Box::new(Expr::Var(var.to_string())),
                    op: CompareOp::Eq,
                    right: Box::new(Expr::Int(val)),
                });
            }
        }
    }

    // For "discr: targets" format, create equality with target
    if guard_str.contains(':') {
        let parts: Vec<&str> = guard_str.split(':').collect();
        if !parts.is_empty() {
            let var = parts[0].trim();
            // Create guard based on successor index
            // (actual discriminant value may differ but this preserves structure)
            return Some(Predicate::Compare {
                left: Box::new(Expr::Var(var.to_string())),
                op: CompareOp::Eq,
                right: Box::new(Expr::Int(target_successor as i64)),
            });
        }
    }

    None
}

/// Parse a type string to VarType
fn parse_type_string(ty: &str) -> VarType {
    // Handle common Rust types
    match ty {
        "bool" => VarType::Bool,
        "i8" => VarType::Int {
            bits: 8,
            signed: true,
        },
        "i16" => VarType::Int {
            bits: 16,
            signed: true,
        },
        "i32" => VarType::Int {
            bits: 32,
            signed: true,
        },
        "i64" | "isize" => VarType::Int {
            bits: 64,
            signed: true,
        }, // isize assumed 64-bit
        "i128" => VarType::Int {
            bits: 128,
            signed: true,
        },
        "u8" => VarType::Int {
            bits: 8,
            signed: false,
        },
        "u16" => VarType::Int {
            bits: 16,
            signed: false,
        },
        "u32" => VarType::Int {
            bits: 32,
            signed: false,
        },
        "u64" | "usize" => VarType::Int {
            bits: 64,
            signed: false,
        }, // usize assumed 64-bit
        "u128" => VarType::Int {
            bits: 128,
            signed: false,
        },
        _ => VarType::Opaque(ty.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_convert_simple_mir() {
        let mir = MirStateMachineResult {
            name: "simple_test".to_string(),
            blocks: vec![
                MirBasicBlockInfo {
                    index: 0,
                    terminator_kind: "Goto".to_string(),
                    successors: vec![1],
                    is_yield: false,
                    guard: None,
                    statement_count: 0,
                },
                MirBasicBlockInfo {
                    index: 1,
                    terminator_kind: "Return".to_string(),
                    successors: vec![],
                    is_yield: false,
                    guard: None,
                    statement_count: 0,
                },
            ],
            yield_points: vec![],
            captured_vars: vec![],
            state_count: 2,
            transition_count: 1,
        };

        let model = convert_mir_to_tla2(&mir);

        assert_eq!(model.name, "simple_test");
        // _state and _pc variables
        assert_eq!(model.variables.len(), 2);
        assert_eq!(model.transitions.len(), 1);
        assert_eq!(model.terminal_states.len(), 1);
    }

    #[test]
    fn test_convert_mir_with_captured_vars() {
        let mir = MirStateMachineResult {
            name: "with_vars".to_string(),
            blocks: vec![MirBasicBlockInfo {
                index: 0,
                terminator_kind: "Return".to_string(),
                successors: vec![],
                is_yield: false,
                guard: None,
                statement_count: 0,
            }],
            yield_points: vec![],
            captured_vars: vec![
                MirCapturedVar {
                    name: "x".to_string(),
                    ty: "i32".to_string(),
                    is_mut: false,
                },
                MirCapturedVar {
                    name: "y".to_string(),
                    ty: "bool".to_string(),
                    is_mut: true,
                },
            ],
            state_count: 1,
            transition_count: 0,
        };

        let model = convert_mir_to_tla2(&mir);

        // x, y, _state, _pc
        assert_eq!(model.variables.len(), 4);
        assert_eq!(model.variables[0].name, "x");
        assert_eq!(model.variables[1].name, "y");
    }

    #[test]
    fn test_convert_mir_with_switchint_guard() {
        let mir = MirStateMachineResult {
            name: "guarded".to_string(),
            blocks: vec![
                MirBasicBlockInfo {
                    index: 0,
                    terminator_kind: "SwitchInt".to_string(),
                    successors: vec![1, 2],
                    is_yield: false,
                    guard: Some("discr == 0".to_string()),
                    statement_count: 0,
                },
                MirBasicBlockInfo {
                    index: 1,
                    terminator_kind: "Return".to_string(),
                    successors: vec![],
                    is_yield: false,
                    guard: None,
                    statement_count: 0,
                },
                MirBasicBlockInfo {
                    index: 2,
                    terminator_kind: "Return".to_string(),
                    successors: vec![],
                    is_yield: false,
                    guard: None,
                    statement_count: 0,
                },
            ],
            yield_points: vec![],
            captured_vars: vec![],
            state_count: 3,
            transition_count: 2,
        };

        let model = convert_mir_to_tla2(&mir);

        // Two transitions from block 0
        assert_eq!(model.transitions.len(), 2);
        // Both terminal
        assert_eq!(model.terminal_states.len(), 2);
    }

    #[test]
    fn test_parse_type_string() {
        assert!(matches!(parse_type_string("bool"), VarType::Bool));
        assert!(matches!(
            parse_type_string("i32"),
            VarType::Int {
                bits: 32,
                signed: true
            }
        ));
        assert!(matches!(
            parse_type_string("u64"),
            VarType::Int {
                bits: 64,
                signed: false
            }
        ));
        assert!(matches!(parse_type_string("MyStruct"), VarType::Opaque(_)));
    }

    #[test]
    fn test_parse_guard_string() {
        let guard = parse_guard_string("discr == 0", 1).unwrap();
        assert!(matches!(guard, Predicate::Compare { .. }));

        let guard2 = parse_guard_string("state: 0, 1, 2", 1).unwrap();
        assert!(matches!(guard2, Predicate::Compare { .. }));
    }
}
