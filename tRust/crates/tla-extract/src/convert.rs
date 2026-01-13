//! Conversion from vc_ir::AsyncStateMachine to TLA2Model
//!
//! This module implements the conversion from vc_ir types to the portable
//! TLA2Model format that can be consumed by TLA2 for temporal property verification.

use crate::model::{
    ActionId, Assignment, BinOp, CompareOp, Expr, Predicate, StateId, TLA2Model, Transition,
    UnaryOp, VarType, Variable,
};
use vc_ir::temporal::{AsyncStateKind, AsyncStateMachine, CapturedVariable};
use vc_ir::VcType;

/// Convert an AsyncStateMachine from vc_ir to a TLA2Model
pub fn convert_to_tla2(sm: &AsyncStateMachine) -> TLA2Model {
    let mut model = TLA2Model::new(&sm.name);

    // Convert captured variables
    model.variables = sm
        .captured_variables
        .iter()
        .map(convert_captured_variable)
        .collect();

    // Add implicit state variable for current state
    model.variables.push(Variable {
        name: "_state".to_string(),
        ty: VarType::Int {
            bits: 32,
            signed: false,
        },
        invariant: None,
        initial_value: Some(Expr::Int(sm.initial as i64)),
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
        model
            .transitions
            .push(convert_transition(trans, &mut action_counter));
    }

    // Build init predicate
    model.init = build_init_predicate(sm);

    model
}

/// Convert a captured variable to TLA2 Variable
fn convert_captured_variable(cv: &CapturedVariable) -> Variable {
    Variable {
        name: cv.name.clone(),
        ty: convert_vc_type(&cv.ty),
        invariant: None,
        initial_value: None,
    }
}

/// Convert a vc_ir transition to TLA2 Transition
fn convert_transition(
    trans: &vc_ir::temporal::AsyncTransition,
    action_counter: &mut u64,
) -> Transition {
    let action_id = ActionId(*action_counter);
    *action_counter += 1;

    // Convert guard if present
    let guard = trans
        .guard
        .as_ref()
        .map_or(Predicate::Bool(true), convert_predicate_from_vc);

    // Convert effects to assignments
    let assignments: Vec<Assignment> = trans
        .effect
        .iter()
        .map(|eff| Assignment {
            variable: eff.variable.clone(),
            value: convert_expr_from_vc(&eff.value),
        })
        .collect();

    Transition {
        action_id,
        name: format!("t{}_{}", trans.from, trans.to),
        from: Some(StateId(trans.from)),
        to: Some(StateId(trans.to)),
        guard,
        assignments,
        is_yield: trans.is_yield,
        is_poll: trans.is_poll,
    }
}

/// Convert VcType to TLA2 VarType
///
/// VcType variants:
/// - Bool
/// - Int { signed, bits }
/// - Float { bits }
/// - BitVec { bits }
/// - Array { elem, len: Option<usize> }
/// - Tuple(Vec<VcType>)
/// - Struct { name, fields }
/// - Ref { mutable, inner }
/// - Tensor { elem, shape }
/// - Abstract(String)
fn convert_vc_type(ty: &VcType) -> VarType {
    match ty {
        VcType::Bool => VarType::Bool,
        VcType::Int { signed, bits } => VarType::Int {
            bits: *bits as u8,
            signed: *signed,
        },
        VcType::Float { bits: _ } => VarType::Opaque("float".to_string()),
        VcType::BitVec { bits } => VarType::Opaque(format!("bitvec{bits}")),
        VcType::Array { elem, len } => VarType::Array {
            elem: Box::new(convert_vc_type(elem)),
            len: len.unwrap_or(0),
        },
        VcType::Tuple(elems) => VarType::Tuple(elems.iter().map(convert_vc_type).collect()),
        VcType::Struct { name, .. } | VcType::Abstract(name) => VarType::Opaque(name.clone()),
        VcType::Ref { inner, .. } => convert_vc_type(inner),
        VcType::Tensor { elem, shape } => {
            // Model tensors as nested arrays
            let base = convert_vc_type(elem);
            shape.iter().rev().fold(base, |acc, dim| VarType::Array {
                elem: Box::new(acc),
                len: *dim,
            })
        }
    }
}

/// Convert vc_ir Predicate to TLA2 Predicate
///
/// vc_ir::Predicate variants:
/// - Bool(bool)
/// - Expr(Expr)
/// - Not(Box<Predicate>)
/// - And(Vec<Predicate>)
/// - Or(Vec<Predicate>)
/// - Implies(Box<Predicate>, Box<Predicate>)
/// - Iff(Box<Predicate>, Box<Predicate>)
/// - Forall { vars, triggers, body }
/// - Exists { vars, body }
/// - Let { bindings, body }
fn convert_predicate_from_vc(pred: &vc_ir::Predicate) -> Predicate {
    match pred {
        vc_ir::Predicate::Bool(b) => Predicate::Bool(*b),
        vc_ir::Predicate::Expr(e) => {
            // Convert expression to a predicate (assume it's a boolean expr)
            let expr = convert_expr_from_vc(e);
            // If the expression is a variable, treat it as a predicate variable
            match expr {
                Expr::Var(v) => Predicate::Var(v),
                Expr::Bool(b) => Predicate::Bool(b),
                // For other expressions, wrap in a comparison with true
                other => Predicate::Compare {
                    left: Box::new(other),
                    op: CompareOp::Eq,
                    right: Box::new(Expr::Bool(true)),
                },
            }
        }
        vc_ir::Predicate::Not(p) => Predicate::Not(Box::new(convert_predicate_from_vc(p))),
        vc_ir::Predicate::And(preds) => {
            Predicate::And(preds.iter().map(convert_predicate_from_vc).collect())
        }
        vc_ir::Predicate::Or(preds) => {
            Predicate::Or(preds.iter().map(convert_predicate_from_vc).collect())
        }
        vc_ir::Predicate::Implies(lhs, rhs) => Predicate::Implies(
            Box::new(convert_predicate_from_vc(lhs)),
            Box::new(convert_predicate_from_vc(rhs)),
        ),
        vc_ir::Predicate::Iff(lhs, rhs) => {
            // A <=> B is equivalent to (A => B) /\ (B => A)
            let lhs_conv = convert_predicate_from_vc(lhs);
            let rhs_conv = convert_predicate_from_vc(rhs);
            Predicate::And(vec![
                Predicate::Implies(Box::new(lhs_conv.clone()), Box::new(rhs_conv.clone())),
                Predicate::Implies(Box::new(rhs_conv), Box::new(lhs_conv)),
            ])
        }
        vc_ir::Predicate::Forall {
            vars,
            triggers: _,
            body,
        } => {
            // Convert each bound variable to a ForAll
            // For multiple vars, nest them: forall x. forall y. body
            let body_conv = convert_predicate_from_vc(body);
            vars.iter()
                .rev()
                .fold(body_conv, |acc, (var, ty)| Predicate::ForAll {
                    var: var.clone(),
                    domain: Box::new(type_to_domain(ty)),
                    body: Box::new(acc),
                })
        }
        vc_ir::Predicate::Exists { vars, body } => {
            // Convert each bound variable to an Exists
            let body_conv = convert_predicate_from_vc(body);
            vars.iter()
                .rev()
                .fold(body_conv, |acc, (var, ty)| Predicate::Exists {
                    var: var.clone(),
                    domain: Box::new(type_to_domain(ty)),
                    body: Box::new(acc),
                })
        }
        vc_ir::Predicate::Let { bindings: _, body } => {
            // Let bindings can be modeled as substitution, but for now
            // we'll just convert the body (losing the bindings - conservative)
            convert_predicate_from_vc(body)
        }
    }
}

/// Convert a VcType to a domain expression (for quantifiers)
fn type_to_domain(ty: &VcType) -> Expr {
    // Return an expression representing the domain of values of this type
    // For now, use a symbolic representation
    match ty {
        VcType::Bool => Expr::SetLit(vec![Expr::Bool(false), Expr::Bool(true)]),
        VcType::Int {
            signed: true,
            bits: 8,
        } => Expr::Apply {
            func: "Int8".to_string(),
            args: vec![],
        },
        VcType::Int {
            signed: true,
            bits: 16,
        } => Expr::Apply {
            func: "Int16".to_string(),
            args: vec![],
        },
        VcType::Int {
            signed: true,
            bits: 32,
        } => Expr::Apply {
            func: "Int32".to_string(),
            args: vec![],
        },
        VcType::Int {
            signed: true,
            bits: 64,
        } => Expr::Apply {
            func: "Int64".to_string(),
            args: vec![],
        },
        VcType::Int {
            signed: false,
            bits,
        } => Expr::Apply {
            func: format!("Uint{bits}"),
            args: vec![],
        },
        _ => Expr::Apply {
            func: "Universe".to_string(),
            args: vec![],
        },
    }
}

/// Convert vc_ir Expr to TLA2 Expr
///
/// vc_ir::Expr variants include:
/// - BoolLit(bool), IntLit(i128), FloatLit(f64), BitVecLit{..}
/// - Var(String), Old(Box<Expr>), Result
/// - Neg, Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, BitNot, Shl, Shr
/// - Eq, Ne, Lt, Le, Gt, Ge
/// - Not, And, Or
/// - Ite { cond, then_, else_ }
/// - ArrayIndex, ArrayLen, ArraySlice, TupleField, StructField
/// - Apply { func, args }
/// - Forall, Exists
fn convert_expr_from_vc(expr: &vc_ir::Expr) -> Expr {
    match expr {
        // Literals
        vc_ir::Expr::BoolLit(b) => Expr::Bool(*b),
        vc_ir::Expr::IntLit(i) => Expr::Int(*i as i64),
        vc_ir::Expr::FloatLit(_) => Expr::Var("_float".to_string()),
        vc_ir::Expr::BitVecLit { bits: _, value: _ } => Expr::Var("_bitvec".to_string()),

        // Variables
        vc_ir::Expr::Var(v) => Expr::Var(v.clone()),
        vc_ir::Expr::Old(inner) => {
            // Old values - prefix with "old_" for TLA2
            let inner_expr = convert_expr_from_vc(inner);
            match inner_expr {
                Expr::Var(v) => Expr::Var(format!("old_{v}")),
                _ => inner_expr,
            }
        }
        vc_ir::Expr::Result => Expr::Var("result".to_string()),

        // Unary arithmetic
        vc_ir::Expr::Neg(e) => Expr::UnaryOp {
            op: UnaryOp::Neg,
            arg: Box::new(convert_expr_from_vc(e)),
        },

        // Binary arithmetic
        vc_ir::Expr::Add(l, r) => Expr::BinOp {
            left: Box::new(convert_expr_from_vc(l)),
            op: BinOp::Add,
            right: Box::new(convert_expr_from_vc(r)),
        },
        vc_ir::Expr::Sub(l, r) => Expr::BinOp {
            left: Box::new(convert_expr_from_vc(l)),
            op: BinOp::Sub,
            right: Box::new(convert_expr_from_vc(r)),
        },
        vc_ir::Expr::Mul(l, r) => Expr::BinOp {
            left: Box::new(convert_expr_from_vc(l)),
            op: BinOp::Mul,
            right: Box::new(convert_expr_from_vc(r)),
        },
        vc_ir::Expr::Div(l, r) => Expr::BinOp {
            left: Box::new(convert_expr_from_vc(l)),
            op: BinOp::Div,
            right: Box::new(convert_expr_from_vc(r)),
        },
        vc_ir::Expr::Rem(l, r) => Expr::BinOp {
            left: Box::new(convert_expr_from_vc(l)),
            op: BinOp::Mod,
            right: Box::new(convert_expr_from_vc(r)),
        },

        // Bitwise
        vc_ir::Expr::BitAnd(l, r) => Expr::BinOp {
            left: Box::new(convert_expr_from_vc(l)),
            op: BinOp::BitAnd,
            right: Box::new(convert_expr_from_vc(r)),
        },
        vc_ir::Expr::BitOr(l, r) => Expr::BinOp {
            left: Box::new(convert_expr_from_vc(l)),
            op: BinOp::BitOr,
            right: Box::new(convert_expr_from_vc(r)),
        },
        vc_ir::Expr::BitXor(l, r) => Expr::BinOp {
            left: Box::new(convert_expr_from_vc(l)),
            op: BinOp::BitXor,
            right: Box::new(convert_expr_from_vc(r)),
        },
        vc_ir::Expr::BitNot(e) => Expr::UnaryOp {
            op: UnaryOp::BitNot,
            arg: Box::new(convert_expr_from_vc(e)),
        },
        vc_ir::Expr::Shl(l, r) => Expr::BinOp {
            left: Box::new(convert_expr_from_vc(l)),
            op: BinOp::Shl,
            right: Box::new(convert_expr_from_vc(r)),
        },
        vc_ir::Expr::Shr(l, r) => Expr::BinOp {
            left: Box::new(convert_expr_from_vc(l)),
            op: BinOp::Shr,
            right: Box::new(convert_expr_from_vc(r)),
        },

        // Comparisons - convert to boolean expressions via conditional
        vc_ir::Expr::Eq(l, r) => Expr::If {
            cond: Box::new(Predicate::Compare {
                left: Box::new(convert_expr_from_vc(l)),
                op: CompareOp::Eq,
                right: Box::new(convert_expr_from_vc(r)),
            }),
            then_: Box::new(Expr::Bool(true)),
            else_: Box::new(Expr::Bool(false)),
        },
        vc_ir::Expr::Ne(l, r) => Expr::If {
            cond: Box::new(Predicate::Compare {
                left: Box::new(convert_expr_from_vc(l)),
                op: CompareOp::Ne,
                right: Box::new(convert_expr_from_vc(r)),
            }),
            then_: Box::new(Expr::Bool(true)),
            else_: Box::new(Expr::Bool(false)),
        },
        vc_ir::Expr::Lt(l, r) => Expr::If {
            cond: Box::new(Predicate::Compare {
                left: Box::new(convert_expr_from_vc(l)),
                op: CompareOp::Lt,
                right: Box::new(convert_expr_from_vc(r)),
            }),
            then_: Box::new(Expr::Bool(true)),
            else_: Box::new(Expr::Bool(false)),
        },
        vc_ir::Expr::Le(l, r) => Expr::If {
            cond: Box::new(Predicate::Compare {
                left: Box::new(convert_expr_from_vc(l)),
                op: CompareOp::Le,
                right: Box::new(convert_expr_from_vc(r)),
            }),
            then_: Box::new(Expr::Bool(true)),
            else_: Box::new(Expr::Bool(false)),
        },
        vc_ir::Expr::Gt(l, r) => Expr::If {
            cond: Box::new(Predicate::Compare {
                left: Box::new(convert_expr_from_vc(l)),
                op: CompareOp::Gt,
                right: Box::new(convert_expr_from_vc(r)),
            }),
            then_: Box::new(Expr::Bool(true)),
            else_: Box::new(Expr::Bool(false)),
        },
        vc_ir::Expr::Ge(l, r) => Expr::If {
            cond: Box::new(Predicate::Compare {
                left: Box::new(convert_expr_from_vc(l)),
                op: CompareOp::Ge,
                right: Box::new(convert_expr_from_vc(r)),
            }),
            then_: Box::new(Expr::Bool(true)),
            else_: Box::new(Expr::Bool(false)),
        },

        // Logical operations
        vc_ir::Expr::Not(e) => Expr::UnaryOp {
            op: UnaryOp::Not,
            arg: Box::new(convert_expr_from_vc(e)),
        },
        vc_ir::Expr::And(l, r) => Expr::If {
            cond: Box::new(Predicate::And(vec![
                expr_to_predicate(convert_expr_from_vc(l)),
                expr_to_predicate(convert_expr_from_vc(r)),
            ])),
            then_: Box::new(Expr::Bool(true)),
            else_: Box::new(Expr::Bool(false)),
        },
        vc_ir::Expr::Or(l, r) => Expr::If {
            cond: Box::new(Predicate::Or(vec![
                expr_to_predicate(convert_expr_from_vc(l)),
                expr_to_predicate(convert_expr_from_vc(r)),
            ])),
            then_: Box::new(Expr::Bool(true)),
            else_: Box::new(Expr::Bool(false)),
        },

        // Conditional
        vc_ir::Expr::Ite { cond, then_, else_ } => Expr::If {
            cond: Box::new(expr_to_predicate(convert_expr_from_vc(cond))),
            then_: Box::new(convert_expr_from_vc(then_)),
            else_: Box::new(convert_expr_from_vc(else_)),
        },

        // Collections
        vc_ir::Expr::ArrayIndex(arr, idx) => Expr::Apply {
            func: "index".to_string(),
            args: vec![convert_expr_from_vc(arr), convert_expr_from_vc(idx)],
        },
        vc_ir::Expr::ArrayLen(arr) => Expr::Apply {
            func: "len".to_string(),
            args: vec![convert_expr_from_vc(arr)],
        },
        vc_ir::Expr::ArraySlice { array, start, end } => Expr::Apply {
            func: "slice".to_string(),
            args: vec![
                convert_expr_from_vc(array),
                convert_expr_from_vc(start),
                convert_expr_from_vc(end),
            ],
        },
        vc_ir::Expr::TupleField(tuple, idx) => Expr::Project {
            tuple: Box::new(convert_expr_from_vc(tuple)),
            index: *idx,
        },
        vc_ir::Expr::StructField(base, field) => Expr::Apply {
            func: format!("field_{field}"),
            args: vec![convert_expr_from_vc(base)],
        },

        // Function application
        vc_ir::Expr::Apply { func, args } => Expr::Apply {
            func: func.clone(),
            args: args.iter().map(convert_expr_from_vc).collect(),
        },

        // Quantified expressions
        vc_ir::Expr::Forall { vars, body } => {
            // Quantified expressions in vc_ir return bool
            // Convert to a conditional that evaluates to true/false
            let body_pred = expr_to_predicate(convert_expr_from_vc(body));
            let pred = vars
                .iter()
                .rev()
                .fold(body_pred, |acc, (var, ty)| Predicate::ForAll {
                    var: var.clone(),
                    domain: Box::new(type_to_domain(ty)),
                    body: Box::new(acc),
                });
            Expr::If {
                cond: Box::new(pred),
                then_: Box::new(Expr::Bool(true)),
                else_: Box::new(Expr::Bool(false)),
            }
        }
        vc_ir::Expr::Exists { vars, body } => {
            let body_pred = expr_to_predicate(convert_expr_from_vc(body));
            let pred = vars
                .iter()
                .rev()
                .fold(body_pred, |acc, (var, ty)| Predicate::Exists {
                    var: var.clone(),
                    domain: Box::new(type_to_domain(ty)),
                    body: Box::new(acc),
                });
            Expr::If {
                cond: Box::new(pred),
                then_: Box::new(Expr::Bool(true)),
                else_: Box::new(Expr::Bool(false)),
            }
        }

        // Handle any other cases conservatively
        _ => Expr::Var("_unknown".to_string()),
    }
}

/// Helper to convert an expression to a predicate (for boolean contexts)
fn expr_to_predicate(expr: Expr) -> Predicate {
    match expr {
        Expr::Bool(b) => Predicate::Bool(b),
        Expr::Var(v) => Predicate::Var(v),
        other => Predicate::Compare {
            left: Box::new(other),
            op: CompareOp::Eq,
            right: Box::new(Expr::Bool(true)),
        },
    }
}

/// Build the initial state predicate
fn build_init_predicate(sm: &AsyncStateMachine) -> Predicate {
    let mut conjuncts = vec![];

    // State starts at initial
    conjuncts.push(Predicate::Compare {
        left: Box::new(Expr::Var("_state".to_string())),
        op: CompareOp::Eq,
        right: Box::new(Expr::Int(sm.initial as i64)),
    });

    // Add initial value constraints for captured variables
    for _cv in &sm.captured_variables {
        // Variables without explicit initial values are unconstrained
        // (could add type-based constraints here)
    }

    if conjuncts.len() == 1 {
        // SAFETY: We just checked len() == 1, so pop() returns Some
        conjuncts.pop().unwrap()
    } else {
        Predicate::And(conjuncts)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use vc_ir::temporal::AsyncStateMachine;

    #[test]
    fn test_convert_empty_sm() {
        let mut sm = AsyncStateMachine::new("empty");
        let end = sm.add_state("End", AsyncStateKind::End);
        sm.add_transition(0, end);

        let model = convert_to_tla2(&sm);
        assert_eq!(model.name, "empty");
        assert_eq!(model.transitions.len(), 1);
        assert_eq!(model.terminal_states.len(), 1);
    }

    #[test]
    fn test_convert_with_captured_vars() {
        let mut sm = AsyncStateMachine::new("with_vars");
        sm.captured_variables.push(CapturedVariable {
            name: "x".to_string(),
            ty: VcType::Int {
                signed: true,
                bits: 32,
            },
            live_across: vec![0],
            is_mutable: false,
        });

        let model = convert_to_tla2(&sm);
        // Should have x and _state
        assert_eq!(model.variables.len(), 2);
        assert_eq!(model.variables[0].name, "x");
        assert_eq!(model.variables[1].name, "_state");
    }

    #[test]
    fn test_convert_vc_type() {
        assert!(matches!(convert_vc_type(&VcType::Bool), VarType::Bool));
        assert!(matches!(
            convert_vc_type(&VcType::Int {
                signed: true,
                bits: 64
            }),
            VarType::Int {
                bits: 64,
                signed: true
            }
        ));
    }

    #[test]
    fn test_convert_predicate() {
        let pred = vc_ir::Predicate::Bool(true);
        let converted = convert_predicate_from_vc(&pred);
        assert!(matches!(converted, Predicate::Bool(true)));
    }

    #[test]
    fn test_convert_expr_var() {
        let expr = vc_ir::Expr::Var("x".to_string());
        let converted = convert_expr_from_vc(&expr);
        assert!(matches!(converted, Expr::Var(v) if v == "x"));
    }

    #[test]
    fn test_convert_expr_int() {
        let expr = vc_ir::Expr::IntLit(42);
        let converted = convert_expr_from_vc(&expr);
        assert!(matches!(converted, Expr::Int(42)));
    }

    #[test]
    fn test_convert_expr_add() {
        let expr = vc_ir::Expr::Add(
            Box::new(vc_ir::Expr::Var("x".to_string())),
            Box::new(vc_ir::Expr::IntLit(1)),
        );
        let converted = convert_expr_from_vc(&expr);
        assert!(matches!(converted, Expr::BinOp { op: BinOp::Add, .. }));
    }
}
