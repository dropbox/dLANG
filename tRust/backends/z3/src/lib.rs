//! Z3 SMT Solver Backend
//!
//! This crate provides real Z3 integration for tRust verification.
//! Z3 handles most verification conditions including:
//! - Arithmetic (linear and nonlinear, integer and real)
//! - Bitvectors
//! - Arrays
//! - Uninterpreted functions
//! - Quantifiers (with E-matching)

use std::collections::HashMap;
use vc_ir::{
    backend::ProofBackend, BackendCapabilities, Counterexample, Expr, Predicate, Theory, Value,
    VcKind, VcType, VerificationCondition, VerifyConfig, VerifyError, VerifyResult,
};
use z3::ast::Ast as Z3Ast;
use z3::{ast, with_z3_config, Config, Pattern, SatResult as Z3SatResult, Solver};

/// Check if a verification condition is valid using Z3
///
/// To prove P is valid, we check if NOT P is unsatisfiable.
/// Returns Proven if valid, Counterexample if invalid, Unknown if timeout.
#[must_use]
pub fn check_vc(vc: &VerificationCondition, _config: &VerifyConfig) -> VerifyResult {
    let cfg = Config::new();

    with_z3_config(&cfg, || {
        let solver = Solver::new();
        let mut vars: HashMap<String, ast::Dynamic> = HashMap::new();
        let mut scopes: Vec<HashMap<String, ast::Dynamic>> = Vec::new();

        let pred = match &vc.condition {
            VcKind::Predicate(p) => p.clone(),
            VcKind::Implies {
                antecedent,
                consequent,
            } => Predicate::Implies(Box::new(antecedent.clone()), Box::new(consequent.clone())),
            VcKind::Forall { vars, body } => {
                // For quantified VCs, create a forall predicate
                if let VcKind::Predicate(p) = body.as_ref() {
                    Predicate::Forall {
                        vars: vars
                            .iter()
                            .map(|v| (v.name.clone(), v.ty.clone()))
                            .collect(),
                        triggers: vec![],
                        body: Box::new(p.clone()),
                    }
                } else {
                    return VerifyResult::Unknown {
                        reason: "Nested quantified VCs not yet supported".to_string(),
                    };
                }
            }
            _ => {
                return VerifyResult::Error(VerifyError::Unsupported {
                    feature: format!("Z3 cannot handle {:?}", vc.condition),
                    suggestion: Some("Try a different backend".to_string()),
                });
            }
        };

        // Translate the predicate to Z3
        let z3_pred = translate_predicate(&pred, &mut vars, &mut scopes);

        // Assert the negation (to prove validity)
        let negated = z3_pred.not();
        solver.assert(&negated);

        // Check satisfiability
        match solver.check() {
            Z3SatResult::Unsat => {
                // NOT P is unsatisfiable, so P is valid
                VerifyResult::Proven
            }
            Z3SatResult::Sat => {
                // NOT P is satisfiable, so we have a counterexample
                let assignments = extract_counterexample(&solver, &vars);
                VerifyResult::Counterexample(Counterexample {
                    vc_id: vc.id,
                    assignments,
                    trace: None,
                    explanation: format!("Counterexample found for '{}'", vc.name),
                })
            }
            Z3SatResult::Unknown => VerifyResult::Unknown {
                reason: solver
                    .get_reason_unknown()
                    .unwrap_or_else(|| "solver returned unknown".to_string()),
            },
        }
    })
}

/// Translate a predicate to Z3 Bool ast
fn translate_predicate(
    pred: &Predicate,
    vars: &mut HashMap<String, ast::Dynamic>,
    scopes: &mut Vec<HashMap<String, ast::Dynamic>>,
) -> ast::Bool {
    match pred {
        Predicate::Bool(b) => ast::Bool::from_bool(*b),
        Predicate::Expr(e) => translate_expr_to_bool(e, vars, scopes),
        Predicate::Not(p) => translate_predicate(p, vars, scopes).not(),
        Predicate::And(ps) => {
            let translated: Vec<ast::Bool> = ps
                .iter()
                .map(|p| translate_predicate(p, vars, scopes))
                .collect();
            let refs: Vec<&ast::Bool> = translated.iter().collect();
            if refs.is_empty() {
                ast::Bool::from_bool(true)
            } else {
                ast::Bool::and(&refs)
            }
        }
        Predicate::Or(ps) => {
            let translated: Vec<ast::Bool> = ps
                .iter()
                .map(|p| translate_predicate(p, vars, scopes))
                .collect();
            let refs: Vec<&ast::Bool> = translated.iter().collect();
            if refs.is_empty() {
                ast::Bool::from_bool(false)
            } else {
                ast::Bool::or(&refs)
            }
        }
        Predicate::Implies(a, b) => {
            let a_z3 = translate_predicate(a, vars, scopes);
            let b_z3 = translate_predicate(b, vars, scopes);
            a_z3.implies(&b_z3)
        }
        Predicate::Iff(a, b) => {
            let a_z3 = translate_predicate(a, vars, scopes);
            let b_z3 = translate_predicate(b, vars, scopes);
            a_z3.iff(&b_z3)
        }
        Predicate::Forall {
            vars: bound_vars,
            triggers,
            body,
        } => {
            let (bound_consts, bound_scope) = mk_bound_scope(bound_vars);
            scopes.push(bound_scope);
            let patterns = mk_patterns(triggers, vars, scopes);
            let body_z3 = translate_predicate(body, vars, scopes);
            scopes.pop();
            let pattern_refs: Vec<&Pattern> = patterns.iter().collect();
            let bound_refs: Vec<&dyn Z3Ast> =
                bound_consts.iter().map(|c| c as &dyn Z3Ast).collect();
            ast::forall_const(&bound_refs, &pattern_refs, &body_z3)
        }
        Predicate::Exists {
            vars: bound_vars,
            body,
        } => {
            let (bound_consts, bound_scope) = mk_bound_scope(bound_vars);
            scopes.push(bound_scope);
            let body_z3 = translate_predicate(body, vars, scopes);
            scopes.pop();

            let bound_refs: Vec<&dyn Z3Ast> =
                bound_consts.iter().map(|c| c as &dyn Z3Ast).collect();
            ast::exists_const(&bound_refs, &[], &body_z3)
        }
        Predicate::Let { bindings, body } => {
            scopes.push(HashMap::new());
            for (name, expr) in bindings {
                let term = translate_expr_to_dynamic(expr, vars, scopes);
                scopes
                    .last_mut()
                    .expect("scopes just pushed")
                    .insert(name.clone(), term);
            }
            let result = translate_predicate(body, vars, scopes);
            scopes.pop();
            result
        }
    }
}

/// Translate an expression to Z3 Float ast
fn translate_expr_to_float(
    expr: &Expr,
    vars: &mut HashMap<String, ast::Dynamic>,
    scopes: &mut Vec<HashMap<String, ast::Dynamic>>,
) -> ast::Float {
    // Get default rounding mode (round to nearest, ties to even)
    let rm = ast::RoundingMode::round_nearest_ties_to_even();

    match expr {
        Expr::FloatLit(f) => ast::Float::from_f64(*f),
        Expr::Var(name) => {
            if let Some(var) = lookup_scoped_var(name, scopes) {
                if let Some(float_var) = var.as_float() {
                    return float_var;
                }
            }
            let var = get_or_create_var(name, &VcType::Float { bits: 64 }, vars);
            var.as_float()
                .unwrap_or_else(|| ast::Float::new_const_double(name.as_str()))
        }
        Expr::Result => {
            let var = get_or_create_var("__result", &VcType::Float { bits: 64 }, vars);
            var.as_float()
                .unwrap_or_else(|| ast::Float::new_const_double("__result"))
        }
        Expr::Add(a, b) => {
            let a_z3 = translate_expr_to_float(a, vars, scopes);
            let b_z3 = translate_expr_to_float(b, vars, scopes);
            a_z3.add_with_rounding_mode(b_z3, &rm)
        }
        Expr::Sub(a, b) => {
            let a_z3 = translate_expr_to_float(a, vars, scopes);
            let b_z3 = translate_expr_to_float(b, vars, scopes);
            a_z3.sub_with_rounding_mode(b_z3, &rm)
        }
        Expr::Mul(a, b) => {
            let a_z3 = translate_expr_to_float(a, vars, scopes);
            let b_z3 = translate_expr_to_float(b, vars, scopes);
            a_z3.mul_with_rounding_mode(b_z3, &rm)
        }
        Expr::Div(a, b) => {
            let a_z3 = translate_expr_to_float(a, vars, scopes);
            let b_z3 = translate_expr_to_float(b, vars, scopes);
            a_z3.div_with_rounding_mode(b_z3, &rm)
        }
        Expr::Neg(a) => {
            let a_z3 = translate_expr_to_float(a, vars, scopes);
            a_z3.unary_neg()
        }
        Expr::Abs(a) => {
            let a_z3 = translate_expr_to_float(a, vars, scopes);
            a_z3.unary_abs()
        }
        Expr::Ite { cond, then_, else_ } => {
            let cond_z3 = translate_expr_to_bool(cond, vars, scopes);
            let then_z3 = translate_expr_to_float(then_, vars, scopes);
            let else_z3 = translate_expr_to_float(else_, vars, scopes);
            cond_z3.ite(&then_z3, &else_z3)
        }
        // For integer literals in float context, convert to float
        Expr::IntLit(i) => ast::Float::from_f64(*i as f64),
        // Fallback: panic for unsupported float expressions
        other => panic!(
            "Z3 backend: translate_expr_to_float cannot handle {other:?} - expected float-valued expression"
        ),
    }
}

/// Check if an expression involves floating-point values
fn expr_involves_float(expr: &Expr) -> bool {
    match expr {
        Expr::FloatLit(_) => true,
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) => {
            expr_involves_float(a) || expr_involves_float(b)
        }
        Expr::Neg(e) | Expr::Abs(e) => expr_involves_float(e),
        Expr::Ite {
            cond: _,
            then_,
            else_,
        } => expr_involves_float(then_) || expr_involves_float(else_),
        _ => false,
    }
}

/// Translate an expression to Z3 Int ast
fn translate_expr(
    expr: &Expr,
    vars: &mut HashMap<String, ast::Dynamic>,
    scopes: &mut Vec<HashMap<String, ast::Dynamic>>,
) -> ast::Int {
    match expr {
        Expr::IntLit(i) => ast::Int::from_i64(*i as i64),
        Expr::Var(name) => {
            if let Some(var) = lookup_scoped_var(name, scopes) {
                if let Some(int_var) = var.as_int() {
                    return int_var;
                }
            }

            let var = get_or_create_var(
                name,
                &VcType::Int {
                    signed: true,
                    bits: 32,
                },
                vars,
            );
            var.as_int()
                .unwrap_or_else(|| ast::Int::new_const(name.as_str()))
        }
        Expr::Result => {
            let var = get_or_create_var(
                "__result",
                &VcType::Int {
                    signed: true,
                    bits: 32,
                },
                vars,
            );
            var.as_int()
                .unwrap_or_else(|| ast::Int::new_const("__result"))
        }
        Expr::Old(e) => {
            let name = format!("__old_{e:?}");
            let var = get_or_create_var(
                &name,
                &VcType::Int {
                    signed: true,
                    bits: 32,
                },
                vars,
            );
            var.as_int()
                .unwrap_or_else(|| ast::Int::new_const(name.as_str()))
        }
        Expr::Add(a, b) => {
            let a_z3 = translate_expr(a, vars, scopes);
            let b_z3 = translate_expr(b, vars, scopes);
            ast::Int::add(&[&a_z3, &b_z3])
        }
        Expr::Sub(a, b) => {
            let a_z3 = translate_expr(a, vars, scopes);
            let b_z3 = translate_expr(b, vars, scopes);
            ast::Int::sub(&[&a_z3, &b_z3])
        }
        Expr::Mul(a, b) => {
            let a_z3 = translate_expr(a, vars, scopes);
            let b_z3 = translate_expr(b, vars, scopes);
            ast::Int::mul(&[&a_z3, &b_z3])
        }
        Expr::Div(a, b) => {
            let a_z3 = translate_expr(a, vars, scopes);
            let b_z3 = translate_expr(b, vars, scopes);
            a_z3.div(&b_z3)
        }
        Expr::Neg(a) => {
            let a_z3 = translate_expr(a, vars, scopes);
            a_z3.unary_minus()
        }
        Expr::Ite { cond, then_, else_ } => {
            let cond_z3 = translate_expr_to_bool(cond, vars, scopes);
            let then_z3 = translate_expr(then_, vars, scopes);
            let else_z3 = translate_expr(else_, vars, scopes);
            cond_z3.ite(&then_z3, &else_z3)
        }
        Expr::Rem(a, b) => {
            let a_z3 = translate_expr(a, vars, scopes);
            let b_z3 = translate_expr(b, vars, scopes);
            a_z3.rem(&b_z3)
        }
        Expr::Abs(a) => {
            // abs(x) = if x < 0 then -x else x
            let a_z3 = translate_expr(a, vars, scopes);
            let zero = ast::Int::from_i64(0);
            let neg = a_z3.unary_minus();
            a_z3.lt(&zero).ite(&neg, &a_z3)
        }
        Expr::Min(a, b) => {
            // min(a, b) = if a < b then a else b
            let a_z3 = translate_expr(a, vars, scopes);
            let b_z3 = translate_expr(b, vars, scopes);
            a_z3.lt(&b_z3).ite(&a_z3, &b_z3)
        }
        Expr::Max(a, b) => {
            // max(a, b) = if a > b then a else b
            let a_z3 = translate_expr(a, vars, scopes);
            let b_z3 = translate_expr(b, vars, scopes);
            a_z3.gt(&b_z3).ite(&a_z3, &b_z3)
        }
        // Struct field access - encode as flattened variable name
        Expr::StructField(base, field) => {
            // Flatten to variable like "base__field_name"
            let base_name = expr_to_var_name(base);
            let name = format!("{base_name}__field_{field}");
            let var = get_or_create_var(
                &name,
                &VcType::Int {
                    signed: true,
                    bits: 32,
                },
                vars,
            );
            var.as_int()
                .unwrap_or_else(|| ast::Int::new_const(name.as_str()))
        }
        Expr::TupleField(base, idx) => {
            // Flatten to variable like "base__field_0"
            let base_name = expr_to_var_name(base);
            let name = format!("{base_name}__field_{idx}");
            let var = get_or_create_var(
                &name,
                &VcType::Int {
                    signed: true,
                    bits: 32,
                },
                vars,
            );
            var.as_int()
                .unwrap_or_else(|| ast::Int::new_const(name.as_str()))
        }
        // Array index - encode as uninterpreted function
        Expr::ArrayIndex(arr, idx) => {
            let arr_name = expr_to_var_name(arr);
            let idx_z3 = translate_expr(idx, vars, scopes);
            // Encode as select function on array
            let name = format!("{arr_name}__select_{idx_z3}");
            ast::Int::new_const(name.as_str())
        }
        // Array length - encode as property
        Expr::ArrayLen(arr) => {
            let arr_name = expr_to_var_name(arr);
            let name = format!("{arr_name}__len");
            let var = get_or_create_var(
                &name,
                &VcType::Int {
                    signed: false,
                    bits: 64,
                },
                vars,
            );
            var.as_int()
                .unwrap_or_else(|| ast::Int::new_const(name.as_str()))
        }
        // Cast - treat as identity for integers
        Expr::Cast { expr, .. } => translate_expr(expr, vars, scopes),
        // Deref - treat as variable lookup
        Expr::Deref(e) => {
            let base_name = expr_to_var_name(e);
            let name = format!("{base_name}__deref");
            let var = get_or_create_var(
                &name,
                &VcType::Int {
                    signed: true,
                    bits: 32,
                },
                vars,
            );
            var.as_int()
                .unwrap_or_else(|| ast::Int::new_const(name.as_str()))
        }
        // AddrOf - treat as variable
        Expr::AddrOf(e) => {
            let base_name = expr_to_var_name(e);
            let name = format!("{base_name}__addr");
            let var = get_or_create_var(
                &name,
                &VcType::Int {
                    signed: false,
                    bits: 64,
                },
                vars,
            );
            var.as_int()
                .unwrap_or_else(|| ast::Int::new_const(name.as_str()))
        }
        // Function application - encode as uninterpreted function
        Expr::Apply { func, args } => {
            let args_str: Vec<String> = args.iter().map(expr_to_var_name).collect();
            let name = format!("{}_{}", func, args_str.join("_"));
            let var = get_or_create_var(
                &name,
                &VcType::Int {
                    signed: true,
                    bits: 32,
                },
                vars,
            );
            var.as_int()
                .unwrap_or_else(|| ast::Int::new_const(name.as_str()))
        }
        // Unhandled expression types - fail explicitly rather than silently returning 0
        other => panic!(
            "Z3 backend: translate_expr cannot handle {other:?} - expected integer-valued expression"
        ),
    }
}

/// Translate an expression that should yield a boolean
fn translate_expr_to_bool(
    expr: &Expr,
    vars: &mut HashMap<String, ast::Dynamic>,
    scopes: &mut Vec<HashMap<String, ast::Dynamic>>,
) -> ast::Bool {
    match expr {
        Expr::BoolLit(b) => ast::Bool::from_bool(*b),
        Expr::Var(name) => {
            if let Some(var) = lookup_scoped_var(name, scopes) {
                if let Some(bool_var) = var.as_bool() {
                    return bool_var;
                }
            }

            let var = get_or_create_var(name, &VcType::Bool, vars);
            var.as_bool()
                .unwrap_or_else(|| ast::Bool::new_const(name.as_str()))
        }
        Expr::Eq(a, b) => {
            if expr_involves_float(a) || expr_involves_float(b) {
                let a_z3 = translate_expr_to_float(a, vars, scopes);
                let b_z3 = translate_expr_to_float(b, vars, scopes);
                a_z3.eq(&b_z3)
            } else {
                let a_z3 = translate_expr(a, vars, scopes);
                let b_z3 = translate_expr(b, vars, scopes);
                a_z3.eq(&b_z3)
            }
        }
        Expr::Lt(a, b) => {
            if expr_involves_float(a) || expr_involves_float(b) {
                let a_z3 = translate_expr_to_float(a, vars, scopes);
                let b_z3 = translate_expr_to_float(b, vars, scopes);
                a_z3.lt(&b_z3)
            } else {
                let a_z3 = translate_expr(a, vars, scopes);
                let b_z3 = translate_expr(b, vars, scopes);
                a_z3.lt(&b_z3)
            }
        }
        Expr::Le(a, b) => {
            if expr_involves_float(a) || expr_involves_float(b) {
                let a_z3 = translate_expr_to_float(a, vars, scopes);
                let b_z3 = translate_expr_to_float(b, vars, scopes);
                a_z3.le(&b_z3)
            } else {
                let a_z3 = translate_expr(a, vars, scopes);
                let b_z3 = translate_expr(b, vars, scopes);
                a_z3.le(&b_z3)
            }
        }
        Expr::Gt(a, b) => {
            if expr_involves_float(a) || expr_involves_float(b) {
                let a_z3 = translate_expr_to_float(a, vars, scopes);
                let b_z3 = translate_expr_to_float(b, vars, scopes);
                a_z3.gt(&b_z3)
            } else {
                let a_z3 = translate_expr(a, vars, scopes);
                let b_z3 = translate_expr(b, vars, scopes);
                a_z3.gt(&b_z3)
            }
        }
        Expr::Ge(a, b) => {
            if expr_involves_float(a) || expr_involves_float(b) {
                let a_z3 = translate_expr_to_float(a, vars, scopes);
                let b_z3 = translate_expr_to_float(b, vars, scopes);
                a_z3.ge(&b_z3)
            } else {
                let a_z3 = translate_expr(a, vars, scopes);
                let b_z3 = translate_expr(b, vars, scopes);
                a_z3.ge(&b_z3)
            }
        }
        Expr::And(a, b) => {
            let a_z3 = translate_expr_to_bool(a, vars, scopes);
            let b_z3 = translate_expr_to_bool(b, vars, scopes);
            ast::Bool::and(&[&a_z3, &b_z3])
        }
        Expr::Or(a, b) => {
            let a_z3 = translate_expr_to_bool(a, vars, scopes);
            let b_z3 = translate_expr_to_bool(b, vars, scopes);
            ast::Bool::or(&[&a_z3, &b_z3])
        }
        Expr::Not(e) => {
            let e_z3 = translate_expr_to_bool(e, vars, scopes);
            e_z3.not()
        }
        // Note: Expr doesn't have Implies variant - it's converted to Or(Not(a), b) by the implies method
        Expr::Ite { cond, then_, else_ } => {
            let cond_z3 = translate_expr_to_bool(cond, vars, scopes);
            let then_z3 = translate_expr_to_bool(then_, vars, scopes);
            let else_z3 = translate_expr_to_bool(else_, vars, scopes);
            cond_z3.ite(&then_z3, &else_z3)
        }
        Expr::Ne(a, b) => {
            if expr_involves_float(a) || expr_involves_float(b) {
                let a_z3 = translate_expr_to_float(a, vars, scopes);
                let b_z3 = translate_expr_to_float(b, vars, scopes);
                a_z3.eq(&b_z3).not()
            } else {
                let a_z3 = translate_expr(a, vars, scopes);
                let b_z3 = translate_expr(b, vars, scopes);
                a_z3.eq(&b_z3).not()
            }
        }
        Expr::Forall { vars: bound_vars, body } => {
            let (bound_consts, bound_scope) = mk_bound_scope(bound_vars);
            scopes.push(bound_scope);
            let body_z3 = translate_expr_to_bool(body, vars, scopes);
            scopes.pop();
            let bound_refs: Vec<&dyn Z3Ast> = bound_consts.iter().map(|c| c as &dyn Z3Ast).collect();
            ast::forall_const(&bound_refs, &[], &body_z3)
        }
        Expr::Exists { vars: bound_vars, body } => {
            let (bound_consts, bound_scope) = mk_bound_scope(bound_vars);
            scopes.push(bound_scope);
            let body_z3 = translate_expr_to_bool(body, vars, scopes);
            scopes.pop();
            let bound_refs: Vec<&dyn Z3Ast> = bound_consts.iter().map(|c| c as &dyn Z3Ast).collect();
            ast::exists_const(&bound_refs, &[], &body_z3)
        }
        // Struct field access - might be boolean type
        Expr::StructField(base, field) => {
            let base_name = expr_to_var_name(base);
            let name = format!("{base_name}__field_{field}");
            let var = get_or_create_var(&name, &VcType::Bool, vars);
            var.as_bool()
                .unwrap_or_else(|| ast::Bool::new_const(name.as_str()))
        }
        Expr::TupleField(base, idx) => {
            let base_name = expr_to_var_name(base);
            let name = format!("{base_name}__field_{idx}");
            let var = get_or_create_var(&name, &VcType::Bool, vars);
            var.as_bool()
                .unwrap_or_else(|| ast::Bool::new_const(name.as_str()))
        }
        // Cast to bool
        Expr::Cast { expr, .. } => translate_expr_to_bool(expr, vars, scopes),
        // Unhandled expression types - fail explicitly rather than silently returning true
        other => panic!(
            "Z3 backend: translate_expr_to_bool cannot handle {other:?} - expected boolean-valued expression"
        ),
    }
}

fn translate_expr_to_dynamic(
    expr: &Expr,
    vars: &mut HashMap<String, ast::Dynamic>,
    scopes: &mut Vec<HashMap<String, ast::Dynamic>>,
) -> ast::Dynamic {
    match expr {
        Expr::BoolLit(_)
        | Expr::And(_, _)
        | Expr::Or(_, _)
        | Expr::Not(_)
        | Expr::Eq(_, _)
        | Expr::Ne(_, _)
        | Expr::Lt(_, _)
        | Expr::Le(_, _)
        | Expr::Gt(_, _)
        | Expr::Ge(_, _)
        | Expr::Forall { .. }
        | Expr::Exists { .. } => translate_expr_to_bool(expr, vars, scopes).into(),
        _ => translate_expr(expr, vars, scopes).into(),
    }
}

fn lookup_scoped_var(name: &str, scopes: &[HashMap<String, ast::Dynamic>]) -> Option<ast::Dynamic> {
    scopes
        .iter()
        .rev()
        .find_map(|scope| scope.get(name).cloned())
}

fn mk_patterns(
    triggers: &[Vec<Expr>],
    vars: &mut HashMap<String, ast::Dynamic>,
    scopes: &mut Vec<HashMap<String, ast::Dynamic>>,
) -> Vec<Pattern> {
    triggers
        .iter()
        .map(|terms| {
            let translated: Vec<ast::Dynamic> = terms
                .iter()
                .map(|e| translate_expr_to_dynamic(e, vars, scopes))
                .collect();
            let term_refs: Vec<&dyn Z3Ast> = translated.iter().map(|t| t as &dyn Z3Ast).collect();
            Pattern::new(&term_refs)
        })
        .collect()
}

fn mk_bound_scope(
    bound_vars: &[(String, VcType)],
) -> (Vec<ast::Dynamic>, HashMap<String, ast::Dynamic>) {
    let mut bound_consts = Vec::with_capacity(bound_vars.len());
    let mut scope = HashMap::new();

    for (name, ty) in bound_vars {
        let constant = mk_const_for_type(name, ty);
        scope.insert(name.clone(), constant.clone());
        bound_consts.push(constant);
    }

    (bound_consts, scope)
}

fn mk_const_for_type(name: &str, ty: &VcType) -> ast::Dynamic {
    match ty {
        VcType::Bool => ast::Bool::new_const(name).into(),
        VcType::Float { bits: 32 } => ast::Float::new_const_float32(name).into(),
        VcType::Float { bits: 64 } | VcType::Float { .. } => {
            ast::Float::new_const_double(name).into()
        }
        VcType::BitVec { bits } => ast::BV::new_const(name, *bits).into(),
        // Int and all other types (Unit, Ref, Array, Struct, Tuple, etc.) default to Int
        _ => ast::Int::new_const(name).into(),
    }
}

/// Convert an expression to a variable name for flattening compound expressions
fn expr_to_var_name(expr: &Expr) -> String {
    match expr {
        Expr::Var(name) => name.clone(),
        Expr::Result => "__result".to_string(),
        Expr::Old(e) => format!("__old_{}", expr_to_var_name(e)),
        Expr::StructField(base, field) => {
            format!("{}__field_{}", expr_to_var_name(base), field)
        }
        Expr::TupleField(base, idx) => {
            format!("{}__field_{}", expr_to_var_name(base), idx)
        }
        Expr::Deref(e) => format!("{}__deref", expr_to_var_name(e)),
        Expr::AddrOf(e) => format!("{}__addr", expr_to_var_name(e)),
        Expr::ArrayIndex(arr, idx) => {
            format!("{}__idx_{}", expr_to_var_name(arr), expr_to_var_name(idx))
        }
        Expr::ArrayLen(arr) => format!("{}__len", expr_to_var_name(arr)),
        Expr::IntLit(i) => format!("lit_{i}"),
        Expr::BoolLit(b) => format!("lit_{b}"),
        // For complex expressions, use a placeholder
        other => format!("expr_{other:p}"),
    }
}

/// Get or create a variable
fn get_or_create_var(
    name: &str,
    ty: &VcType,
    vars: &mut HashMap<String, ast::Dynamic>,
) -> ast::Dynamic {
    if let Some(var) = vars.get(name) {
        return var.clone();
    }

    let var = mk_const_for_type(name, ty);

    vars.insert(name.to_string(), var.clone());
    var
}

/// Extract counterexample from Z3 model
fn extract_counterexample(
    solver: &Solver,
    vars: &HashMap<String, ast::Dynamic>,
) -> Vec<(String, Value)> {
    let mut assignments = Vec::new();

    if let Some(model) = solver.get_model() {
        for (name, var) in vars {
            if let Some(int_var) = var.as_int() {
                if let Some(val) = model.eval(&int_var, true) {
                    if let Some(i) = val.as_i64() {
                        assignments.push((name.clone(), Value::Int(i128::from(i))));
                    }
                }
            } else if let Some(bool_var) = var.as_bool() {
                if let Some(val) = model.eval(&bool_var, true) {
                    if let Some(b) = val.as_bool() {
                        assignments.push((name.clone(), Value::Bool(b)));
                    }
                }
            } else if let Some(float_var) = var.as_float() {
                if let Some(val) = model.eval(&float_var, true) {
                    let f = val.as_f64();
                    assignments.push((name.clone(), Value::Float(f)));
                }
            } else if let Some(real_var) = var.as_real() {
                if let Some(val) = model.eval(&real_var, true) {
                    if let Some((num, den)) = val.as_rational() {
                        assignments.push((name.clone(), Value::Float(num as f64 / den as f64)));
                    }
                }
            }
        }
    }

    assignments
}

/// Z3 backend that implements ProofBackend trait
pub struct Z3Backend;

impl Z3Backend {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }
}

impl Default for Z3Backend {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofBackend for Z3Backend {
    fn name(&self) -> &'static str {
        "z3"
    }

    fn capabilities(&self) -> BackendCapabilities {
        BackendCapabilities {
            predicates: true,
            quantifiers: true,
            theories: vec![
                Theory::Core,
                Theory::LIA,
                Theory::LRA,
                Theory::NIA,
                Theory::NRA,
                Theory::BV,
                Theory::Arrays,
                Theory::UF,
                Theory::FP,
            ],
            temporal: false,
            separation: false,
            neural_network: false,
            bounded_model_check: false,
            induction: false,
            incremental: true,
            counterexamples: true,
            proof_production: true,
        }
    }

    fn check(&self, vc: &VerificationCondition, config: &VerifyConfig) -> VerifyResult {
        check_vc(vc, config)
    }

    fn counterexample(&self, _vc: &VerificationCondition) -> Option<Counterexample> {
        None // Would need to store state to implement
    }

    fn reset(&mut self) {
        // Nothing to reset in stateless backend
    }

    fn push(&mut self) {
        // Would need stateful implementation
    }

    fn pop(&mut self) {
        // Would need stateful implementation
    }

    fn assume(&mut self, _pred: &Predicate) {
        // Would need stateful implementation
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use vc_ir::{SourceSpan, VcId};

    fn default_config() -> VerifyConfig {
        VerifyConfig::default()
    }

    // ============================================
    // Basic Z3 functionality tests
    // ============================================

    #[test]
    fn test_z3_capabilities() {
        let backend = Z3Backend::new();
        let caps = backend.capabilities();
        assert!(caps.predicates);
        assert!(caps.quantifiers);
        assert!(caps.theories.contains(&Theory::LIA));
        assert!(caps.counterexamples);
    }

    #[test]
    fn test_prove_true() {
        let vc = VerificationCondition {
            id: VcId(1),
            name: "true_is_valid".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Bool(true)),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_disprove_false() {
        let vc = VerificationCondition {
            id: VcId(2),
            name: "false_is_invalid".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Bool(false)),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Counterexample(_)));
    }

    // ============================================
    // Arithmetic tests
    // ============================================

    #[test]
    fn test_simple_arithmetic() {
        // x > 0 implies x >= 1 (for integers)
        let vc = VerificationCondition {
            id: VcId(3),
            name: "x_gt_0_implies_ge_1".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::Expr(Expr::Gt(
                    Box::new(Expr::var("x")),
                    Box::new(Expr::int(0)),
                )),
                consequent: Predicate::Expr(Expr::Ge(
                    Box::new(Expr::var("x")),
                    Box::new(Expr::int(1)),
                )),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_arithmetic_counterexample() {
        // x > 0 implies x > 5 - should fail with counterexample like x=1
        let vc = VerificationCondition {
            id: VcId(4),
            name: "x_gt_0_not_implies_gt_5".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::Expr(Expr::Gt(
                    Box::new(Expr::var("x")),
                    Box::new(Expr::int(0)),
                )),
                consequent: Predicate::Expr(Expr::Gt(
                    Box::new(Expr::var("x")),
                    Box::new(Expr::int(5)),
                )),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        match result {
            VerifyResult::Counterexample(cex) => {
                // Should have a counterexample where x is in (0, 5]
                assert!(!cex.assignments.is_empty());
            }
            _ => panic!("Expected counterexample, got {result:?}"),
        }
    }

    #[test]
    fn test_addition_commutative() {
        // x + y = y + x (commutativity)
        let vc = VerificationCondition {
            id: VcId(5),
            name: "addition_commutative".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(Expr::Add(
                    Box::new(Expr::var("x")),
                    Box::new(Expr::var("y")),
                )),
                Box::new(Expr::Add(
                    Box::new(Expr::var("y")),
                    Box::new(Expr::var("x")),
                )),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_multiplication_by_zero() {
        // x * 0 = 0
        let vc = VerificationCondition {
            id: VcId(6),
            name: "mul_by_zero".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(Expr::Mul(Box::new(Expr::var("x")), Box::new(Expr::int(0)))),
                Box::new(Expr::int(0)),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    // ============================================
    // Logical operations tests
    // ============================================

    #[test]
    fn test_and_elimination() {
        // P and Q implies P
        let vc = VerificationCondition {
            id: VcId(7),
            name: "and_elimination".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::And(vec![
                    Predicate::Expr(Expr::var("p")),
                    Predicate::Expr(Expr::var("q")),
                ]),
                consequent: Predicate::Expr(Expr::var("p")),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_or_introduction() {
        // P implies P or Q
        let vc = VerificationCondition {
            id: VcId(8),
            name: "or_introduction".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::Expr(Expr::var("p")),
                consequent: Predicate::Or(vec![
                    Predicate::Expr(Expr::var("p")),
                    Predicate::Expr(Expr::var("q")),
                ]),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_double_negation() {
        // not(not(P)) iff P
        let vc = VerificationCondition {
            id: VcId(9),
            name: "double_negation".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Iff(
                Box::new(Predicate::Not(Box::new(Predicate::Not(Box::new(
                    Predicate::Expr(Expr::var("p")),
                ))))),
                Box::new(Predicate::Expr(Expr::var("p"))),
            )),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_modus_ponens() {
        // (P and (P implies Q)) implies Q
        let vc = VerificationCondition {
            id: VcId(10),
            name: "modus_ponens".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::And(vec![
                    Predicate::Expr(Expr::var("p")),
                    Predicate::Implies(
                        Box::new(Predicate::Expr(Expr::var("p"))),
                        Box::new(Predicate::Expr(Expr::var("q"))),
                    ),
                ]),
                consequent: Predicate::Expr(Expr::var("q")),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    // ============================================
    // Quantifier semantics tests
    // ============================================

    #[test]
    fn test_forall_in_antecedent_is_not_treated_as_free_var() {
        // (forall x. x > 0) implies false is valid, because (forall x. x > 0) is false.
        // If `forall` is incorrectly erased and `x` is treated as a free existential,
        // this becomes (x > 0) implies false, which is not valid.
        let vc = VerificationCondition {
            id: VcId(11),
            name: "forall_in_antecedent".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::Forall {
                    vars: vec![(
                        "x".to_string(),
                        VcType::Int {
                            signed: true,
                            bits: 32,
                        },
                    )],
                    triggers: vec![],
                    body: Box::new(Predicate::Expr(Expr::Gt(
                        Box::new(Expr::var("x")),
                        Box::new(Expr::int(0)),
                    ))),
                },
                consequent: Predicate::Bool(false),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(
            matches!(result, VerifyResult::Proven),
            "forall quantifier must be preserved under implication antecedents"
        );
    }

    // ============================================
    // Hello Verified World test - clamp_positive
    // ============================================

    #[test]
    fn test_clamp_positive_postcondition_1() {
        // For clamp_positive(n, val): result >= 1 when n > 0
        // The function returns: if val < 1 { 1 } else if val > n { n } else { val }
        // All branches return >= 1 when n > 0

        let result_expr = Expr::Ite {
            cond: Box::new(Expr::Lt(Box::new(Expr::var("val")), Box::new(Expr::int(1)))),
            then_: Box::new(Expr::int(1)),
            else_: Box::new(Expr::Ite {
                cond: Box::new(Expr::Gt(
                    Box::new(Expr::var("val")),
                    Box::new(Expr::var("n")),
                )),
                then_: Box::new(Expr::var("n")),
                else_: Box::new(Expr::var("val")),
            }),
        };

        let vc = VerificationCondition {
            id: VcId(100),
            name: "clamp_positive_postcond_1".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::Expr(Expr::Gt(
                    Box::new(Expr::var("n")),
                    Box::new(Expr::int(0)),
                )),
                consequent: Predicate::Expr(Expr::Ge(
                    Box::new(result_expr),
                    Box::new(Expr::int(1)),
                )),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(
            matches!(result, VerifyResult::Proven),
            "clamp_positive postcondition 'result >= 1' should be proven"
        );
    }

    #[test]
    fn test_clamp_positive_postcondition_2() {
        // For clamp_positive(n, val): result <= n when n >= 1
        // The function returns: if val < 1 { 1 } else if val > n { n } else { val }

        let result_expr = Expr::Ite {
            cond: Box::new(Expr::Lt(Box::new(Expr::var("val")), Box::new(Expr::int(1)))),
            then_: Box::new(Expr::int(1)),
            else_: Box::new(Expr::Ite {
                cond: Box::new(Expr::Gt(
                    Box::new(Expr::var("val")),
                    Box::new(Expr::var("n")),
                )),
                then_: Box::new(Expr::var("n")),
                else_: Box::new(Expr::var("val")),
            }),
        };

        // Need n >= 1 for the first branch (returning 1) to satisfy result <= n
        let vc = VerificationCondition {
            id: VcId(101),
            name: "clamp_positive_postcond_2".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::Expr(Expr::Ge(
                    Box::new(Expr::var("n")),
                    Box::new(Expr::int(1)),
                )),
                consequent: Predicate::Expr(Expr::Le(
                    Box::new(result_expr),
                    Box::new(Expr::var("n")),
                )),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(
            matches!(result, VerifyResult::Proven),
            "clamp_positive postcondition 'result <= n' should be proven"
        );
    }

    // ============================================
    // Expression coverage tests (new in #449)
    // ============================================

    #[test]
    fn test_not_equal() {
        // x != y implies not (x = y)
        let vc = VerificationCondition {
            id: VcId(200),
            name: "not_equal_iff_not_eq".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Iff(
                Box::new(Predicate::Expr(Expr::Ne(
                    Box::new(Expr::var("x")),
                    Box::new(Expr::var("y")),
                ))),
                Box::new(Predicate::Not(Box::new(Predicate::Expr(Expr::Eq(
                    Box::new(Expr::var("x")),
                    Box::new(Expr::var("y")),
                ))))),
            )),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_remainder() {
        // x % 2 = 0 or x % 2 = 1 (for non-negative x)
        let vc = VerificationCondition {
            id: VcId(201),
            name: "remainder_mod_2".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::Expr(Expr::Ge(
                    Box::new(Expr::var("x")),
                    Box::new(Expr::int(0)),
                )),
                consequent: Predicate::Or(vec![
                    Predicate::Expr(Expr::Eq(
                        Box::new(Expr::Rem(Box::new(Expr::var("x")), Box::new(Expr::int(2)))),
                        Box::new(Expr::int(0)),
                    )),
                    Predicate::Expr(Expr::Eq(
                        Box::new(Expr::Rem(Box::new(Expr::var("x")), Box::new(Expr::int(2)))),
                        Box::new(Expr::int(1)),
                    )),
                ]),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_abs_non_negative() {
        // abs(x) >= 0 for all x
        let vc = VerificationCondition {
            id: VcId(202),
            name: "abs_non_negative".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Ge(
                Box::new(Expr::Abs(Box::new(Expr::var("x")))),
                Box::new(Expr::int(0)),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_min_le_both() {
        // min(x, y) <= x and min(x, y) <= y
        let min_xy = Expr::Min(Box::new(Expr::var("x")), Box::new(Expr::var("y")));
        let vc = VerificationCondition {
            id: VcId(203),
            name: "min_le_both".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::And(vec![
                Predicate::Expr(Expr::Le(Box::new(min_xy.clone()), Box::new(Expr::var("x")))),
                Predicate::Expr(Expr::Le(Box::new(min_xy), Box::new(Expr::var("y")))),
            ])),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_max_ge_both() {
        // max(x, y) >= x and max(x, y) >= y
        let max_xy = Expr::Max(Box::new(Expr::var("x")), Box::new(Expr::var("y")));
        let vc = VerificationCondition {
            id: VcId(204),
            name: "max_ge_both".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::And(vec![
                Predicate::Expr(Expr::Ge(Box::new(max_xy.clone()), Box::new(Expr::var("x")))),
                Predicate::Expr(Expr::Ge(Box::new(max_xy), Box::new(Expr::var("y")))),
            ])),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_expr_forall() {
        // Test Expr::Forall (quantifier in expression position)
        // forall x. x + 0 = x
        let forall_expr = Expr::Forall {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Add(Box::new(Expr::var("x")), Box::new(Expr::int(0)))),
                Box::new(Expr::var("x")),
            )),
        };

        let vc = VerificationCondition {
            id: VcId(205),
            name: "expr_forall_identity".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(forall_expr)),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_expr_exists() {
        // Test Expr::Exists (quantifier in expression position)
        // exists x. x > 0 (should be provable - just find x=1)
        let exists_expr = Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Expr::Gt(Box::new(Expr::var("x")), Box::new(Expr::int(0)))),
        };

        let vc = VerificationCondition {
            id: VcId(206),
            name: "expr_exists_positive".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(exists_expr)),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_abs_of_neg() {
        // abs(-x) = abs(x) for any x
        let abs_neg_x = Expr::Abs(Box::new(Expr::Neg(Box::new(Expr::var("x")))));
        let abs_x = Expr::Abs(Box::new(Expr::var("x")));

        let vc = VerificationCondition {
            id: VcId(207),
            name: "abs_of_neg".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(abs_neg_x),
                Box::new(abs_x),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_min_max_relationship() {
        // min(x, y) <= max(x, y) for all x, y
        let min_xy = Expr::Min(Box::new(Expr::var("x")), Box::new(Expr::var("y")));
        let max_xy = Expr::Max(Box::new(Expr::var("x")), Box::new(Expr::var("y")));

        let vc = VerificationCondition {
            id: VcId(208),
            name: "min_max_relationship".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Le(
                Box::new(min_xy),
                Box::new(max_xy),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_min_idempotent() {
        // min(x, x) = x for all x
        let min_xx = Expr::Min(Box::new(Expr::var("x")), Box::new(Expr::var("x")));

        let vc = VerificationCondition {
            id: VcId(209),
            name: "min_idempotent".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(min_xx),
                Box::new(Expr::var("x")),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_max_idempotent() {
        // max(x, x) = x for all x
        let max_xx = Expr::Max(Box::new(Expr::var("x")), Box::new(Expr::var("x")));

        let vc = VerificationCondition {
            id: VcId(210),
            name: "max_idempotent".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(max_xx),
                Box::new(Expr::var("x")),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_min_commutative() {
        // min(x, y) = min(y, x) for all x, y
        let min_xy = Expr::Min(Box::new(Expr::var("x")), Box::new(Expr::var("y")));
        let min_yx = Expr::Min(Box::new(Expr::var("y")), Box::new(Expr::var("x")));

        let vc = VerificationCondition {
            id: VcId(211),
            name: "min_commutative".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(min_xy),
                Box::new(min_yx),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_max_commutative() {
        // max(x, y) = max(y, x) for all x, y
        let max_xy = Expr::Max(Box::new(Expr::var("x")), Box::new(Expr::var("y")));
        let max_yx = Expr::Max(Box::new(Expr::var("y")), Box::new(Expr::var("x")));

        let vc = VerificationCondition {
            id: VcId(212),
            name: "max_commutative".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(max_xy),
                Box::new(max_yx),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_abs_positive_identity() {
        // x >= 0 implies abs(x) = x
        let abs_x = Expr::Abs(Box::new(Expr::var("x")));

        let vc = VerificationCondition {
            id: VcId(213),
            name: "abs_positive_identity".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::Expr(Expr::Ge(
                    Box::new(Expr::var("x")),
                    Box::new(Expr::int(0)),
                )),
                consequent: Predicate::Expr(Expr::Eq(Box::new(abs_x), Box::new(Expr::var("x")))),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_abs_negative_negate() {
        // x < 0 implies abs(x) = -x
        let abs_x = Expr::Abs(Box::new(Expr::var("x")));
        let neg_x = Expr::Neg(Box::new(Expr::var("x")));

        let vc = VerificationCondition {
            id: VcId(214),
            name: "abs_negative_negate".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::Expr(Expr::Lt(
                    Box::new(Expr::var("x")),
                    Box::new(Expr::int(0)),
                )),
                consequent: Predicate::Expr(Expr::Eq(Box::new(abs_x), Box::new(neg_x))),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(matches!(result, VerifyResult::Proven));
    }

    // ============================================
    // Struct field access tests (new)
    // ============================================

    #[test]
    fn test_struct_field_equality() {
        // self.field == self.field (reflexivity with struct fields)
        let field_expr = Expr::StructField(Box::new(Expr::var("self")), "value".to_string());

        let vc = VerificationCondition {
            id: VcId(300),
            name: "struct_field_reflexive".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(field_expr.clone()),
                Box::new(field_expr),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(
            matches!(result, VerifyResult::Proven),
            "struct field reflexivity should be proven"
        );
    }

    #[test]
    fn test_struct_field_old_equality() {
        // self.field == old(self.field) when field not modified
        // This encodes as: self__field_value == __old_self__field_value
        // As an implication: true implies self.field == old(self.field)
        // With no constraints, this should return Unknown (can't prove without context)
        let field_expr = Expr::StructField(Box::new(Expr::var("self")), "size".to_string());
        let old_field_expr = Expr::Old(Box::new(field_expr.clone()));

        let vc = VerificationCondition {
            id: VcId(301),
            name: "struct_field_old_equality".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(field_expr),
                Box::new(old_field_expr),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        // Without assumptions about field modification, this cannot be proven
        // The result depends on whether field was modified - returns counterexample
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample(_) | VerifyResult::Unknown { .. }
            ),
            "struct field old equality without assumptions should not be proven, got {result:?}"
        );
    }

    #[test]
    fn test_nested_struct_field() {
        // self.inner.value == self.inner.value (nested field access)
        let inner_field = Expr::StructField(Box::new(Expr::var("self")), "inner".to_string());
        let value_field = Expr::StructField(Box::new(inner_field), "value".to_string());

        let vc = VerificationCondition {
            id: VcId(302),
            name: "nested_struct_field_reflexive".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(value_field.clone()),
                Box::new(value_field),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(
            matches!(result, VerifyResult::Proven),
            "nested struct field reflexivity should be proven"
        );
    }

    #[test]
    fn test_tuple_field_equality() {
        // t.0 == t.0 (reflexivity with tuple fields)
        let field_expr = Expr::TupleField(Box::new(Expr::var("t")), 0);

        let vc = VerificationCondition {
            id: VcId(303),
            name: "tuple_field_reflexive".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(field_expr.clone()),
                Box::new(field_expr),
            ))),
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(
            matches!(result, VerifyResult::Proven),
            "tuple field reflexivity should be proven"
        );
    }

    #[test]
    fn test_struct_field_arithmetic() {
        // self.count > 0 implies self.count >= 1
        let field_expr = Expr::StructField(Box::new(Expr::var("self")), "count".to_string());

        let vc = VerificationCondition {
            id: VcId(304),
            name: "struct_field_arithmetic".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Implies {
                antecedent: Predicate::Expr(Expr::Gt(
                    Box::new(field_expr.clone()),
                    Box::new(Expr::int(0)),
                )),
                consequent: Predicate::Expr(Expr::Ge(Box::new(field_expr), Box::new(Expr::int(1)))),
            },
            preferred_backend: None,
        };

        let result = check_vc(&vc, &default_config());
        assert!(
            matches!(result, VerifyResult::Proven),
            "struct field arithmetic should be proven"
        );
    }
}
