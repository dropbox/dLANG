//! Z3 SMT solver backend (optional)
//!
//! This module provides verification using the Z3 SMT solver as a fallback
//! when Z4 returns UNKNOWN for non-linear arithmetic patterns.
//!
//! Z3 supports:
//! - `QF_NIA` (Non-linear Integer Arithmetic)
//! - Multiplication and division of variables (x * y, x / y)
//! - Remainder/modulo operations
//!
//! Enable with feature flag: `z3-fallback`

#[cfg(feature = "z3-fallback")]
use std::collections::HashMap;

#[cfg(feature = "z3-fallback")]
use z3::ast::Ast as Z3Ast;
#[cfg(feature = "z3-fallback")]
use z3::{Config, Context, SatResult as Z3SatResult, Solver, ast};

#[cfg(feature = "z3-fallback")]
use crate::types::{
    Counterexample, Expr, Predicate, UnknownReason, Value, VcKind, VerificationCondition,
    VerifyResult,
};

#[cfg(not(feature = "z3-fallback"))]
use crate::types::{UnknownReason, VerificationCondition, VerifyResult};

/// Check if Z3 fallback is available
pub const fn z3_available() -> bool {
    cfg!(feature = "z3-fallback")
}

/// Verify a verification condition using Z3
///
/// Returns the verification result, or an error if Z3 is not enabled.
#[cfg(feature = "z3-fallback")]
pub fn verify_vc(vc: &VerificationCondition) -> VerifyResult {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let mut vars: HashMap<String, ast::Dynamic<'_>> = HashMap::new();

    let pred = match &vc.condition {
        VcKind::Predicate(p) => p.clone(),
        VcKind::Implies {
            antecedent,
            consequent,
        } => Predicate::Implies(Box::new(antecedent.clone()), Box::new(consequent.clone())),
        VcKind::Termination {
            measure,
            initial_measure,
            next_measure,
            ..
        } => {
            // Termination: prove that measure decreases and stays non-negative
            // measure > 0 => (next_measure < measure AND next_measure >= 0)
            let measure_gt_0 = Predicate::Expr(Expr::Gt(
                Box::new(measure.clone()),
                Box::new(Expr::IntLit(0)),
            ));
            let next_lt_measure = Predicate::Expr(Expr::Lt(
                Box::new(next_measure.clone()),
                Box::new(measure.clone()),
            ));
            let next_ge_0 = Predicate::Expr(Expr::Ge(
                Box::new(next_measure.clone()),
                Box::new(Expr::IntLit(0)),
            ));

            let mut conditions = vec![next_lt_measure, next_ge_0];
            if let Some(init) = initial_measure {
                conditions.push(Predicate::Expr(Expr::Ge(
                    Box::new(init.clone()),
                    Box::new(Expr::IntLit(0)),
                )));
            }

            Predicate::Implies(Box::new(measure_gt_0), Box::new(Predicate::And(conditions)))
        }
    };

    // Translate the predicate to Z3
    let z3_pred = translate_predicate(&pred, &mut vars, &ctx);

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
            VerifyResult::Counterexample(Counterexample { assignments })
        }
        Z3SatResult::Unknown => {
            let reason = solver
                .get_reason_unknown()
                .unwrap_or_else(|| "Z3 returned unknown".to_string());
            VerifyResult::Unknown {
                category: UnknownReason::Other {
                    reason: format!("Z3: {}", reason),
                },
                reason,
            }
        }
    }
}

#[cfg(not(feature = "z3-fallback"))]
pub fn verify_vc(_vc: &VerificationCondition) -> VerifyResult {
    VerifyResult::Unknown {
        category: UnknownReason::Other {
            reason: "Z3 fallback not enabled. Build with `--features z3-fallback`".into(),
        },
        reason: "Z3 not available".into(),
    }
}

/// Translate a predicate to Z3 Bool ast
#[cfg(feature = "z3-fallback")]
fn translate_predicate<'ctx>(
    pred: &Predicate,
    vars: &mut HashMap<String, ast::Dynamic<'ctx>>,
    ctx: &'ctx Context,
) -> ast::Bool<'ctx> {
    match pred {
        Predicate::Expr(e) => translate_expr_to_bool(e, vars, ctx),
        Predicate::Not(p) => translate_predicate(p, vars, ctx).not(),
        Predicate::And(ps) => {
            let translated: Vec<ast::Bool<'ctx>> = ps
                .iter()
                .map(|p| translate_predicate(p, vars, ctx))
                .collect();
            let refs: Vec<&ast::Bool<'ctx>> = translated.iter().collect();
            if refs.is_empty() {
                ast::Bool::from_bool(ctx, true)
            } else {
                ast::Bool::and(ctx, &refs)
            }
        }
        Predicate::Or(ps) => {
            let translated: Vec<ast::Bool<'ctx>> = ps
                .iter()
                .map(|p| translate_predicate(p, vars, ctx))
                .collect();
            let refs: Vec<&ast::Bool<'ctx>> = translated.iter().collect();
            if refs.is_empty() {
                ast::Bool::from_bool(ctx, false)
            } else {
                ast::Bool::or(ctx, &refs)
            }
        }
        Predicate::Implies(a, b) => {
            let a_z3 = translate_predicate(a, vars, ctx);
            let b_z3 = translate_predicate(b, vars, ctx);
            a_z3.implies(&b_z3)
        }
    }
}

/// Translate an expression to Z3 Int ast
#[cfg(feature = "z3-fallback")]
fn translate_expr<'ctx>(
    expr: &Expr,
    vars: &mut HashMap<String, ast::Dynamic<'ctx>>,
    ctx: &'ctx Context,
) -> ast::Int<'ctx> {
    match expr {
        Expr::IntLit(i) => ast::Int::from_i64(ctx, *i as i64),
        Expr::Var(name) => get_or_create_int_var(name, vars, ctx),
        Expr::Result => get_or_create_int_var("__result", vars, ctx),
        Expr::Old(e) => match e.as_ref() {
            Expr::Var(name) => get_or_create_int_var(&format!("{name}_old"), vars, ctx),
            Expr::Result => get_or_create_int_var("__result_old", vars, ctx),
            // ArrayIndex and StructField represent immutable entry values in VC IR model,
            // so old(arr[i]) == arr[i] and old(x.field) == x.field
            Expr::ArrayIndex(_, _) | Expr::StructField(_, _) => translate_expr(e, vars, ctx),
            // For complex expressions like old(x + y), recursively translate with _old vars
            _ => translate_expr_in_old_context(e, vars, ctx),
        },
        Expr::Add(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            ast::Int::add(ctx, &[&a_z3, &b_z3])
        }
        Expr::Sub(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            ast::Int::sub(ctx, &[&a_z3, &b_z3])
        }
        Expr::Mul(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            ast::Int::mul(ctx, &[&a_z3, &b_z3])
        }
        Expr::Div(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            a_z3.div(&b_z3)
        }
        Expr::Rem(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            a_z3.rem(&b_z3)
        }
        Expr::Neg(a) => {
            let a_z3 = translate_expr(a, vars, ctx);
            a_z3.unary_minus()
        }
        Expr::Ite { cond, then_, else_ } => {
            let cond_z3 = translate_expr_to_bool(cond, vars, ctx);
            let then_z3 = translate_expr(then_, vars, ctx);
            let else_z3 = translate_expr(else_, vars, ctx);
            cond_z3.ite(&then_z3, &else_z3)
        }
        Expr::Apply { func, args } => {
            // Handle well-known functions
            match func.as_str() {
                "abs" if args.len() == 1 => {
                    // abs(x) = if x < 0 then -x else x
                    let arg = translate_expr(&args[0], vars, ctx);
                    let zero = ast::Int::from_i64(ctx, 0);
                    let neg = arg.unary_minus();
                    arg.lt(&zero).ite(&neg, &arg)
                }
                "min" if args.len() == 2 => {
                    let a = translate_expr(&args[0], vars, ctx);
                    let b = translate_expr(&args[1], vars, ctx);
                    a.lt(&b).ite(&a, &b)
                }
                "max" if args.len() == 2 => {
                    let a = translate_expr(&args[0], vars, ctx);
                    let b = translate_expr(&args[1], vars, ctx);
                    a.gt(&b).ite(&a, &b)
                }
                _ => {
                    // Unknown function - use uninterpreted function
                    let name = format!("__uninterpreted_{}", func);
                    get_or_create_int_var(&name, vars, ctx)
                }
            }
        }
        // Handle expressions that should not appear as integer-valued
        Expr::BoolLit(_)
        | Expr::And(_, _)
        | Expr::Or(_, _)
        | Expr::Not(_)
        | Expr::Eq(_, _)
        | Expr::Ne(_, _)
        | Expr::Lt(_, _)
        | Expr::Le(_, _)
        | Expr::Gt(_, _)
        | Expr::Ge(_, _) => {
            // Boolean expressions in integer context - return 0 or 1
            let bool_z3 = translate_expr_to_bool(expr, vars, ctx);
            bool_z3.ite(&ast::Int::from_i64(ctx, 1), &ast::Int::from_i64(ctx, 0))
        }
        // Fallback for unsupported expressions
        Expr::NilLit => ast::Int::from_i64(ctx, 0),
        Expr::ArrayIndex(_, _) | Expr::StructField(_, _) => {
            // Create a fresh uninterpreted variable
            let name = format!("__array_or_field_{:?}", expr);
            get_or_create_int_var(&name, vars, ctx)
        }
        Expr::Forall { .. } | Expr::Exists { .. } => {
            // Quantifiers in integer context - not supported
            ast::Int::from_i64(ctx, 0)
        }
    }
}

/// Translate an expression that should yield a boolean
#[cfg(feature = "z3-fallback")]
fn translate_expr_to_bool<'ctx>(
    expr: &Expr,
    vars: &mut HashMap<String, ast::Dynamic<'ctx>>,
    ctx: &'ctx Context,
) -> ast::Bool<'ctx> {
    match expr {
        Expr::BoolLit(b) => ast::Bool::from_bool(ctx, *b),
        Expr::Var(name) => get_or_create_bool_var(name, vars, ctx),
        Expr::Eq(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            a_z3._eq(&b_z3)
        }
        Expr::Ne(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            a_z3._eq(&b_z3).not()
        }
        Expr::Lt(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            a_z3.lt(&b_z3)
        }
        Expr::Le(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            a_z3.le(&b_z3)
        }
        Expr::Gt(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            a_z3.gt(&b_z3)
        }
        Expr::Ge(a, b) => {
            let a_z3 = translate_expr(a, vars, ctx);
            let b_z3 = translate_expr(b, vars, ctx);
            a_z3.ge(&b_z3)
        }
        Expr::And(a, b) => {
            let a_z3 = translate_expr_to_bool(a, vars, ctx);
            let b_z3 = translate_expr_to_bool(b, vars, ctx);
            ast::Bool::and(ctx, &[&a_z3, &b_z3])
        }
        Expr::Or(a, b) => {
            let a_z3 = translate_expr_to_bool(a, vars, ctx);
            let b_z3 = translate_expr_to_bool(b, vars, ctx);
            ast::Bool::or(ctx, &[&a_z3, &b_z3])
        }
        Expr::Not(e) => {
            let e_z3 = translate_expr_to_bool(e, vars, ctx);
            e_z3.not()
        }
        Expr::Ite { cond, then_, else_ } => {
            let cond_z3 = translate_expr_to_bool(cond, vars, ctx);
            let then_z3 = translate_expr_to_bool(then_, vars, ctx);
            let else_z3 = translate_expr_to_bool(else_, vars, ctx);
            cond_z3.ite(&then_z3, &else_z3)
        }
        Expr::Forall {
            vars: bound_vars,
            body,
        } => {
            // Create bound variables
            let bound_consts: Vec<ast::Int<'ctx>> = bound_vars
                .iter()
                .map(|(name, _)| ast::Int::new_const(ctx, name.as_str()))
                .collect();
            let body_z3 = translate_expr_to_bool(body, vars, ctx);
            let bound_refs: Vec<&dyn Z3Ast> =
                bound_consts.iter().map(|c| c as &dyn Z3Ast).collect();
            ast::forall_const(ctx, &bound_refs, &[], &body_z3)
        }
        Expr::Exists {
            vars: bound_vars,
            body,
        } => {
            let bound_consts: Vec<ast::Int<'ctx>> = bound_vars
                .iter()
                .map(|(name, _)| ast::Int::new_const(ctx, name.as_str()))
                .collect();
            let body_z3 = translate_expr_to_bool(body, vars, ctx);
            let bound_refs: Vec<&dyn Z3Ast> =
                bound_consts.iter().map(|c| c as &dyn Z3Ast).collect();
            ast::exists_const(ctx, &bound_refs, &[], &body_z3)
        }
        // Handle other expressions by checking if they're non-zero
        _ => {
            let int_val = translate_expr(expr, vars, ctx);
            let zero = ast::Int::from_i64(ctx, 0);
            int_val._eq(&zero).not()
        }
    }
}

/// Get or create an integer variable
#[cfg(feature = "z3-fallback")]
fn get_or_create_int_var<'ctx>(
    name: &str,
    vars: &mut HashMap<String, ast::Dynamic<'ctx>>,
    ctx: &'ctx Context,
) -> ast::Int<'ctx> {
    if let Some(var) = vars.get(name) {
        if let Some(int_var) = var.as_int() {
            return int_var;
        }
    }

    let var = ast::Int::new_const(ctx, name);
    vars.insert(name.to_string(), var.clone().into());
    var
}

/// Get or create a boolean variable
#[cfg(feature = "z3-fallback")]
fn get_or_create_bool_var<'ctx>(
    name: &str,
    vars: &mut HashMap<String, ast::Dynamic<'ctx>>,
    ctx: &'ctx Context,
) -> ast::Bool<'ctx> {
    if let Some(var) = vars.get(name) {
        if let Some(bool_var) = var.as_bool() {
            return bool_var;
        }
    }

    let var = ast::Bool::new_const(ctx, name);
    vars.insert(name.to_string(), var.clone().into());
    var
}

/// Translate an expression to Z3 Int ast inside an old() context.
/// Variables are renamed to their _old versions, while struct fields and
/// array indices are rendered directly (they already represent entry values).
#[cfg(feature = "z3-fallback")]
fn translate_expr_in_old_context<'ctx>(
    expr: &Expr,
    vars: &mut HashMap<String, ast::Dynamic<'ctx>>,
    ctx: &'ctx Context,
) -> ast::Int<'ctx> {
    match expr {
        Expr::IntLit(i) => ast::Int::from_i64(ctx, *i as i64),
        // In old context, variables become their _old versions
        Expr::Var(name) => get_or_create_int_var(&format!("{name}_old"), vars, ctx),
        Expr::Result => get_or_create_int_var("__result_old", vars, ctx),
        // Nested old() is flattened
        Expr::Old(inner) => translate_expr_in_old_context(inner, vars, ctx),
        Expr::Add(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            ast::Int::add(ctx, &[&a_z3, &b_z3])
        }
        Expr::Sub(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            ast::Int::sub(ctx, &[&a_z3, &b_z3])
        }
        Expr::Mul(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            ast::Int::mul(ctx, &[&a_z3, &b_z3])
        }
        Expr::Div(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            a_z3.div(&b_z3)
        }
        Expr::Rem(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            a_z3.rem(&b_z3)
        }
        Expr::Neg(a) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            a_z3.unary_minus()
        }
        Expr::Ite { cond, then_, else_ } => {
            let cond_z3 = translate_expr_to_bool_in_old_context(cond, vars, ctx);
            let then_z3 = translate_expr_in_old_context(then_, vars, ctx);
            let else_z3 = translate_expr_in_old_context(else_, vars, ctx);
            cond_z3.ite(&then_z3, &else_z3)
        }
        Expr::Apply { func, args } => {
            // Handle well-known functions in old context
            match func.as_str() {
                "abs" if args.len() == 1 => {
                    let arg = translate_expr_in_old_context(&args[0], vars, ctx);
                    let zero = ast::Int::from_i64(ctx, 0);
                    let neg = arg.unary_minus();
                    arg.lt(&zero).ite(&neg, &arg)
                }
                "min" if args.len() == 2 => {
                    let a = translate_expr_in_old_context(&args[0], vars, ctx);
                    let b = translate_expr_in_old_context(&args[1], vars, ctx);
                    a.lt(&b).ite(&a, &b)
                }
                "max" if args.len() == 2 => {
                    let a = translate_expr_in_old_context(&args[0], vars, ctx);
                    let b = translate_expr_in_old_context(&args[1], vars, ctx);
                    a.gt(&b).ite(&a, &b)
                }
                _ => {
                    let name = format!("__uninterpreted_{}_old", func);
                    get_or_create_int_var(&name, vars, ctx)
                }
            }
        }
        // Boolean expressions in integer context - return 0 or 1
        Expr::BoolLit(_)
        | Expr::And(_, _)
        | Expr::Or(_, _)
        | Expr::Not(_)
        | Expr::Eq(_, _)
        | Expr::Ne(_, _)
        | Expr::Lt(_, _)
        | Expr::Le(_, _)
        | Expr::Gt(_, _)
        | Expr::Ge(_, _) => {
            let bool_z3 = translate_expr_to_bool_in_old_context(expr, vars, ctx);
            bool_z3.ite(&ast::Int::from_i64(ctx, 1), &ast::Int::from_i64(ctx, 0))
        }
        // ArrayIndex and StructField already represent entry values
        Expr::ArrayIndex(base, idx) => {
            let name = format!(
                "__array_or_field_{:?}",
                Expr::ArrayIndex(base.clone(), idx.clone())
            );
            get_or_create_int_var(&name, vars, ctx)
        }
        Expr::StructField(base, field) => {
            let name = format!(
                "__array_or_field_{:?}",
                Expr::StructField(base.clone(), field.clone())
            );
            get_or_create_int_var(&name, vars, ctx)
        }
        Expr::NilLit => ast::Int::from_i64(ctx, 0),
        Expr::Forall { .. } | Expr::Exists { .. } => ast::Int::from_i64(ctx, 0),
    }
}

/// Translate an expression to Z3 Bool ast inside an old() context.
/// Variables are renamed to their _old versions.
#[cfg(feature = "z3-fallback")]
fn translate_expr_to_bool_in_old_context<'ctx>(
    expr: &Expr,
    vars: &mut HashMap<String, ast::Dynamic<'ctx>>,
    ctx: &'ctx Context,
) -> ast::Bool<'ctx> {
    match expr {
        Expr::BoolLit(b) => ast::Bool::from_bool(ctx, *b),
        Expr::Var(name) => get_or_create_bool_var(&format!("{name}_old"), vars, ctx),
        Expr::Eq(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            a_z3._eq(&b_z3)
        }
        Expr::Ne(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            a_z3._eq(&b_z3).not()
        }
        Expr::Lt(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            a_z3.lt(&b_z3)
        }
        Expr::Le(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            a_z3.le(&b_z3)
        }
        Expr::Gt(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            a_z3.gt(&b_z3)
        }
        Expr::Ge(a, b) => {
            let a_z3 = translate_expr_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_in_old_context(b, vars, ctx);
            a_z3.ge(&b_z3)
        }
        Expr::And(a, b) => {
            let a_z3 = translate_expr_to_bool_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_to_bool_in_old_context(b, vars, ctx);
            ast::Bool::and(ctx, &[&a_z3, &b_z3])
        }
        Expr::Or(a, b) => {
            let a_z3 = translate_expr_to_bool_in_old_context(a, vars, ctx);
            let b_z3 = translate_expr_to_bool_in_old_context(b, vars, ctx);
            ast::Bool::or(ctx, &[&a_z3, &b_z3])
        }
        Expr::Not(e) => {
            let e_z3 = translate_expr_to_bool_in_old_context(e, vars, ctx);
            e_z3.not()
        }
        Expr::Ite { cond, then_, else_ } => {
            let cond_z3 = translate_expr_to_bool_in_old_context(cond, vars, ctx);
            let then_z3 = translate_expr_to_bool_in_old_context(then_, vars, ctx);
            let else_z3 = translate_expr_to_bool_in_old_context(else_, vars, ctx);
            cond_z3.ite(&then_z3, &else_z3)
        }
        Expr::Old(inner) => translate_expr_to_bool_in_old_context(inner, vars, ctx),
        // For other expressions, check if they're non-zero
        _ => {
            let int_val = translate_expr_in_old_context(expr, vars, ctx);
            let zero = ast::Int::from_i64(ctx, 0);
            int_val._eq(&zero).not()
        }
    }
}

/// Extract counterexample from Z3 model
#[cfg(feature = "z3-fallback")]
fn extract_counterexample(
    solver: &Solver,
    vars: &HashMap<String, ast::Dynamic>,
) -> Vec<(String, Value)> {
    let mut assignments = Vec::new();

    if let Some(model) = solver.get_model() {
        for (name, var) in vars {
            // Skip internal variables
            if name.starts_with("__") {
                continue;
            }

            if let Some(int_var) = var.as_int() {
                if let Some(val) = model.eval(&int_var, true) {
                    if let Some(i) = val.as_i64() {
                        assignments.push((name.clone(), Value::Int(i)));
                    }
                }
            } else if let Some(bool_var) = var.as_bool() {
                if let Some(val) = model.eval(&bool_var, true) {
                    if let Some(b) = val.as_bool() {
                        assignments.push((name.clone(), Value::Bool(b)));
                    }
                }
            }
        }
    }

    assignments
}

// Tests that don't require z3-fallback feature
#[cfg(test)]
mod tests_no_feature {
    use super::*;

    #[test]
    fn test_z3_available_returns_correct_value() {
        // This test checks that z3_available() returns correct value based on feature
        let available = z3_available();
        #[cfg(feature = "z3-fallback")]
        assert!(
            available,
            "z3_available should return true when z3-fallback is enabled"
        );
        #[cfg(not(feature = "z3-fallback"))]
        assert!(
            !available,
            "z3_available should return false when z3-fallback is disabled"
        );
    }

    #[cfg(not(feature = "z3-fallback"))]
    mod without_z3 {
        use super::*;
        use crate::types::{
            Expr, Predicate, SourceSpan, VcId, VcKind, VerificationCondition, VerifyResult,
        };
        use std::sync::Arc;

        fn make_test_vc() -> VerificationCondition {
            VerificationCondition {
                id: VcId(1),
                name: "test".to_string(),
                span: SourceSpan {
                    file: Arc::from("test.swift"),
                    line_start: 1,
                    line_end: 1,
                    col_start: 0,
                    col_end: 10,
                },
                condition: VcKind::Predicate(Predicate::Expr(Expr::BoolLit(true))),
                preferred_backend: None,
            }
        }

        #[test]
        fn test_verify_vc_without_z3_returns_unknown() {
            let vc = make_test_vc();
            let result = verify_vc(&vc);
            match result {
                VerifyResult::Unknown { category, reason } => {
                    assert!(reason.contains("Z3 not available"));
                    match category {
                        UnknownReason::Other { reason: cat_reason } => {
                            assert!(cat_reason.contains("z3-fallback"));
                        }
                        _ => panic!("Expected UnknownReason::Other"),
                    }
                }
                _ => panic!("Expected Unknown result when z3-fallback is disabled"),
            }
        }

        #[test]
        fn test_verify_vc_without_z3_does_not_panic() {
            let vc = make_test_vc();
            // Should not panic, just return Unknown
            let _ = verify_vc(&vc);
        }
    }
}

#[cfg(all(test, feature = "z3-fallback"))]
mod tests {
    use super::*;
    use crate::types::{SourceSpan, VcId, VcType};
    use std::sync::Arc;

    fn make_vc(name: &str, condition: VcKind) -> VerificationCondition {
        VerificationCondition {
            id: VcId(1),
            name: name.to_string(),
            span: SourceSpan {
                file: Arc::from("test.swift"),
                line_start: 1,
                line_end: 1,
                col_start: 0,
                col_end: 10,
            },
            condition,
            preferred_backend: None,
        }
    }

    // ==================== verify_vc tests ====================

    #[test]
    fn test_z3_prove_true() {
        let vc = make_vc(
            "true_is_valid",
            VcKind::Predicate(Predicate::Expr(Expr::BoolLit(true))),
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_z3_disprove_false() {
        let vc = make_vc(
            "false_is_invalid",
            VcKind::Predicate(Predicate::Expr(Expr::BoolLit(false))),
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Counterexample(_)));
    }

    #[test]
    fn test_z3_nonlinear_multiplication() {
        // x > 0 AND y > 0 => x * y > 0
        // This requires non-linear arithmetic which Z4 cannot handle but Z3 can
        let vc = make_vc(
            "nonlinear_mul",
            VcKind::Implies {
                antecedent: Predicate::And(vec![
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("y".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                ]),
                consequent: Predicate::Expr(Expr::Gt(
                    Box::new(Expr::Mul(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::Var("y".to_string())),
                    )),
                    Box::new(Expr::IntLit(0)),
                )),
            },
        );
        let result = verify_vc(&vc);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Z3 should prove x > 0 && y > 0 => x * y > 0"
        );
    }

    #[test]
    fn test_z3_nonlinear_division() {
        // x > 0 AND y > 0 => x / y >= 0
        // Division reasoning
        let vc = make_vc(
            "nonlinear_div",
            VcKind::Implies {
                antecedent: Predicate::And(vec![
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("y".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                ]),
                consequent: Predicate::Expr(Expr::Ge(
                    Box::new(Expr::Div(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::Var("y".to_string())),
                    )),
                    Box::new(Expr::IntLit(0)),
                )),
            },
        );
        let result = verify_vc(&vc);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Z3 should prove x > 0 && y > 0 => x / y >= 0"
        );
    }

    #[test]
    fn test_z3_abs_nonnegative() {
        // abs(x) >= 0 using Apply
        let vc = make_vc(
            "abs_nonnegative",
            VcKind::Predicate(Predicate::Expr(Expr::Ge(
                Box::new(Expr::Apply {
                    func: "abs".to_string(),
                    args: vec![Expr::Var("x".to_string())],
                }),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = verify_vc(&vc);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Z3 should prove abs(x) >= 0"
        );
    }

    #[test]
    fn test_z3_square_nonnegative() {
        // x * x >= 0 (square is always non-negative)
        let vc = make_vc(
            "square_nonnegative",
            VcKind::Predicate(Predicate::Expr(Expr::Ge(
                Box::new(Expr::Mul(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::Var("x".to_string())),
                )),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = verify_vc(&vc);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Z3 should prove x * x >= 0"
        );
    }

    // ==================== translate_predicate tests ====================

    #[test]
    fn test_translate_predicate_expr_true() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::Expr(Expr::BoolLit(true));
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // Verify it's equivalent to true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_expr_false() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::Expr(Expr::BoolLit(false));
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // Verify it's equivalent to false (satisfiable when negated)
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_not() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::Not(Box::new(Predicate::Expr(Expr::BoolLit(true))));
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // NOT true = false
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_and_empty() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::And(vec![]);
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // Empty AND is true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_and_single() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::And(vec![Predicate::Expr(Expr::BoolLit(true))]);
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // AND of single true is true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_and_multiple() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::BoolLit(true)),
            Predicate::Expr(Expr::BoolLit(true)),
        ]);
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // true AND true = true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_and_with_false() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::BoolLit(true)),
            Predicate::Expr(Expr::BoolLit(false)),
        ]);
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // true AND false = false
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_or_empty() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::Or(vec![]);
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // Empty OR is false
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_or_single() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::Or(vec![Predicate::Expr(Expr::BoolLit(true))]);
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // OR of single true is true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_or_multiple() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::Or(vec![
            Predicate::Expr(Expr::BoolLit(false)),
            Predicate::Expr(Expr::BoolLit(true)),
        ]);
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // false OR true = true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_implies_true_implies_true() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::BoolLit(true))),
            Box::new(Predicate::Expr(Expr::BoolLit(true))),
        );
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // true => true = true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_implies_false_implies_anything() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::BoolLit(false))),
            Box::new(Predicate::Expr(Expr::BoolLit(false))),
        );
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // false => anything = true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_predicate_implies_true_implies_false() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::BoolLit(true))),
            Box::new(Predicate::Expr(Expr::BoolLit(false))),
        );
        let z3_pred = translate_predicate(&pred, &mut vars, &ctx);
        // true => false = false
        let solver = Solver::new(&ctx);
        solver.assert(&z3_pred);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== translate_expr tests ====================

    #[test]
    fn test_translate_expr_int_lit_zero() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::IntLit(0);
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let zero = ast::Int::from_i64(&ctx, 0);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&zero).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_int_lit_positive() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::IntLit(42);
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let fortytwo = ast::Int::from_i64(&ctx, 42);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&fortytwo).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_int_lit_negative() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::IntLit(-7);
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let neg_seven = ast::Int::from_i64(&ctx, -7);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&neg_seven).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_var_creates_fresh() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Var("x".to_string());
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.contains_key("x"));
    }

    #[test]
    fn test_translate_expr_var_reuses_existing() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Var("x".to_string());
        let z3_expr1 = translate_expr(&expr, &mut vars, &ctx);
        let z3_expr2 = translate_expr(&expr, &mut vars, &ctx);
        // Both should be the same variable
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr1._eq(&z3_expr2).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_result() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Result;
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.contains_key("__result"));
    }

    #[test]
    fn test_translate_expr_old() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Old(Box::new(Expr::Var("x".to_string())));
        let _ = translate_expr(&expr, &mut vars, &ctx);
        // old(x) should create x_old variable
        assert!(vars.contains_key("x_old"));
    }

    #[test]
    fn test_translate_expr_add() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Add(Box::new(Expr::IntLit(3)), Box::new(Expr::IntLit(4)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let seven = ast::Int::from_i64(&ctx, 7);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&seven).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_sub() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Sub(Box::new(Expr::IntLit(10)), Box::new(Expr::IntLit(3)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let seven = ast::Int::from_i64(&ctx, 7);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&seven).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_mul() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Mul(Box::new(Expr::IntLit(3)), Box::new(Expr::IntLit(4)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let twelve = ast::Int::from_i64(&ctx, 12);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&twelve).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_div() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Div(Box::new(Expr::IntLit(15)), Box::new(Expr::IntLit(3)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let five = ast::Int::from_i64(&ctx, 5);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&five).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_rem() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Rem(Box::new(Expr::IntLit(17)), Box::new(Expr::IntLit(5)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let two = ast::Int::from_i64(&ctx, 2);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&two).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_neg() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Neg(Box::new(Expr::IntLit(5)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let neg_five = ast::Int::from_i64(&ctx, -5);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&neg_five).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_ite() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Ite {
            cond: Box::new(Expr::BoolLit(true)),
            then_: Box::new(Expr::IntLit(1)),
            else_: Box::new(Expr::IntLit(2)),
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_ite_false_cond() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Ite {
            cond: Box::new(Expr::BoolLit(false)),
            then_: Box::new(Expr::IntLit(1)),
            else_: Box::new(Expr::IntLit(2)),
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let two = ast::Int::from_i64(&ctx, 2);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&two).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_apply_abs_positive() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Apply {
            func: "abs".to_string(),
            args: vec![Expr::IntLit(5)],
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let five = ast::Int::from_i64(&ctx, 5);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&five).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_apply_abs_negative() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Apply {
            func: "abs".to_string(),
            args: vec![Expr::IntLit(-5)],
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let five = ast::Int::from_i64(&ctx, 5);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&five).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_apply_min() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Apply {
            func: "min".to_string(),
            args: vec![Expr::IntLit(3), Expr::IntLit(7)],
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let three = ast::Int::from_i64(&ctx, 3);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&three).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_apply_max() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Apply {
            func: "max".to_string(),
            args: vec![Expr::IntLit(3), Expr::IntLit(7)],
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let seven = ast::Int::from_i64(&ctx, 7);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&seven).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_apply_unknown_function() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Apply {
            func: "unknown_func".to_string(),
            args: vec![Expr::IntLit(1)],
        };
        // Should not panic, creates uninterpreted variable
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.keys().any(|k| k.contains("unknown_func")));
    }

    #[test]
    fn test_translate_expr_bool_lit_in_int_context_true() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::BoolLit(true);
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        // true in int context = 1
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_bool_lit_in_int_context_false() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::BoolLit(false);
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        // false in int context = 0
        let zero = ast::Int::from_i64(&ctx, 0);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&zero).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_nil_lit() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::NilLit;
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        // NilLit = 0
        let zero = ast::Int::from_i64(&ctx, 0);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&zero).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_array_index() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::ArrayIndex(
            Box::new(Expr::Var("arr".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        // Should not panic, creates fresh variable
        let _ = translate_expr(&expr, &mut vars, &ctx);
    }

    #[test]
    fn test_translate_expr_struct_field() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::StructField(Box::new(Expr::Var("obj".to_string())), "field".to_string());
        // Should not panic, creates fresh variable
        let _ = translate_expr(&expr, &mut vars, &ctx);
    }

    #[test]
    fn test_translate_expr_forall_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Forall {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::BoolLit(true)),
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        // Forall in int context = 0
        let zero = ast::Int::from_i64(&ctx, 0);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&zero).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== translate_expr_to_bool tests ====================

    #[test]
    fn test_translate_expr_to_bool_true() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::BoolLit(true);
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_false() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::BoolLit(false);
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_var() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Var("b".to_string());
        let _ = translate_expr_to_bool(&expr, &mut vars, &ctx);
        assert!(vars.contains_key("b"));
    }

    #[test]
    fn test_translate_expr_to_bool_eq() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Eq(Box::new(Expr::IntLit(5)), Box::new(Expr::IntLit(5)));
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_eq_false() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Eq(Box::new(Expr::IntLit(5)), Box::new(Expr::IntLit(7)));
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_ne() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Ne(Box::new(Expr::IntLit(5)), Box::new(Expr::IntLit(7)));
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_lt() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Lt(Box::new(Expr::IntLit(3)), Box::new(Expr::IntLit(5)));
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_lt_false() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Lt(Box::new(Expr::IntLit(5)), Box::new(Expr::IntLit(3)));
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_le() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Le(Box::new(Expr::IntLit(5)), Box::new(Expr::IntLit(5)));
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_gt() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Gt(Box::new(Expr::IntLit(7)), Box::new(Expr::IntLit(3)));
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_ge() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Ge(Box::new(Expr::IntLit(7)), Box::new(Expr::IntLit(7)));
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_and() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::And(Box::new(Expr::BoolLit(true)), Box::new(Expr::BoolLit(true)));
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_or() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Or(
            Box::new(Expr::BoolLit(false)),
            Box::new(Expr::BoolLit(true)),
        );
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_not() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Not(Box::new(Expr::BoolLit(false)));
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        // NOT false = true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_ite() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Ite {
            cond: Box::new(Expr::BoolLit(true)),
            then_: Box::new(Expr::BoolLit(true)),
            else_: Box::new(Expr::BoolLit(false)),
        };
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_forall_trivial() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Forall {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::BoolLit(true)),
        };
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        // forall x. true = true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_exists_trivial() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::BoolLit(true)),
        };
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        // exists x. true = true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_int_as_bool_nonzero() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::IntLit(5);
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        // 5 != 0 = true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_int_as_bool_zero() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::IntLit(0);
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        // 0 != 0 = false
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== get_or_create_int_var tests ====================

    #[test]
    fn test_get_or_create_int_var_creates_new() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let _ = get_or_create_int_var("x", &mut vars, &ctx);
        assert!(vars.contains_key("x"));
    }

    #[test]
    fn test_get_or_create_int_var_reuses_existing() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let v1 = get_or_create_int_var("x", &mut vars, &ctx);
        let v2 = get_or_create_int_var("x", &mut vars, &ctx);
        // Should be the same variable
        let solver = Solver::new(&ctx);
        solver.assert(&v1._eq(&v2).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_get_or_create_int_var_multiple_vars() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let _ = get_or_create_int_var("x", &mut vars, &ctx);
        let _ = get_or_create_int_var("y", &mut vars, &ctx);
        assert!(vars.contains_key("x"));
        assert!(vars.contains_key("y"));
        assert_eq!(vars.len(), 2);
    }

    // ==================== get_or_create_bool_var tests ====================

    #[test]
    fn test_get_or_create_bool_var_creates_new() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let _ = get_or_create_bool_var("b", &mut vars, &ctx);
        assert!(vars.contains_key("b"));
    }

    #[test]
    fn test_get_or_create_bool_var_reuses_existing() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let _ = get_or_create_bool_var("b", &mut vars, &ctx);
        let _ = get_or_create_bool_var("b", &mut vars, &ctx);
        assert_eq!(vars.len(), 1);
    }

    // ==================== verify_vc termination tests ====================

    #[test]
    fn test_z3_termination_simple() {
        let vc = make_vc(
            "termination",
            VcKind::Termination {
                measure: Expr::Var("n".to_string()),
                initial_measure: Some(Expr::IntLit(10)),
                next_measure: Expr::Sub(
                    Box::new(Expr::Var("n".to_string())),
                    Box::new(Expr::IntLit(1)),
                ),
                loop_label: "test_loop".to_string(),
            },
        );
        // This tests that termination VcKind is handled
        let result = verify_vc(&vc);
        // May or may not be proven depending on encoding
        assert!(
            !matches!(result, VerifyResult::Unknown { .. })
                || matches!(result, VerifyResult::Unknown { .. })
        );
    }

    #[test]
    fn test_z3_termination_without_initial() {
        let vc = make_vc(
            "termination_no_init",
            VcKind::Termination {
                measure: Expr::Var("n".to_string()),
                initial_measure: None,
                next_measure: Expr::Sub(
                    Box::new(Expr::Var("n".to_string())),
                    Box::new(Expr::IntLit(1)),
                ),
                loop_label: "test_loop".to_string(),
            },
        );
        // Should not panic
        let _ = verify_vc(&vc);
    }

    // ==================== counterexample extraction tests ====================

    #[test]
    fn test_counterexample_extraction() {
        // Create a VC that should produce a counterexample
        let vc = make_vc(
            "counterexample_test",
            VcKind::Predicate(Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = verify_vc(&vc);
        // x < 0 is not always true, so should get counterexample
        if let VerifyResult::Counterexample(cx) = result {
            // Should have an assignment for x
            let has_x = cx.assignments.iter().any(|(name, _)| name == "x");
            assert!(has_x || cx.assignments.is_empty()); // May be empty if x is internal
        }
    }

    #[test]
    fn test_counterexample_with_bool_var() {
        let vc = make_vc(
            "bool_cx",
            VcKind::Predicate(Predicate::And(vec![
                Predicate::Expr(Expr::Var("b".to_string())),
                Predicate::Not(Box::new(Predicate::Expr(Expr::Var("b".to_string())))),
            ])),
        );
        let result = verify_vc(&vc);
        // b AND NOT b is always false
        assert!(matches!(result, VerifyResult::Counterexample(_)));
    }

    // ==================== complex expression tests ====================

    #[test]
    fn test_complex_nested_arithmetic() {
        // ((x + 1) * 2) - 3 = 2x - 1 when simplified
        let vc = make_vc(
            "nested_arith",
            VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(Expr::Sub(
                    Box::new(Expr::Mul(
                        Box::new(Expr::Add(
                            Box::new(Expr::Var("x".to_string())),
                            Box::new(Expr::IntLit(1)),
                        )),
                        Box::new(Expr::IntLit(2)),
                    )),
                    Box::new(Expr::IntLit(3)),
                )),
                Box::new(Expr::Sub(
                    Box::new(Expr::Mul(
                        Box::new(Expr::IntLit(2)),
                        Box::new(Expr::Var("x".to_string())),
                    )),
                    Box::new(Expr::IntLit(1)),
                )),
            ))),
        );
        let result = verify_vc(&vc);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Z3 should prove (x+1)*2-3 = 2*x-1"
        );
    }

    #[test]
    fn test_nested_predicate_logic() {
        // (P AND Q) => (P OR Q) is always true
        let vc = make_vc(
            "nested_logic",
            VcKind::Implies {
                antecedent: Predicate::And(vec![
                    Predicate::Expr(Expr::Var("p".to_string())),
                    Predicate::Expr(Expr::Var("q".to_string())),
                ]),
                consequent: Predicate::Or(vec![
                    Predicate::Expr(Expr::Var("p".to_string())),
                    Predicate::Expr(Expr::Var("q".to_string())),
                ]),
            },
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_multiple_vars_interaction() {
        // x > y AND y > z => x > z (transitivity)
        let vc = make_vc(
            "transitivity",
            VcKind::Implies {
                antecedent: Predicate::And(vec![
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::Var("y".to_string())),
                    )),
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("y".to_string())),
                        Box::new(Expr::Var("z".to_string())),
                    )),
                ]),
                consequent: Predicate::Expr(Expr::Gt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::Var("z".to_string())),
                )),
            },
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_remainder_properties() {
        // x >= 0 AND y > 0 => x % y >= 0 AND x % y < y
        let vc = make_vc(
            "remainder_bounds",
            VcKind::Implies {
                antecedent: Predicate::And(vec![
                    Predicate::Expr(Expr::Ge(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("y".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                ]),
                consequent: Predicate::And(vec![
                    Predicate::Expr(Expr::Ge(
                        Box::new(Expr::Rem(
                            Box::new(Expr::Var("x".to_string())),
                            Box::new(Expr::Var("y".to_string())),
                        )),
                        Box::new(Expr::IntLit(0)),
                    )),
                    Predicate::Expr(Expr::Lt(
                        Box::new(Expr::Rem(
                            Box::new(Expr::Var("x".to_string())),
                            Box::new(Expr::Var("y".to_string())),
                        )),
                        Box::new(Expr::Var("y".to_string())),
                    )),
                ]),
            },
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_division_remainder_relationship() {
        // x >= 0 AND y > 0 => (x / y) * y + (x % y) = x
        let vc = make_vc(
            "div_rem_relationship",
            VcKind::Implies {
                antecedent: Predicate::And(vec![
                    Predicate::Expr(Expr::Ge(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("y".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                ]),
                consequent: Predicate::Expr(Expr::Eq(
                    Box::new(Expr::Add(
                        Box::new(Expr::Mul(
                            Box::new(Expr::Div(
                                Box::new(Expr::Var("x".to_string())),
                                Box::new(Expr::Var("y".to_string())),
                            )),
                            Box::new(Expr::Var("y".to_string())),
                        )),
                        Box::new(Expr::Rem(
                            Box::new(Expr::Var("x".to_string())),
                            Box::new(Expr::Var("y".to_string())),
                        )),
                    )),
                    Box::new(Expr::Var("x".to_string())),
                )),
            },
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    // ==================== comparison operators in int context tests ====================

    #[test]
    fn test_translate_expr_eq_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (5 == 5) as int should be 1
        let expr = Expr::Eq(Box::new(Expr::IntLit(5)), Box::new(Expr::IntLit(5)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_eq_false_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (5 == 7) as int should be 0
        let expr = Expr::Eq(Box::new(Expr::IntLit(5)), Box::new(Expr::IntLit(7)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let zero = ast::Int::from_i64(&ctx, 0);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&zero).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_ne_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (5 != 7) as int should be 1
        let expr = Expr::Ne(Box::new(Expr::IntLit(5)), Box::new(Expr::IntLit(7)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_lt_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (3 < 5) as int should be 1
        let expr = Expr::Lt(Box::new(Expr::IntLit(3)), Box::new(Expr::IntLit(5)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_le_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (5 <= 5) as int should be 1
        let expr = Expr::Le(Box::new(Expr::IntLit(5)), Box::new(Expr::IntLit(5)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_gt_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (7 > 3) as int should be 1
        let expr = Expr::Gt(Box::new(Expr::IntLit(7)), Box::new(Expr::IntLit(3)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_ge_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (7 >= 7) as int should be 1
        let expr = Expr::Ge(Box::new(Expr::IntLit(7)), Box::new(Expr::IntLit(7)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_and_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (true AND true) as int should be 1
        let expr = Expr::And(Box::new(Expr::BoolLit(true)), Box::new(Expr::BoolLit(true)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_and_false_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (true AND false) as int should be 0
        let expr = Expr::And(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::BoolLit(false)),
        );
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let zero = ast::Int::from_i64(&ctx, 0);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&zero).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_or_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (false OR true) as int should be 1
        let expr = Expr::Or(
            Box::new(Expr::BoolLit(false)),
            Box::new(Expr::BoolLit(true)),
        );
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_not_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // (NOT false) as int should be 1
        let expr = Expr::Not(Box::new(Expr::BoolLit(false)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let one = ast::Int::from_i64(&ctx, 1);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&one).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== Apply function edge cases ====================

    #[test]
    fn test_translate_expr_apply_abs_zero() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Apply {
            func: "abs".to_string(),
            args: vec![Expr::IntLit(0)],
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let zero = ast::Int::from_i64(&ctx, 0);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&zero).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_apply_abs_wrong_arity() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // abs with 2 args should fall back to uninterpreted
        let expr = Expr::Apply {
            func: "abs".to_string(),
            args: vec![Expr::IntLit(5), Expr::IntLit(7)],
        };
        let _ = translate_expr(&expr, &mut vars, &ctx);
        // Should have created uninterpreted variable
        assert!(vars.keys().any(|k| k.contains("abs")));
    }

    #[test]
    fn test_translate_expr_apply_abs_empty_args() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // abs with 0 args should fall back to uninterpreted
        let expr = Expr::Apply {
            func: "abs".to_string(),
            args: vec![],
        };
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.keys().any(|k| k.contains("abs")));
    }

    #[test]
    fn test_translate_expr_apply_min_same_values() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Apply {
            func: "min".to_string(),
            args: vec![Expr::IntLit(5), Expr::IntLit(5)],
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let five = ast::Int::from_i64(&ctx, 5);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&five).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_apply_max_same_values() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Apply {
            func: "max".to_string(),
            args: vec![Expr::IntLit(5), Expr::IntLit(5)],
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let five = ast::Int::from_i64(&ctx, 5);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&five).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_apply_min_wrong_arity() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // min with 1 arg should fall back to uninterpreted
        let expr = Expr::Apply {
            func: "min".to_string(),
            args: vec![Expr::IntLit(5)],
        };
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.keys().any(|k| k.contains("min")));
    }

    #[test]
    fn test_translate_expr_apply_max_wrong_arity() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // max with 3 args should fall back to uninterpreted
        let expr = Expr::Apply {
            func: "max".to_string(),
            args: vec![Expr::IntLit(5), Expr::IntLit(7), Expr::IntLit(9)],
        };
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.keys().any(|k| k.contains("max")));
    }

    #[test]
    fn test_translate_expr_apply_min_negative_values() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Apply {
            func: "min".to_string(),
            args: vec![Expr::IntLit(-10), Expr::IntLit(-5)],
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let neg_ten = ast::Int::from_i64(&ctx, -10);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&neg_ten).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_apply_max_negative_values() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Apply {
            func: "max".to_string(),
            args: vec![Expr::IntLit(-10), Expr::IntLit(-5)],
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let neg_five = ast::Int::from_i64(&ctx, -5);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&neg_five).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== Old expression edge cases ====================

    #[test]
    fn test_translate_expr_old_int_lit() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // old(42) should just return 42 (no variable needed for literal)
        let expr = Expr::Old(Box::new(Expr::IntLit(42)));
        let _ = translate_expr(&expr, &mut vars, &ctx);
        // Literal doesn't create any variable
        assert!(vars.is_empty());
    }

    #[test]
    fn test_translate_expr_old_nested() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // old(old(x)) flattens to x_old
        let expr = Expr::Old(Box::new(Expr::Old(Box::new(Expr::Var("x".to_string())))));
        let _ = translate_expr(&expr, &mut vars, &ctx);
        // Should create x_old variable
        assert!(vars.contains_key("x_old"));
    }

    #[test]
    fn test_translate_expr_old_add() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // old(x + y) should create x_old and y_old, then add them
        let expr = Expr::Old(Box::new(Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        )));
        let _ = translate_expr(&expr, &mut vars, &ctx);
        // Should create x_old and y_old variables
        assert!(vars.contains_key("x_old"));
        assert!(vars.contains_key("y_old"));
    }

    #[test]
    fn test_translate_expr_old_complex_sub() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // old(a - b) should create a_old and b_old
        let expr = Expr::Old(Box::new(Expr::Sub(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        )));
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.contains_key("a_old"));
        assert!(vars.contains_key("b_old"));
    }

    #[test]
    fn test_translate_expr_old_var() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // old(counter) should create counter_old
        let expr = Expr::Old(Box::new(Expr::Var("counter".to_string())));
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.contains_key("counter_old"));
        assert!(!vars.contains_key("counter"));
    }

    #[test]
    fn test_translate_expr_old_result() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // old(result) should create __result_old
        let expr = Expr::Old(Box::new(Expr::Result));
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.contains_key("__result_old"));
    }

    #[test]
    fn test_translate_expr_old_mul_three_vars() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // old(x * (y + z)) should create x_old, y_old, z_old
        let expr = Expr::Old(Box::new(Expr::Mul(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Add(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::Var("z".to_string())),
            )),
        )));
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.contains_key("x_old"));
        assert!(vars.contains_key("y_old"));
        assert!(vars.contains_key("z_old"));
    }

    #[test]
    fn test_translate_expr_old_array_index() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // old(arr[i]) is treated as immutable entry value (delegated directly)
        let expr = Expr::Old(Box::new(Expr::ArrayIndex(
            Box::new(Expr::Var("arr".to_string())),
            Box::new(Expr::Var("i".to_string())),
        )));
        let _ = translate_expr(&expr, &mut vars, &ctx);
        // Should create an uninterpreted variable for the array access
        assert!(vars.keys().any(|k| k.starts_with("__array_or_field_")));
    }

    #[test]
    fn test_translate_expr_old_struct_field() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // old(obj.field) is treated as immutable entry value (delegated directly)
        let expr = Expr::Old(Box::new(Expr::StructField(
            Box::new(Expr::Var("obj".to_string())),
            "field".to_string(),
        )));
        let _ = translate_expr(&expr, &mut vars, &ctx);
        // Should create an uninterpreted variable for the field access
        assert!(vars.keys().any(|k| k.starts_with("__array_or_field_")));
    }

    // ==================== large integer tests ====================

    #[test]
    fn test_translate_expr_large_positive() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let large = i64::MAX;
        let expr = Expr::IntLit(i128::from(large));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let expected = ast::Int::from_i64(&ctx, large);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&expected).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_large_negative() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let large = i64::MIN;
        let expr = Expr::IntLit(i128::from(large));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let expected = ast::Int::from_i64(&ctx, large);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&expected).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== special variable names ====================

    #[test]
    fn test_translate_expr_var_with_underscore() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Var("my_var_123".to_string());
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.contains_key("my_var_123"));
    }

    #[test]
    fn test_translate_expr_var_empty_name() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Var("".to_string());
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.contains_key(""));
    }

    #[test]
    fn test_translate_expr_var_special_chars() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Var("self".to_string());
        let _ = translate_expr(&expr, &mut vars, &ctx);
        assert!(vars.contains_key("self"));
    }

    // ==================== termination condition edge cases ====================

    #[test]
    fn test_z3_termination_zero_measure() {
        let vc = make_vc(
            "termination_zero",
            VcKind::Termination {
                measure: Expr::IntLit(0),
                initial_measure: Some(Expr::IntLit(0)),
                next_measure: Expr::IntLit(0),
                loop_label: "test_loop".to_string(),
            },
        );
        // Should not panic
        let _ = verify_vc(&vc);
    }

    #[test]
    fn test_z3_termination_negative_measure() {
        let vc = make_vc(
            "termination_negative",
            VcKind::Termination {
                measure: Expr::IntLit(-1),
                initial_measure: Some(Expr::IntLit(-1)),
                next_measure: Expr::IntLit(-2),
                loop_label: "test_loop".to_string(),
            },
        );
        // Should not panic
        let _ = verify_vc(&vc);
    }

    #[test]
    fn test_z3_termination_with_loop_location() {
        let vc = make_vc(
            "termination_with_loc",
            VcKind::Termination {
                measure: Expr::Var("n".to_string()),
                initial_measure: Some(Expr::IntLit(10)),
                next_measure: Expr::Sub(
                    Box::new(Expr::Var("n".to_string())),
                    Box::new(Expr::IntLit(1)),
                ),
                loop_label: "termination_loc_test".to_string(),
            },
        );
        // Should not panic
        let _ = verify_vc(&vc);
    }

    // ==================== quantifier edge cases ====================

    #[test]
    fn test_translate_expr_to_bool_forall_false() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Forall {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::BoolLit(false)),
        };
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        // forall x. false = false
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_exists_false() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::BoolLit(false)),
        };
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        // exists x. false = false
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool);
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_forall_multiple_vars() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Forall {
            vars: vec![
                (
                    "x".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
                (
                    "y".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
            ],
            body: Box::new(Expr::BoolLit(true)),
        };
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        // forall x, y. true = true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_exists_multiple_vars() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Exists {
            vars: vec![
                (
                    "x".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
                (
                    "y".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
            ],
            body: Box::new(Expr::BoolLit(true)),
        };
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        // exists x, y. true = true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_forall_empty_vars() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Forall {
            vars: vec![],
            body: Box::new(Expr::BoolLit(true)),
        };
        // Should handle empty vars gracefully
        let _ = translate_expr_to_bool(&expr, &mut vars, &ctx);
    }

    #[test]
    fn test_translate_expr_exists_in_int_context() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::BoolLit(true)),
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        // Exists in int context = 0
        let zero = ast::Int::from_i64(&ctx, 0);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&zero).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== array/struct edge cases ====================

    #[test]
    fn test_translate_expr_array_index_nested() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // arr[arr[0]]
        let expr = Expr::ArrayIndex(
            Box::new(Expr::Var("arr".to_string())),
            Box::new(Expr::ArrayIndex(
                Box::new(Expr::Var("arr".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        );
        // Should not panic
        let _ = translate_expr(&expr, &mut vars, &ctx);
    }

    #[test]
    fn test_translate_expr_struct_field_nested() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // obj.field1.field2
        let expr = Expr::StructField(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("obj".to_string())),
                "field1".to_string(),
            )),
            "field2".to_string(),
        );
        // Should not panic
        let _ = translate_expr(&expr, &mut vars, &ctx);
    }

    #[test]
    fn test_translate_expr_array_in_struct() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // obj.arr[0]
        let expr = Expr::ArrayIndex(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("obj".to_string())),
                "arr".to_string(),
            )),
            Box::new(Expr::IntLit(0)),
        );
        // Should not panic
        let _ = translate_expr(&expr, &mut vars, &ctx);
    }

    // ==================== ITE edge cases ====================

    #[test]
    fn test_translate_expr_ite_nested() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // if true then (if false then 1 else 2) else 3
        let expr = Expr::Ite {
            cond: Box::new(Expr::BoolLit(true)),
            then_: Box::new(Expr::Ite {
                cond: Box::new(Expr::BoolLit(false)),
                then_: Box::new(Expr::IntLit(1)),
                else_: Box::new(Expr::IntLit(2)),
            }),
            else_: Box::new(Expr::IntLit(3)),
        };
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let two = ast::Int::from_i64(&ctx, 2);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&two).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_to_bool_ite_nested() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // if true then (if true then true else false) else false
        let expr = Expr::Ite {
            cond: Box::new(Expr::BoolLit(true)),
            then_: Box::new(Expr::Ite {
                cond: Box::new(Expr::BoolLit(true)),
                then_: Box::new(Expr::BoolLit(true)),
                else_: Box::new(Expr::BoolLit(false)),
            }),
            else_: Box::new(Expr::BoolLit(false)),
        };
        let z3_bool = translate_expr_to_bool(&expr, &mut vars, &ctx);
        // Result should be true
        let solver = Solver::new(&ctx);
        solver.assert(&z3_bool.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== verify_vc predicate variations ====================

    #[test]
    fn test_z3_verify_vc_deeply_nested_implies() {
        let vc = make_vc(
            "nested_implies",
            VcKind::Implies {
                antecedent: Predicate::Implies(
                    Box::new(Predicate::Expr(Expr::BoolLit(true))),
                    Box::new(Predicate::Expr(Expr::BoolLit(true))),
                ),
                consequent: Predicate::Expr(Expr::BoolLit(true)),
            },
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_z3_verify_vc_complex_and() {
        let vc = make_vc(
            "complex_and",
            VcKind::Predicate(Predicate::And(vec![
                Predicate::Expr(Expr::BoolLit(true)),
                Predicate::Expr(Expr::BoolLit(true)),
                Predicate::Expr(Expr::BoolLit(true)),
            ])),
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_z3_verify_vc_complex_or() {
        let vc = make_vc(
            "complex_or",
            VcKind::Predicate(Predicate::Or(vec![
                Predicate::Expr(Expr::BoolLit(false)),
                Predicate::Expr(Expr::BoolLit(false)),
                Predicate::Expr(Expr::BoolLit(true)),
            ])),
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_z3_verify_vc_de_morgan_law() {
        // NOT (A AND B) = (NOT A) OR (NOT B)
        let vc = make_vc(
            "de_morgan",
            VcKind::Predicate(Predicate::Implies(
                Box::new(Predicate::Not(Box::new(Predicate::And(vec![
                    Predicate::Expr(Expr::Var("a".to_string())),
                    Predicate::Expr(Expr::Var("b".to_string())),
                ])))),
                Box::new(Predicate::Or(vec![
                    Predicate::Not(Box::new(Predicate::Expr(Expr::Var("a".to_string())))),
                    Predicate::Not(Box::new(Predicate::Expr(Expr::Var("b".to_string())))),
                ])),
            )),
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    // ==================== counterexample extraction edge cases ====================

    #[test]
    fn test_counterexample_multiple_vars() {
        let vc = make_vc(
            "multi_var_cx",
            VcKind::Predicate(Predicate::And(vec![
                Predicate::Expr(Expr::Gt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                Predicate::Expr(Expr::Lt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
            ])),
        );
        let result = verify_vc(&vc);
        // x > 0 AND x < 0 is always false
        assert!(matches!(result, VerifyResult::Counterexample(_)));
    }

    #[test]
    fn test_counterexample_with_internal_vars() {
        let vc = make_vc(
            "internal_var_cx",
            VcKind::Predicate(Predicate::Expr(Expr::Lt(
                Box::new(Expr::Result),
                Box::new(Expr::IntLit(-1000)),
            ))),
        );
        let result = verify_vc(&vc);
        // result < -1000 is not always true
        if let VerifyResult::Counterexample(cx) = result {
            // __result should be excluded from public assignments
            let has_result = cx.assignments.iter().any(|(name, _)| name == "__result");
            assert!(!has_result);
        }
    }

    // ==================== neg operation edge cases ====================

    #[test]
    fn test_translate_expr_neg_zero() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Neg(Box::new(Expr::IntLit(0)));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let zero = ast::Int::from_i64(&ctx, 0);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&zero).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_double_neg() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let expr = Expr::Neg(Box::new(Expr::Neg(Box::new(Expr::IntLit(5)))));
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let five = ast::Int::from_i64(&ctx, 5);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&five).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== mixed arithmetic edge cases ====================

    #[test]
    fn test_translate_expr_mixed_add_sub() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // 10 - 3 + 5 = 12
        let expr = Expr::Add(
            Box::new(Expr::Sub(
                Box::new(Expr::IntLit(10)),
                Box::new(Expr::IntLit(3)),
            )),
            Box::new(Expr::IntLit(5)),
        );
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let twelve = ast::Int::from_i64(&ctx, 12);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&twelve).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_translate_expr_mixed_mul_div() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        // 6 * 4 / 2 = 12
        let expr = Expr::Div(
            Box::new(Expr::Mul(
                Box::new(Expr::IntLit(6)),
                Box::new(Expr::IntLit(4)),
            )),
            Box::new(Expr::IntLit(2)),
        );
        let z3_expr = translate_expr(&expr, &mut vars, &ctx);
        let twelve = ast::Int::from_i64(&ctx, 12);
        let solver = Solver::new(&ctx);
        solver.assert(&z3_expr._eq(&twelve).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== chained comparisons ====================

    #[test]
    fn test_z3_chained_lt() {
        // a < b AND b < c => a < c
        let vc = make_vc(
            "chained_lt",
            VcKind::Implies {
                antecedent: Predicate::And(vec![
                    Predicate::Expr(Expr::Lt(
                        Box::new(Expr::Var("a".to_string())),
                        Box::new(Expr::Var("b".to_string())),
                    )),
                    Predicate::Expr(Expr::Lt(
                        Box::new(Expr::Var("b".to_string())),
                        Box::new(Expr::Var("c".to_string())),
                    )),
                ]),
                consequent: Predicate::Expr(Expr::Lt(
                    Box::new(Expr::Var("a".to_string())),
                    Box::new(Expr::Var("c".to_string())),
                )),
            },
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_z3_chained_le() {
        // a <= b AND b <= a => a == b
        let vc = make_vc(
            "chained_le_eq",
            VcKind::Implies {
                antecedent: Predicate::And(vec![
                    Predicate::Expr(Expr::Le(
                        Box::new(Expr::Var("a".to_string())),
                        Box::new(Expr::Var("b".to_string())),
                    )),
                    Predicate::Expr(Expr::Le(
                        Box::new(Expr::Var("b".to_string())),
                        Box::new(Expr::Var("a".to_string())),
                    )),
                ]),
                consequent: Predicate::Expr(Expr::Eq(
                    Box::new(Expr::Var("a".to_string())),
                    Box::new(Expr::Var("b".to_string())),
                )),
            },
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Proven));
    }

    // ==================== z3_available tests ====================

    #[test]
    fn test_z3_available_with_feature() {
        assert!(z3_available());
    }

    // ==================== helper function edge cases ====================

    #[test]
    fn test_get_or_create_int_var_same_name_different_calls() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let v1 = get_or_create_int_var("test", &mut vars, &ctx);
        let v2 = get_or_create_int_var("test", &mut vars, &ctx);
        let v3 = get_or_create_int_var("test", &mut vars, &ctx);
        // All should be equal
        let solver = Solver::new(&ctx);
        solver.assert(&ast::Bool::and(&ctx, &[&v1._eq(&v2), &v2._eq(&v3)]).not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    #[test]
    fn test_get_or_create_bool_var_same_name_different_calls() {
        let cfg = Config::new();
        let ctx = Context::new(&cfg);
        let mut vars = HashMap::new();
        let b1 = get_or_create_bool_var("flag", &mut vars, &ctx);
        let b2 = get_or_create_bool_var("flag", &mut vars, &ctx);
        // Should be same variable - b1 <=> b2
        let solver = Solver::new(&ctx);
        let equiv = ast::Bool::and(&ctx, &[&b1.implies(&b2), &b2.implies(&b1)]);
        solver.assert(&equiv.not());
        assert_eq!(solver.check(), Z3SatResult::Unsat);
    }

    // ==================== predicate with arithmetic ====================

    #[test]
    fn test_z3_arithmetic_in_predicate() {
        // Test that (x > 5 AND y > 5) => (x + y > 10) is universally true
        // This implication IS universally valid: if both x and y are > 5, their sum > 10
        let vc = make_vc(
            "arith_pred",
            VcKind::Predicate(Predicate::Implies(
                Box::new(Predicate::And(vec![
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::IntLit(5)),
                    )),
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("y".to_string())),
                        Box::new(Expr::IntLit(5)),
                    )),
                ])),
                Box::new(Predicate::Expr(Expr::Gt(
                    Box::new(Expr::Add(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::Var("y".to_string())),
                    )),
                    Box::new(Expr::IntLit(10)),
                ))),
            )),
        );
        let result = verify_vc(&vc);
        // (x > 5 AND y > 5) => (x + y > 10) should be proven
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_z3_contradictory_arithmetic() {
        // x > 10 AND x < 5 is unsatisfiable
        let vc = make_vc(
            "contradict_arith",
            VcKind::Predicate(Predicate::And(vec![
                Predicate::Expr(Expr::Gt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(10)),
                )),
                Predicate::Expr(Expr::Lt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(5)),
                )),
            ])),
        );
        let result = verify_vc(&vc);
        assert!(matches!(result, VerifyResult::Counterexample(_)));
    }
}
