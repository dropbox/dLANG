//! Conversion from Swift JSON types to local VC IR types.

use std::sync::Arc;

use crate::types::{
    Expr as VcExpr, FunctionSignature, FunctionVcs, Predicate, SourceSpan, VcId, VcKind, VcType,
    VerificationCondition,
};

use crate::error::VcBridgeResult;
#[cfg(test)]
use crate::json_types::SwiftParam;
use crate::json_types::{SwiftAutoVc, SwiftExpr, SwiftType, SwiftVcBundle};

/// Bounds used for overflow checking (legacy, assumes Int64).
///
/// These bounds model Swift's trapping signed integer arithmetic:
/// overflow occurs iff the mathematical result is outside the target
/// signed integer range.
#[must_use]
pub fn overflow_proxy_bounds() -> (i128, i128) {
    (i128::from(i64::MIN), i128::from(i64::MAX)) // INT64_MIN, INT64_MAX
}

/// Compute overflow bounds for a specific integer type.
///
/// Returns (min, max) bounds based on whether the type is signed and its bitwidth.
/// - Signed types: [-2^(bits-1), 2^(bits-1) - 1]
/// - Unsigned types: [0, 2^bits - 1]
#[must_use]
pub fn overflow_bounds_for_type(signed: bool, bits: u8) -> (i128, i128) {
    match (signed, bits) {
        // Signed types
        (true, 8) => (i128::from(i8::MIN), i128::from(i8::MAX)),
        (true, 16) => (i128::from(i16::MIN), i128::from(i16::MAX)),
        (true, 32) => (i128::from(i32::MIN), i128::from(i32::MAX)),
        // Unsigned types
        (false, 8) => (0, i128::from(u8::MAX)),
        (false, 16) => (0, i128::from(u16::MAX)),
        (false, 32) => (0, i128::from(u32::MAX)),
        (false, 64) => (0, i128::from(u64::MAX)),
        // Default to Int64 for unknown sizes (includes signed 64-bit)
        _ => (i128::from(i64::MIN), i128::from(i64::MAX)),
    }
}

/// Convert a Swift verification bundle to VC IR `FunctionVcs`.
///
/// # Errors
/// Returns an error if any expression, type, or condition in the bundle cannot be converted.
pub fn convert_bundle(bundle: &SwiftVcBundle) -> VcBridgeResult<FunctionVcs> {
    let mut vc_id_counter: u64 = 0;

    // Convert parameters
    let params: Vec<(String, VcType)> = bundle
        .parameters
        .iter()
        .map(|p| Ok((p.name.clone(), convert_type(&p.param_type)?)))
        .collect::<VcBridgeResult<Vec<_>>>()?;

    // Convert return type
    let return_type = match &bundle.return_type {
        Some(t) => convert_type(t)?,
        None => VcType::Tuple(vec![]), // Unit/Void
    };

    // Build signature
    let signature = FunctionSignature {
        name: bundle.function_name.clone(),
        params,
        return_type,
    };

    // Convert requires
    let requires: Vec<VerificationCondition> = bundle
        .requires
        .iter()
        .enumerate()
        .map(|(i, expr)| {
            let vc_id = VcId(vc_id_counter);
            vc_id_counter += 1;
            convert_to_vc(expr, vc_id, &format!("requires_{i}"), bundle)
        })
        .collect::<VcBridgeResult<Vec<_>>>()?;

    // Convert ensures
    let ensures: Vec<VerificationCondition> = bundle
        .ensures
        .iter()
        .enumerate()
        .map(|(i, expr)| {
            let vc_id = VcId(vc_id_counter);
            vc_id_counter += 1;
            convert_to_vc(expr, vc_id, &format!("ensures_{i}"), bundle)
        })
        .collect::<VcBridgeResult<Vec<_>>>()?;

    // Convert loop invariants
    let loop_invariants: Vec<VerificationCondition> = bundle
        .invariants
        .iter()
        .enumerate()
        .map(|(i, expr)| {
            let vc_id = VcId(vc_id_counter);
            vc_id_counter += 1;
            convert_to_vc(expr, vc_id, &format!("invariant_{i}"), bundle)
        })
        .collect::<VcBridgeResult<Vec<_>>>()?;

    // Convert auto-VCs to assertions
    let assertions: Vec<VerificationCondition> = bundle
        .auto_vcs
        .iter()
        .map(|auto_vc| {
            let vc_id = VcId(vc_id_counter);
            vc_id_counter += 1;
            convert_auto_vc(auto_vc, vc_id, bundle)
        })
        .collect::<VcBridgeResult<Vec<_>>>()?;

    Ok(FunctionVcs {
        name: bundle.function_name.clone(),
        signature,
        requires,
        ensures,
        loop_invariants,
        assertions,
        termination: None, // Termination proofs not yet supported
    })
}

/// Convert a Swift type to VC IR type.
///
/// # Errors
/// Returns an error if the Swift type cannot be represented in VC IR.
pub fn convert_type(swift_type: &SwiftType) -> VcBridgeResult<VcType> {
    match swift_type {
        SwiftType::Int { signed, bits } => Ok(VcType::Int {
            signed: *signed,
            bits: *bits,
        }),

        SwiftType::Bool => Ok(VcType::Bool),

        SwiftType::Float { bits } => Ok(VcType::Float { bits: *bits }),

        SwiftType::Optional { inner } => {
            // Model Optional as a struct with (hasValue: Bool, value: T)
            let inner_type = convert_type(inner)?;
            Ok(VcType::Struct {
                name: "Optional".to_string(),
                fields: vec![
                    ("hasValue".to_string(), VcType::Bool),
                    ("value".to_string(), inner_type),
                ],
            })
        }

        SwiftType::Array { element } => {
            let elem_type = convert_type(element)?;
            Ok(VcType::Array {
                elem: Box::new(elem_type),
                len: None,
            })
        }

        SwiftType::Pointer { mutable, pointee } => {
            let inner_type = convert_type(pointee)?;
            Ok(VcType::Ref {
                mutable: *mutable,
                inner: Box::new(inner_type),
            })
        }

        SwiftType::Void => Ok(VcType::Tuple(vec![])),

        SwiftType::Named { name } => Ok(VcType::Abstract(name.clone())),
    }
}

/// Convert a Swift expression to VC IR expression.
///
/// # Errors
/// Returns an error if the Swift expression cannot be represented in VC IR.
#[allow(clippy::too_many_lines)]
pub fn convert_expr(expr: &SwiftExpr) -> VcBridgeResult<VcExpr> {
    match expr {
        // Literals
        SwiftExpr::IntLit { value } => Ok(VcExpr::IntLit(i128::from(*value))),

        SwiftExpr::BoolLit { value } => Ok(VcExpr::BoolLit(*value)),

        SwiftExpr::NilLit => Ok(VcExpr::NilLit),

        // References
        SwiftExpr::ParamRef { name, .. } => Ok(VcExpr::Var(name.clone())),

        SwiftExpr::ResultRef => Ok(VcExpr::Result),

        // Arithmetic binary ops
        SwiftExpr::Add { lhs, rhs } => Ok(VcExpr::Add(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        SwiftExpr::Sub { lhs, rhs } => Ok(VcExpr::Sub(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        SwiftExpr::Mul { lhs, rhs } => Ok(VcExpr::Mul(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        SwiftExpr::Div { lhs, rhs } => Ok(VcExpr::Div(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        SwiftExpr::Mod { lhs, rhs } => Ok(VcExpr::Rem(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        // Comparison binary ops
        // Special case: expr == nil becomes expr.hasValue == false
        SwiftExpr::Eq { lhs, rhs } => {
            if matches!(rhs.as_ref(), SwiftExpr::NilLit) {
                // expr == nil -> expr.hasValue == false
                let expr = convert_expr(lhs)?;
                let has_value = VcExpr::StructField(Box::new(expr), "hasValue".to_string());
                Ok(VcExpr::Eq(
                    Box::new(has_value),
                    Box::new(VcExpr::BoolLit(false)),
                ))
            } else if matches!(lhs.as_ref(), SwiftExpr::NilLit) {
                // nil == expr -> expr.hasValue == false
                let expr = convert_expr(rhs)?;
                let has_value = VcExpr::StructField(Box::new(expr), "hasValue".to_string());
                Ok(VcExpr::Eq(
                    Box::new(has_value),
                    Box::new(VcExpr::BoolLit(false)),
                ))
            } else {
                Ok(VcExpr::Eq(
                    Box::new(convert_expr(lhs)?),
                    Box::new(convert_expr(rhs)?),
                ))
            }
        }

        // Special case: expr != nil becomes expr.hasValue == true
        SwiftExpr::Ne { lhs, rhs } => {
            if matches!(rhs.as_ref(), SwiftExpr::NilLit) {
                // expr != nil -> expr.hasValue == true
                let expr = convert_expr(lhs)?;
                let has_value = VcExpr::StructField(Box::new(expr), "hasValue".to_string());
                Ok(VcExpr::Eq(
                    Box::new(has_value),
                    Box::new(VcExpr::BoolLit(true)),
                ))
            } else if matches!(lhs.as_ref(), SwiftExpr::NilLit) {
                // nil != expr -> expr.hasValue == true
                let expr = convert_expr(rhs)?;
                let has_value = VcExpr::StructField(Box::new(expr), "hasValue".to_string());
                Ok(VcExpr::Eq(
                    Box::new(has_value),
                    Box::new(VcExpr::BoolLit(true)),
                ))
            } else {
                Ok(VcExpr::Ne(
                    Box::new(convert_expr(lhs)?),
                    Box::new(convert_expr(rhs)?),
                ))
            }
        }

        SwiftExpr::Lt { lhs, rhs } => Ok(VcExpr::Lt(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        SwiftExpr::Le { lhs, rhs } => Ok(VcExpr::Le(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        SwiftExpr::Gt { lhs, rhs } => Ok(VcExpr::Gt(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        SwiftExpr::Ge { lhs, rhs } => Ok(VcExpr::Ge(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        // Logical binary ops
        SwiftExpr::And { lhs, rhs } => Ok(VcExpr::And(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        SwiftExpr::Or { lhs, rhs } => Ok(VcExpr::Or(
            Box::new(convert_expr(lhs)?),
            Box::new(convert_expr(rhs)?),
        )),

        // Unary ops
        SwiftExpr::Neg { operand } => Ok(VcExpr::Neg(Box::new(convert_expr(operand)?))),

        SwiftExpr::Not { operand } => Ok(VcExpr::Not(Box::new(convert_expr(operand)?))),

        // Advanced
        SwiftExpr::Old { expr } => Ok(VcExpr::Old(Box::new(convert_expr(expr)?))),

        SwiftExpr::Index { base, index } => Ok(VcExpr::ArrayIndex(
            Box::new(convert_expr(base)?),
            Box::new(convert_expr(index)?),
        )),

        SwiftExpr::Field { base, field } => Ok(VcExpr::StructField(
            Box::new(convert_expr(base)?),
            field.clone(),
        )),

        SwiftExpr::Call { func, args } => {
            let converted_args: Vec<VcExpr> = args
                .iter()
                .map(convert_expr)
                .collect::<VcBridgeResult<Vec<_>>>()?;
            Ok(VcExpr::Apply {
                func: func.clone(),
                args: converted_args,
            })
        }

        SwiftExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => Ok(VcExpr::Ite {
            cond: Box::new(convert_expr(cond)?),
            then_: Box::new(convert_expr(then_expr)?),
            else_: Box::new(convert_expr(else_expr)?),
        }),

        SwiftExpr::Forall { vars, body } => {
            let converted_vars: Vec<(String, VcType)> = vars
                .iter()
                .map(|(name, ty)| Ok((name.clone(), convert_type(ty)?)))
                .collect::<VcBridgeResult<Vec<_>>>()?;
            Ok(VcExpr::Forall {
                vars: converted_vars,
                body: Box::new(convert_expr(body)?),
            })
        }

        SwiftExpr::Exists { vars, body } => {
            let converted_vars: Vec<(String, VcType)> = vars
                .iter()
                .map(|(name, ty)| Ok((name.clone(), convert_type(ty)?)))
                .collect::<VcBridgeResult<Vec<_>>>()?;
            Ok(VcExpr::Exists {
                vars: converted_vars,
                body: Box::new(convert_expr(body)?),
            })
        }

        // Type literals - represent as symbolic constants
        SwiftExpr::TypeLit { ty } => Ok(VcExpr::Var(format!("type_{ty}"))),

        // String literals - represent as symbolic constants
        SwiftExpr::StringLit { value } => {
            Ok(VcExpr::Var(format!("str_{}", value.replace('-', "_"))))
        }
    }
}

/// Convert a Swift expression to a `VerificationCondition`.
fn convert_to_vc(
    expr: &SwiftExpr,
    id: VcId,
    name: &str,
    bundle: &SwiftVcBundle,
) -> VcBridgeResult<VerificationCondition> {
    let vc_expr = convert_expr(expr)?;
    let predicate = Predicate::Expr(vc_expr);

    Ok(VerificationCondition {
        id,
        name: name.to_string(),
        span: make_source_span(&bundle.source_file, bundle.source_line, 0),
        condition: VcKind::Predicate(predicate),
        preferred_backend: None,
    })
}

/// Convert an auto-VC to a `VerificationCondition`.
#[allow(clippy::too_many_lines)]
fn convert_auto_vc(
    auto_vc: &SwiftAutoVc,
    id: VcId,
    bundle: &SwiftVcBundle,
) -> VcBridgeResult<VerificationCondition> {
    match auto_vc {
        SwiftAutoVc::Overflow {
            description,
            operands,
            operation,
            source_line,
            path_condition,
            signed,
            bits,
            ..
        } => {
            // For overflow, we need to check that the result of the operation
            // stays within the integer type's bounds.
            //
            // Signed types: [INT_MIN, INT_MAX] where INT_MIN = -2^(bits-1), INT_MAX = 2^(bits-1) - 1
            // Unsigned types: [0, UINT_MAX] where UINT_MAX = 2^bits - 1
            //
            // We generate a condition based on the operation:
            // - add: bound_min <= lhs + rhs <= bound_max
            // - sub: bound_min <= lhs - rhs <= bound_max
            // - mul: bound_min <= lhs * rhs <= bound_max

            let operand_exprs: Vec<VcExpr> = operands
                .iter()
                .map(convert_expr)
                .collect::<VcBridgeResult<Vec<_>>>()?;

            // Build the result expression based on operation
            let result_expr = if operand_exprs.len() >= 2 {
                let lhs = operand_exprs[0].clone();
                let rhs = operand_exprs[1].clone();
                match operation.as_str() {
                    "add" => VcExpr::Add(Box::new(lhs), Box::new(rhs)),
                    "sub" => VcExpr::Sub(Box::new(lhs), Box::new(rhs)),
                    "mul" => VcExpr::Mul(Box::new(lhs), Box::new(rhs)),
                    "div" => VcExpr::Div(Box::new(lhs), Box::new(rhs)),
                    "mod" => VcExpr::Rem(Box::new(lhs), Box::new(rhs)),
                    _ => {
                        // Unknown operation - use placeholder
                        return Ok(VerificationCondition {
                            id,
                            name: description.clone(),
                            span: make_auto_vc_span(*source_line, bundle),
                            condition: VcKind::Predicate(Predicate::t()),
                            preferred_backend: None,
                        });
                    }
                }
            } else if operand_exprs.len() == 1 && operation == "neg" {
                // Unary negation: -x
                // Overflow occurs when x == INT_MIN because -INT_MIN overflows
                let operand = operand_exprs[0].clone();
                VcExpr::Neg(Box::new(operand))
            } else {
                // Not enough operands - use placeholder
                return Ok(VerificationCondition {
                    id,
                    name: description.clone(),
                    span: make_auto_vc_span(*source_line, bundle),
                    condition: VcKind::Predicate(Predicate::t()),
                    preferred_backend: None,
                });
            };

            // Overflow check: prove the result stays within the target integer range.
            //
            // Note: For multiplication this is non-linear; we opportunistically prove
            // safety via interval analysis elsewhere and otherwise may get Unknown.
            let (bound_min_i128, bound_max_i128) = overflow_bounds_for_type(*signed, *bits);
            let bound_min = VcExpr::IntLit(bound_min_i128);
            let bound_max = VcExpr::IntLit(bound_max_i128);

            // result >= bound_min
            let lower_bound = VcExpr::Ge(Box::new(result_expr.clone()), Box::new(bound_min));
            // result <= bound_max
            let upper_bound = VcExpr::Le(Box::new(result_expr), Box::new(bound_max));
            // Combined: no overflow (within integer bounds)
            let no_overflow = VcExpr::And(Box::new(lower_bound), Box::new(upper_bound));

            // If there's a path condition, the VC is: path_condition => no_overflow
            let condition = if let Some(path_cond) = path_condition {
                let path_expr = convert_expr(path_cond)?;
                VcKind::Implies {
                    antecedent: Predicate::Expr(path_expr),
                    consequent: Predicate::Expr(no_overflow),
                }
            } else {
                VcKind::Predicate(Predicate::Expr(no_overflow))
            };

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition,
                preferred_backend: None,
            })
        }

        SwiftAutoVc::DivByZero {
            divisor,
            description,
            source_line,
            ..
        } => {
            // Division by zero: divisor != 0
            let divisor_expr = convert_expr(divisor)?;
            let zero = VcExpr::IntLit(0);
            let condition = VcExpr::Ne(Box::new(divisor_expr), Box::new(zero));
            let predicate = Predicate::Expr(condition);

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Predicate(predicate),
                preferred_backend: None,
            })
        }

        SwiftAutoVc::BoundsCheck {
            index,
            length,
            description,
            source_line,
            ..
        } => {
            // Bounds check: 0 <= index < length
            let index_expr = convert_expr(index)?;
            let length_expr = convert_expr(length)?;
            let zero = VcExpr::IntLit(0);

            // index >= 0
            let lower_bound = VcExpr::Ge(Box::new(index_expr.clone()), Box::new(zero));
            // index < length
            let upper_bound = VcExpr::Lt(Box::new(index_expr), Box::new(length_expr));
            // Combined
            let condition = VcExpr::And(Box::new(lower_bound), Box::new(upper_bound));
            let predicate = Predicate::Expr(condition);

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Predicate(predicate),
                preferred_backend: None,
            })
        }

        SwiftAutoVc::NilCheck {
            value,
            description,
            source_line,
            ..
        } => {
            // Nil check: value is not nil (hasValue == true for Optional model)
            let value_expr = convert_expr(value)?;
            // For our Optional model: value.hasValue == true
            let has_value = VcExpr::StructField(Box::new(value_expr), "hasValue".to_string());
            let predicate = Predicate::Expr(has_value);

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Predicate(predicate),
                preferred_backend: None,
            })
        }

        SwiftAutoVc::CastCheck {
            value,
            target_type,
            description,
            source_line,
            ..
        } => {
            // Cast check: value must be of the target type
            // We model this as is_type(value, target_type) which represents
            // a runtime type check that the value can be cast to target_type.
            // The type name is encoded as a variable for SMT solver consumption.
            let value_expr = convert_expr(value)?;
            // Sanitize type name for use as identifier
            let type_var = VcExpr::Var(format!(
                "type_{}",
                target_type.replace([' ', '<', '>', ',', '(', ')', '.'], "_")
            ));
            let type_pred = VcExpr::Apply {
                func: "is_type".to_string(),
                args: vec![value_expr, type_var],
            };
            let predicate = Predicate::Expr(type_pred);

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Predicate(predicate),
                preferred_backend: None,
            })
        }

        SwiftAutoVc::CondFail {
            condition,
            description,
            source_line,
            ..
        } => {
            // cond_fail: condition must hold to avoid failure
            let condition_expr = convert_expr(condition)?;
            let predicate = Predicate::Expr(condition_expr);

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Predicate(predicate),
                preferred_backend: None,
            })
        }

        SwiftAutoVc::CallPrecondition {
            condition,
            description,
            source_line,
            ..
        } => {
            // Call precondition: the callee's @_requires must be satisfied
            let condition_expr = convert_expr(condition)?;
            let predicate = Predicate::Expr(condition_expr);

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Predicate(predicate),
                preferred_backend: None,
            })
        }

        SwiftAutoVc::Termination {
            loop_label,
            measure,
            initial_measure,
            next_measure,
            description,
            source_line,
            ..
        } => {
            // Termination: measure decreases and stays non-negative
            let measure_expr = convert_expr(measure)?;
            let initial_expr = initial_measure.as_ref().map(convert_expr).transpose()?;
            let next_expr = convert_expr(next_measure)?;

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Termination {
                    measure: measure_expr,
                    initial_measure: initial_expr,
                    next_measure: next_expr,
                    loop_label: loop_label.clone(),
                },
                preferred_backend: None,
            })
        }

        SwiftAutoVc::RecursiveTermination {
            function_name,
            measure,
            recursive_measure,
            description,
            source_line,
            ..
        } => {
            // Recursive termination: measure decreases on each recursive call
            // Reuses VcKind::Termination with function_name as the "loop_label"
            let measure_expr = convert_expr(measure)?;
            let recursive_expr = convert_expr(recursive_measure)?;

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Termination {
                    measure: measure_expr.clone(),
                    initial_measure: Some(measure_expr), // Initial is same as current for recursion
                    next_measure: recursive_expr,
                    loop_label: function_name.clone(), // Use function name as label
                },
                preferred_backend: None,
            })
        }

        SwiftAutoVc::MutualRecursiveTermination {
            function_cycle,
            decreasing_param,
            description,
            source_line,
            ..
        } => {
            // Mutual recursive termination: measure decreases across the call cycle
            // Similar to RecursiveTermination but documents the cycle
            // The actual VC just asserts that the measure is non-negative (well-founded)
            let measure_expr = VcExpr::Var(decreasing_param.clone());

            Ok(VerificationCondition {
                id,
                name: format!("{} (cycle: {})", description, function_cycle.join(" -> ")),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Termination {
                    measure: measure_expr.clone(),
                    initial_measure: Some(measure_expr), // Initial is the entry measure
                    next_measure: VcExpr::Sub(
                        Box::new(VcExpr::Var(decreasing_param.clone())),
                        Box::new(VcExpr::IntLit(1)), // Decreases by at least 1 across cycle
                    ),
                    loop_label: function_cycle.join("_"),
                },
                preferred_backend: None,
            })
        }

        SwiftAutoVc::LexicographicTermination {
            function_name,
            measure_params,
            call_site_decreases,
            description,
            source_line,
            ..
        } => {
            // Lexicographic termination: tuple of parameters decreases lexicographically
            // We express this as a termination VC where:
            // - measure is a tuple representation (first param has highest priority)
            // - The VC documents that at each call site, some param decreases
            //   with all earlier params non-increasing

            // Build the measure as the first param (highest priority in lexicographic order)
            let measure_expr = measure_params
                .first()
                .map_or(VcExpr::IntLit(0), |p| VcExpr::Var(p.clone()));

            // Build a description that includes all call site info
            let call_info: Vec<String> = call_site_decreases
                .iter()
                .map(|(site, idx)| format!("{site}: param {idx} decreases"))
                .collect();

            Ok(VerificationCondition {
                id,
                name: format!("{} [{}]", description, call_info.join("; ")),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Termination {
                    measure: measure_expr.clone(),
                    initial_measure: Some(measure_expr),
                    next_measure: VcExpr::Sub(
                        Box::new(VcExpr::Var(
                            measure_params.first().cloned().unwrap_or_default(),
                        )),
                        Box::new(VcExpr::IntLit(1)), // Simplified: first param decreases eventually
                    ),
                    loop_label: function_name.clone(),
                },
                preferred_backend: None,
            })
        }

        SwiftAutoVc::LexicographicMutualRecursiveTermination {
            function_cycle,
            measure_params,
            description,
            source_line,
            ..
        } => {
            // Lexicographic mutual recursive termination: tuple of parameters decreases
            // lexicographically across the cycle of mutually recursive functions.
            // Similar to LexicographicTermination but for function cycles instead of
            // self-recursion.

            // Build the measure as the first param (highest priority in lexicographic order)
            let measure_expr = measure_params
                .first()
                .map_or(VcExpr::IntLit(0), |p| VcExpr::Var(p.clone()));

            // Build a unique loop label from the cycle
            let cycle_label = function_cycle.join("_");

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition: VcKind::Termination {
                    measure: measure_expr.clone(),
                    initial_measure: Some(measure_expr),
                    next_measure: VcExpr::Sub(
                        Box::new(VcExpr::Var(
                            measure_params.first().cloned().unwrap_or_default(),
                        )),
                        Box::new(VcExpr::IntLit(1)), // Simplified: first param decreases eventually across cycle
                    ),
                    loop_label: cycle_label,
                },
                preferred_backend: None,
            })
        }

        SwiftAutoVc::StateInvariant {
            invariant,
            description,
            path_condition,
            source_line,
            ..
        } => {
            // State invariant: verify the invariant holds after mutation
            // The invariant is converted to a predicate that must hold
            let invariant_expr = convert_expr(invariant)?;

            // If there's a path condition, the VC is: path_condition => invariant
            let condition = if let Some(path_cond) = path_condition {
                let path_expr = convert_expr(path_cond)?;
                VcKind::Implies {
                    antecedent: Predicate::Expr(path_expr),
                    consequent: Predicate::Expr(invariant_expr),
                }
            } else {
                VcKind::Predicate(Predicate::Expr(invariant_expr))
            };

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition,
                preferred_backend: None,
            })
        }

        SwiftAutoVc::TypeInvariant {
            invariant,
            description,
            path_condition,
            source_line,
            ..
        } => {
            // Type-level invariant: verify the invariant holds after any mutation
            // to an instance of the type, regardless of which method performs the mutation.
            let invariant_expr = convert_expr(invariant)?;

            // If there's a path condition, the VC is: path_condition => invariant
            let condition = if let Some(path_cond) = path_condition {
                let path_expr = convert_expr(path_cond)?;
                VcKind::Implies {
                    antecedent: Predicate::Expr(path_expr),
                    consequent: Predicate::Expr(invariant_expr),
                }
            } else {
                VcKind::Predicate(Predicate::Expr(invariant_expr))
            };

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition,
                preferred_backend: None,
            })
        }

        SwiftAutoVc::MethodCallStateEffect {
            invariant,
            description,
            path_condition,
            source_line,
            ..
        } => {
            // Cross-method state effect: verify the invariant holds after calling
            // a method that may modify state. This is similar to TypeInvariant but
            // triggered by method calls rather than direct mutations.
            let invariant_expr = convert_expr(invariant)?;

            // If there's a path condition, the VC is: path_condition => invariant
            let condition = if let Some(path_cond) = path_condition {
                let path_expr = convert_expr(path_cond)?;
                VcKind::Implies {
                    antecedent: Predicate::Expr(path_expr),
                    consequent: Predicate::Expr(invariant_expr),
                }
            } else {
                VcKind::Predicate(Predicate::Expr(invariant_expr))
            };

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition,
                preferred_backend: None,
            })
        }

        SwiftAutoVc::ShiftOverflow {
            shift_amount,
            bits,
            description,
            path_condition,
            source_line,
            ..
        } => {
            // Shift overflow: verify 0 <= shift_amount < bits
            // The condition we need to prove: shift_amount >= 0 AND shift_amount < bits
            let shift_expr = convert_expr(shift_amount)?;
            let bits_lit = VcExpr::IntLit(i128::from(*bits));
            let zero_lit = VcExpr::IntLit(0_i128);

            // Build: shift_amount >= 0 AND shift_amount < bits
            let lower_bound = VcExpr::Ge(Box::new(shift_expr.clone()), Box::new(zero_lit));
            let upper_bound = VcExpr::Lt(Box::new(shift_expr), Box::new(bits_lit));
            let valid_shift = VcExpr::And(Box::new(lower_bound), Box::new(upper_bound));

            // If there's a path condition, the VC is: path_condition => valid_shift
            let condition = if let Some(path_cond) = path_condition {
                let path_expr = convert_expr(path_cond)?;
                VcKind::Implies {
                    antecedent: Predicate::Expr(path_expr),
                    consequent: Predicate::Expr(valid_shift),
                }
            } else {
                VcKind::Predicate(Predicate::Expr(valid_shift))
            };

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition,
                preferred_backend: None,
            })
        }

        SwiftAutoVc::UnownedAccess {
            reference,
            description,
            path_condition,
            source_line,
            ..
        } => {
            // UnownedAccess: verify the unowned reference is still valid (object not deallocated).
            // Since we cannot directly verify object lifetime, we represent this as:
            // - The reference being non-nil/valid
            // - This will typically return UNKNOWN without user-provided preconditions
            //
            // The condition is: reference is valid (symbolically: unowned_valid(reference))
            let ref_expr = convert_expr(reference)?;
            let valid_cond = VcExpr::Apply {
                func: "unowned_ref_valid".to_string(),
                args: vec![ref_expr],
            };

            // If there's a path condition, the VC is: path_condition => valid
            let condition = if let Some(path_cond) = path_condition {
                let path_expr = convert_expr(path_cond)?;
                VcKind::Implies {
                    antecedent: Predicate::Expr(path_expr),
                    consequent: Predicate::Expr(valid_cond),
                }
            } else {
                VcKind::Predicate(Predicate::Expr(valid_cond))
            };

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition,
                preferred_backend: None,
            })
        }

        SwiftAutoVc::ActorIsolationCrossing {
            callee_name,
            caller_isolation,
            callee_isolation,
            description,
            path_condition,
            source_line,
            ..
        } => {
            // ActorIsolationCrossing: represents a call that crosses actor boundaries.
            // Since Swift's compiler already enforces actor isolation at compile time,
            // this VC primarily serves as documentation/auditing of where crossings occur.
            //
            // The condition is: actor_crossing_safe(caller, callee, callee_name)
            // This is an uninterpreted function that will return UNKNOWN by default,
            // but could be extended with FFI-specific rules or user annotations.
            let crossing_cond = VcExpr::Apply {
                func: "actor_crossing_safe".to_string(),
                args: vec![
                    VcExpr::Var(caller_isolation.clone()),
                    VcExpr::Var(callee_isolation.clone()),
                    VcExpr::Var(callee_name.clone()),
                ],
            };

            // If there's a path condition, the VC is: path_condition => crossing_safe
            let condition = if let Some(path_cond) = path_condition {
                let path_expr = convert_expr(path_cond)?;
                VcKind::Implies {
                    antecedent: Predicate::Expr(path_expr),
                    consequent: Predicate::Expr(crossing_cond),
                }
            } else {
                VcKind::Predicate(Predicate::Expr(crossing_cond))
            };

            Ok(VerificationCondition {
                id,
                name: description.clone(),
                span: make_auto_vc_span(*source_line, bundle),
                condition,
                preferred_backend: None,
            })
        }
    }
}

/// Create a `SourceSpan` from file/line info.
fn make_source_span(file: &str, line: u32, col: u32) -> SourceSpan {
    SourceSpan {
        file: Arc::from(file),
        line_start: line,
        line_end: line,
        col_start: col,
        col_end: col,
    }
}

/// Create a source span for an auto-VC, using the VC's source line if available,
/// otherwise falling back to the bundle's source line.
fn make_auto_vc_span(source_line: u32, bundle: &SwiftVcBundle) -> SourceSpan {
    let line = if source_line > 0 {
        source_line
    } else {
        bundle.source_line
    };
    make_source_span(&bundle.source_file, line, 0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_convert_int_type() {
        let swift_type = SwiftType::Int {
            signed: true,
            bits: 64,
        };
        let vc_type = convert_type(&swift_type).unwrap();
        assert!(matches!(
            vc_type,
            VcType::Int {
                signed: true,
                bits: 64
            }
        ));
    }

    #[test]
    fn test_convert_bool_type() {
        let swift_type = SwiftType::Bool;
        let vc_type = convert_type(&swift_type).unwrap();
        assert!(matches!(vc_type, VcType::Bool));
    }

    #[test]
    fn test_convert_int_literal() {
        let expr = SwiftExpr::IntLit { value: 42 };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::IntLit(42)));
    }

    #[test]
    fn test_convert_bool_literal() {
        let expr = SwiftExpr::BoolLit { value: true };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::BoolLit(true)));
    }

    #[test]
    fn test_convert_param_ref() {
        let expr = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Var(ref name) if name == "x"));
    }

    #[test]
    fn test_convert_result_ref() {
        let expr = SwiftExpr::ResultRef;
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Result));
    }

    #[test]
    fn test_convert_add() {
        let expr = SwiftExpr::Add {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Add(_, _)));
    }

    #[test]
    fn test_convert_comparison() {
        let expr = SwiftExpr::Gt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Gt(_, _)));
    }

    #[test]
    fn test_convert_logical_and() {
        let expr = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            rhs: Box::new(SwiftExpr::Lt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 100 }),
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::And(_, _)));
    }

    #[test]
    fn test_convert_simple_bundle() {
        let bundle = SwiftVcBundle {
            function_name: "increment".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 10,
            source_column: 1,
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
                index: 0,
            }],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 64,
            }),
            requires: vec![SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }],
            ensures: vec![SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
            }],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let fvcs = convert_bundle(&bundle).unwrap();

        assert_eq!(fvcs.name, "increment");
        assert_eq!(fvcs.signature.params.len(), 1);
        assert_eq!(fvcs.signature.params[0].0, "x");
        assert_eq!(fvcs.requires.len(), 1);
        assert_eq!(fvcs.ensures.len(), 1);
    }

    #[test]
    fn test_overflow_bounds_for_type_signed() {
        // Test signed integer bounds
        assert_eq!(
            overflow_bounds_for_type(true, 8),
            (i128::from(i8::MIN), i128::from(i8::MAX))
        );
        assert_eq!(
            overflow_bounds_for_type(true, 16),
            (i128::from(i16::MIN), i128::from(i16::MAX))
        );
        assert_eq!(
            overflow_bounds_for_type(true, 32),
            (i128::from(i32::MIN), i128::from(i32::MAX))
        );
        assert_eq!(
            overflow_bounds_for_type(true, 64),
            (i128::from(i64::MIN), i128::from(i64::MAX))
        );
    }

    #[test]
    fn test_overflow_bounds_for_type_unsigned() {
        // Test unsigned integer bounds
        assert_eq!(overflow_bounds_for_type(false, 8), (0, i128::from(u8::MAX)));
        assert_eq!(
            overflow_bounds_for_type(false, 16),
            (0, i128::from(u16::MAX))
        );
        assert_eq!(
            overflow_bounds_for_type(false, 32),
            (0, i128::from(u32::MAX))
        );
        assert_eq!(
            overflow_bounds_for_type(false, 64),
            (0, i128::from(u64::MAX))
        );
    }

    #[test]
    fn test_overflow_bounds_for_type_concrete_values() {
        // Verify concrete values for Int8
        let (min, max) = overflow_bounds_for_type(true, 8);
        assert_eq!(min, -128);
        assert_eq!(max, 127);

        // Verify concrete values for UInt8
        let (min, max) = overflow_bounds_for_type(false, 8);
        assert_eq!(min, 0);
        assert_eq!(max, 255);

        // Verify concrete values for Int32
        let (min, max) = overflow_bounds_for_type(true, 32);
        assert_eq!(min, -2_147_483_648);
        assert_eq!(max, 2_147_483_647);
    }

    #[test]
    fn test_overflow_bounds_for_type_unknown_size() {
        // Unknown bit sizes should default to Int64
        let (min, max) = overflow_bounds_for_type(true, 128);
        assert_eq!(min, i128::from(i64::MIN));
        assert_eq!(max, i128::from(i64::MAX));
    }

    // ============================================================
    // Additional type conversion tests
    // ============================================================

    #[test]
    fn test_convert_float_type() {
        let swift_type = SwiftType::Float { bits: 64 };
        let vc_type = convert_type(&swift_type).unwrap();
        assert!(matches!(vc_type, VcType::Float { bits: 64 }));
    }

    #[test]
    fn test_convert_float32_type() {
        let swift_type = SwiftType::Float { bits: 32 };
        let vc_type = convert_type(&swift_type).unwrap();
        assert!(matches!(vc_type, VcType::Float { bits: 32 }));
    }

    #[test]
    fn test_convert_optional_type() {
        let swift_type = SwiftType::Optional {
            inner: Box::new(SwiftType::Int {
                signed: true,
                bits: 64,
            }),
        };
        let vc_type = convert_type(&swift_type).unwrap();
        match vc_type {
            VcType::Struct { name, fields } => {
                assert_eq!(name, "Optional");
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "hasValue");
                assert!(matches!(fields[0].1, VcType::Bool));
                assert_eq!(fields[1].0, "value");
            }
            _ => panic!("Expected Struct type for Optional"),
        }
    }

    #[test]
    fn test_convert_array_type() {
        let swift_type = SwiftType::Array {
            element: Box::new(SwiftType::Bool),
        };
        let vc_type = convert_type(&swift_type).unwrap();
        match vc_type {
            VcType::Array { elem, len } => {
                assert!(matches!(elem.as_ref(), VcType::Bool));
                assert!(len.is_none());
            }
            _ => panic!("Expected Array type"),
        }
    }

    #[test]
    fn test_convert_pointer_type_mutable() {
        let swift_type = SwiftType::Pointer {
            mutable: true,
            pointee: Box::new(SwiftType::Int {
                signed: true,
                bits: 32,
            }),
        };
        let vc_type = convert_type(&swift_type).unwrap();
        match vc_type {
            VcType::Ref { mutable, inner } => {
                assert!(mutable);
                assert!(matches!(
                    inner.as_ref(),
                    VcType::Int {
                        signed: true,
                        bits: 32
                    }
                ));
            }
            _ => panic!("Expected Ref type for Pointer"),
        }
    }

    #[test]
    fn test_convert_pointer_type_immutable() {
        let swift_type = SwiftType::Pointer {
            mutable: false,
            pointee: Box::new(SwiftType::Bool),
        };
        let vc_type = convert_type(&swift_type).unwrap();
        match vc_type {
            VcType::Ref { mutable, inner } => {
                assert!(!mutable);
                assert!(matches!(inner.as_ref(), VcType::Bool));
            }
            _ => panic!("Expected Ref type for Pointer"),
        }
    }

    #[test]
    fn test_convert_void_type() {
        let swift_type = SwiftType::Void;
        let vc_type = convert_type(&swift_type).unwrap();
        assert!(matches!(vc_type, VcType::Tuple(ref elems) if elems.is_empty()));
    }

    #[test]
    fn test_convert_named_type() {
        let swift_type = SwiftType::Named {
            name: "CustomType".to_string(),
        };
        let vc_type = convert_type(&swift_type).unwrap();
        match vc_type {
            VcType::Abstract(name) => {
                assert_eq!(name, "CustomType");
            }
            _ => panic!("Expected Abstract type for Named"),
        }
    }

    // ============================================================
    // Additional expression conversion tests
    // ============================================================

    #[test]
    fn test_convert_nil_lit() {
        let expr = SwiftExpr::NilLit;
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::NilLit));
    }

    #[test]
    fn test_convert_sub() {
        let expr = SwiftExpr::Sub {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Sub(_, _)));
    }

    #[test]
    fn test_convert_mul() {
        let expr = SwiftExpr::Mul {
            lhs: Box::new(SwiftExpr::IntLit { value: 2 }),
            rhs: Box::new(SwiftExpr::IntLit { value: 3 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Mul(_, _)));
    }

    #[test]
    fn test_convert_div() {
        let expr = SwiftExpr::Div {
            lhs: Box::new(SwiftExpr::IntLit { value: 10 }),
            rhs: Box::new(SwiftExpr::IntLit { value: 2 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Div(_, _)));
    }

    #[test]
    fn test_convert_mod() {
        let expr = SwiftExpr::Mod {
            lhs: Box::new(SwiftExpr::IntLit { value: 10 }),
            rhs: Box::new(SwiftExpr::IntLit { value: 3 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Rem(_, _)));
    }

    #[test]
    fn test_convert_eq_with_nil_rhs() {
        // expr == nil should become expr.hasValue == false
        let expr = SwiftExpr::Eq {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::NilLit),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Eq(lhs, rhs) => {
                assert!(matches!(
                    lhs.as_ref(),
                    VcExpr::StructField(_, field) if field == "hasValue"
                ));
                assert!(matches!(rhs.as_ref(), VcExpr::BoolLit(false)));
            }
            _ => panic!("Expected Eq expression"),
        }
    }

    #[test]
    fn test_convert_eq_with_nil_lhs() {
        // nil == expr should become expr.hasValue == false
        let expr = SwiftExpr::Eq {
            lhs: Box::new(SwiftExpr::NilLit),
            rhs: Box::new(SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Eq(lhs, rhs) => {
                assert!(matches!(
                    lhs.as_ref(),
                    VcExpr::StructField(_, field) if field == "hasValue"
                ));
                assert!(matches!(rhs.as_ref(), VcExpr::BoolLit(false)));
            }
            _ => panic!("Expected Eq expression"),
        }
    }

    #[test]
    fn test_convert_ne_with_nil_rhs() {
        // expr != nil should become expr.hasValue == true
        let expr = SwiftExpr::Ne {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::NilLit),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Eq(lhs, rhs) => {
                assert!(matches!(
                    lhs.as_ref(),
                    VcExpr::StructField(_, field) if field == "hasValue"
                ));
                assert!(matches!(rhs.as_ref(), VcExpr::BoolLit(true)));
            }
            _ => panic!("Expected Eq expression for != nil"),
        }
    }

    #[test]
    fn test_convert_ne_with_nil_lhs() {
        // nil != expr should become expr.hasValue == true
        let expr = SwiftExpr::Ne {
            lhs: Box::new(SwiftExpr::NilLit),
            rhs: Box::new(SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Eq(lhs, rhs) => {
                assert!(matches!(
                    lhs.as_ref(),
                    VcExpr::StructField(_, field) if field == "hasValue"
                ));
                assert!(matches!(rhs.as_ref(), VcExpr::BoolLit(true)));
            }
            _ => panic!("Expected Eq expression for nil !="),
        }
    }

    #[test]
    fn test_convert_eq_regular() {
        // Regular equality without nil
        let expr = SwiftExpr::Eq {
            lhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            rhs: Box::new(SwiftExpr::IntLit { value: 2 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Eq(_, _)));
    }

    #[test]
    fn test_convert_ne_regular() {
        // Regular inequality without nil
        let expr = SwiftExpr::Ne {
            lhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            rhs: Box::new(SwiftExpr::IntLit { value: 2 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Ne(_, _)));
    }

    #[test]
    fn test_convert_lt() {
        let expr = SwiftExpr::Lt {
            lhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            rhs: Box::new(SwiftExpr::IntLit { value: 2 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Lt(_, _)));
    }

    #[test]
    fn test_convert_le() {
        let expr = SwiftExpr::Le {
            lhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            rhs: Box::new(SwiftExpr::IntLit { value: 2 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Le(_, _)));
    }

    #[test]
    fn test_convert_ge() {
        let expr = SwiftExpr::Ge {
            lhs: Box::new(SwiftExpr::IntLit { value: 2 }),
            rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Ge(_, _)));
    }

    #[test]
    fn test_convert_gt() {
        let expr = SwiftExpr::Gt {
            lhs: Box::new(SwiftExpr::IntLit { value: 5 }),
            rhs: Box::new(SwiftExpr::IntLit { value: 3 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Gt(_, _)));
    }

    #[test]
    fn test_convert_or() {
        let expr = SwiftExpr::Or {
            lhs: Box::new(SwiftExpr::BoolLit { value: true }),
            rhs: Box::new(SwiftExpr::BoolLit { value: false }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Or(_, _)));
    }

    #[test]
    fn test_convert_neg() {
        let expr = SwiftExpr::Neg {
            operand: Box::new(SwiftExpr::IntLit { value: 42 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Neg(_)));
    }

    #[test]
    fn test_convert_not() {
        let expr = SwiftExpr::Not {
            operand: Box::new(SwiftExpr::BoolLit { value: true }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Not(_)));
    }

    #[test]
    fn test_convert_old() {
        let expr = SwiftExpr::Old {
            expr: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Old(_)));
    }

    #[test]
    fn test_convert_index() {
        let expr = SwiftExpr::Index {
            base: Box::new(SwiftExpr::ParamRef {
                name: "arr".to_string(),
                index: 0,
            }),
            index: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::ArrayIndex(_, _)));
    }

    #[test]
    fn test_convert_field() {
        let expr = SwiftExpr::Field {
            base: Box::new(SwiftExpr::ParamRef {
                name: "obj".to_string(),
                index: 0,
            }),
            field: "value".to_string(),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::StructField(_, field) => {
                assert_eq!(field, "value");
            }
            _ => panic!("Expected StructField"),
        }
    }

    #[test]
    fn test_convert_call() {
        let expr = SwiftExpr::Call {
            func: "abs".to_string(),
            args: vec![SwiftExpr::IntLit { value: -5 }],
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Apply { func, args } => {
                assert_eq!(func, "abs");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("Expected Apply"),
        }
    }

    #[test]
    fn test_convert_call_no_args() {
        let expr = SwiftExpr::Call {
            func: "getTime".to_string(),
            args: vec![],
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Apply { func, args } => {
                assert_eq!(func, "getTime");
                assert!(args.is_empty());
            }
            _ => panic!("Expected Apply"),
        }
    }

    #[test]
    fn test_convert_ite() {
        let expr = SwiftExpr::Ite {
            cond: Box::new(SwiftExpr::BoolLit { value: true }),
            then_expr: Box::new(SwiftExpr::IntLit { value: 1 }),
            else_expr: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Ite { cond, then_, else_ } => {
                assert!(matches!(cond.as_ref(), VcExpr::BoolLit(true)));
                assert!(matches!(then_.as_ref(), VcExpr::IntLit(1)));
                assert!(matches!(else_.as_ref(), VcExpr::IntLit(0)));
            }
            _ => panic!("Expected Ite"),
        }
    }

    #[test]
    fn test_convert_forall() {
        let expr = SwiftExpr::Forall {
            vars: vec![(
                "i".to_string(),
                SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Forall { vars, body: _ } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "i");
            }
            _ => panic!("Expected Forall"),
        }
    }

    #[test]
    fn test_convert_exists() {
        let expr = SwiftExpr::Exists {
            vars: vec![("x".to_string(), SwiftType::Bool)],
            body: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Exists { vars, body: _ } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "x");
            }
            _ => panic!("Expected Exists"),
        }
    }

    #[test]
    fn test_convert_type_lit() {
        let expr = SwiftExpr::TypeLit {
            ty: "String".to_string(),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Var(name) => {
                assert_eq!(name, "type_String");
            }
            _ => panic!("Expected Var for TypeLit"),
        }
    }

    #[test]
    fn test_convert_string_lit() {
        let expr = SwiftExpr::StringLit {
            value: "hello".to_string(),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Var(name) => {
                assert_eq!(name, "str_hello");
            }
            _ => panic!("Expected Var for StringLit"),
        }
    }

    #[test]
    fn test_convert_string_lit_with_dash() {
        // Dashes should be replaced with underscores
        let expr = SwiftExpr::StringLit {
            value: "hello-world".to_string(),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Var(name) => {
                assert_eq!(name, "str_hello_world");
            }
            _ => panic!("Expected Var for StringLit"),
        }
    }

    // ============================================================
    // Test make_source_span
    // ============================================================

    #[test]
    fn test_make_source_span() {
        let span = make_source_span("test.swift", 10, 5);
        assert_eq!(span.file.as_ref(), "test.swift");
        assert_eq!(span.line_start, 10);
        assert_eq!(span.line_end, 10);
        assert_eq!(span.col_start, 5);
        assert_eq!(span.col_end, 5);
    }

    #[test]
    fn test_make_source_span_empty_file() {
        let span = make_source_span("", 0, 0);
        assert_eq!(span.file.as_ref(), "");
        assert_eq!(span.line_start, 0);
    }

    // ============================================================
    // Test overflow_proxy_bounds
    // ============================================================

    #[test]
    fn test_overflow_proxy_bounds() {
        let (min, max) = overflow_proxy_bounds();
        assert_eq!(min, i128::from(i64::MIN));
        assert_eq!(max, i128::from(i64::MAX));
    }

    // ============================================================
    // Auto-VC conversion tests
    // ============================================================

    fn make_test_bundle() -> SwiftVcBundle {
        SwiftVcBundle {
            function_name: "test_func".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 1,
            parameters: vec![],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        }
    }

    #[test]
    fn test_convert_auto_vc_overflow_add() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Overflow {
            description: "overflow check for add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "a".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "b".to_string(),
                    index: 1,
                },
            ],
            operation: "add".to_string(),
            source_line: 10,
            source_column: 5,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(0), &bundle).unwrap();
        assert_eq!(vc.name, "overflow check for add");
        assert_eq!(vc.span.line_start, 10);
        // Should be a Predicate kind (bounds check)
        assert!(matches!(vc.condition, VcKind::Predicate(_)));
    }

    #[test]
    fn test_convert_auto_vc_overflow_sub() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Overflow {
            description: "overflow check for sub".to_string(),
            operands: vec![
                SwiftExpr::IntLit { value: 100 },
                SwiftExpr::IntLit { value: 50 },
            ],
            operation: "sub".to_string(),
            source_line: 20,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 32,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(1), &bundle).unwrap();
        assert_eq!(vc.name, "overflow check for sub");
        assert!(matches!(vc.condition, VcKind::Predicate(_)));
    }

    #[test]
    fn test_convert_auto_vc_overflow_mul() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Overflow {
            description: "overflow check for mul".to_string(),
            operands: vec![
                SwiftExpr::IntLit { value: 2 },
                SwiftExpr::IntLit { value: 3 },
            ],
            operation: "mul".to_string(),
            source_line: 30,
            source_column: 1,
            path_condition: None,
            signed: false,
            bits: 8,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(2), &bundle).unwrap();
        assert_eq!(vc.name, "overflow check for mul");
    }

    #[test]
    fn test_convert_auto_vc_overflow_div() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Overflow {
            description: "overflow check for div".to_string(),
            operands: vec![
                SwiftExpr::IntLit { value: 10 },
                SwiftExpr::IntLit { value: 2 },
            ],
            operation: "div".to_string(),
            source_line: 40,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(3), &bundle).unwrap();
        assert_eq!(vc.name, "overflow check for div");
    }

    #[test]
    fn test_convert_auto_vc_overflow_mod() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Overflow {
            description: "overflow check for mod".to_string(),
            operands: vec![
                SwiftExpr::IntLit { value: 10 },
                SwiftExpr::IntLit { value: 3 },
            ],
            operation: "mod".to_string(),
            source_line: 50,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(4), &bundle).unwrap();
        assert_eq!(vc.name, "overflow check for mod");
    }

    #[test]
    fn test_convert_auto_vc_overflow_neg() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Overflow {
            description: "overflow check for neg".to_string(),
            operands: vec![SwiftExpr::IntLit { value: 42 }],
            operation: "neg".to_string(),
            source_line: 60,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(5), &bundle).unwrap();
        assert_eq!(vc.name, "overflow check for neg");
    }

    #[test]
    fn test_convert_auto_vc_overflow_unknown_op() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Overflow {
            description: "overflow check for unknown".to_string(),
            operands: vec![
                SwiftExpr::IntLit { value: 1 },
                SwiftExpr::IntLit { value: 2 },
            ],
            operation: "unknown_op".to_string(),
            source_line: 70,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(6), &bundle).unwrap();
        // Unknown ops get a placeholder true predicate
        assert!(matches!(vc.condition, VcKind::Predicate(_)));
    }

    #[test]
    fn test_convert_auto_vc_overflow_insufficient_operands() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Overflow {
            description: "overflow with no operands".to_string(),
            operands: vec![],
            operation: "add".to_string(),
            source_line: 80,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(7), &bundle).unwrap();
        // No operands - gets placeholder
        assert!(matches!(vc.condition, VcKind::Predicate(_)));
    }

    #[test]
    fn test_convert_auto_vc_overflow_with_path_condition() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Overflow {
            description: "conditional overflow check".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::IntLit { value: 1 },
            ],
            operation: "add".to_string(),
            source_line: 90,
            source_column: 1,
            path_condition: Some(SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            signed: true,
            bits: 64,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(8), &bundle).unwrap();
        // With path condition, should be Implies
        assert!(matches!(vc.condition, VcKind::Implies { .. }));
    }

    #[test]
    fn test_convert_auto_vc_div_by_zero() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::DivByZero {
            divisor: SwiftExpr::ParamRef {
                name: "d".to_string(),
                index: 1,
            },
            description: "division by zero check".to_string(),
            source_line: 100,
            source_column: 10,
            path_condition: None,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(9), &bundle).unwrap();
        assert_eq!(vc.name, "division by zero check");
        assert_eq!(vc.span.line_start, 100);
    }

    #[test]
    fn test_convert_auto_vc_div_by_zero_fallback_line() {
        let mut bundle = make_test_bundle();
        bundle.source_line = 999;
        let auto_vc = SwiftAutoVc::DivByZero {
            divisor: SwiftExpr::IntLit { value: 5 },
            description: "div check".to_string(),
            source_line: 0, // Zero line should fallback to bundle
            source_column: 0,
            path_condition: None,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(10), &bundle).unwrap();
        assert_eq!(vc.span.line_start, 999);
    }

    #[test]
    fn test_convert_auto_vc_bounds_check() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::IntLit { value: 10 },
            description: "array bounds check".to_string(),
            source_line: 110,
            source_column: 1,
            path_condition: None,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(11), &bundle).unwrap();
        assert_eq!(vc.name, "array bounds check");
        assert!(matches!(vc.condition, VcKind::Predicate(_)));
    }

    #[test]
    fn test_convert_auto_vc_nil_check() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "nil check for optional".to_string(),
            source_line: 120,
            source_column: 1,
            path_condition: None,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(12), &bundle).unwrap();
        assert_eq!(vc.name, "nil check for optional");
    }

    #[test]
    fn test_convert_auto_vc_cast_check() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::CastCheck {
            value: SwiftExpr::ParamRef {
                name: "obj".to_string(),
                index: 0,
            },
            source_type: "Any".to_string(),
            target_type: "String".to_string(),
            description: "cast check to String".to_string(),
            source_line: 130,
            source_column: 1,
            path_condition: None,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(13), &bundle).unwrap();
        assert_eq!(vc.name, "cast check to String");
    }

    #[test]
    fn test_convert_auto_vc_cast_check_complex_type() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::CastCheck {
            value: SwiftExpr::ParamRef {
                name: "obj".to_string(),
                index: 0,
            },
            source_type: "Any".to_string(),
            target_type: "Array<Optional<Int>>".to_string(),
            description: "cast check to complex type".to_string(),
            source_line: 140,
            source_column: 1,
            path_condition: None,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(14), &bundle).unwrap();
        // Type name should have special chars replaced
        assert_eq!(vc.name, "cast check to complex type");
    }

    #[test]
    fn test_convert_auto_vc_cond_fail() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::CondFail {
            condition: SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            },
            message: "x must be positive".to_string(),
            description: "condition must hold".to_string(),
            source_line: 150,
            source_column: 1,
            path_condition: None,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(15), &bundle).unwrap();
        assert_eq!(vc.name, "condition must hold");
    }

    #[test]
    fn test_convert_auto_vc_call_precondition() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::CallPrecondition {
            callee_name: "processPointer".to_string(),
            condition: SwiftExpr::Ne {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "ptr".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::NilLit),
            },
            description: "callee requires non-nil".to_string(),
            source_line: 160,
            source_column: 1,
            path_condition: None,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(16), &bundle).unwrap();
        assert_eq!(vc.name, "callee requires non-nil");
    }

    #[test]
    fn test_convert_auto_vc_termination() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Termination {
            loop_label: "main_loop".to_string(),
            measure: SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 0,
            },
            initial_measure: Some(SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 0,
            }),
            next_measure: SwiftExpr::Sub {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "n".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            },
            description: "loop termination".to_string(),
            source_line: 170,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(17), &bundle).unwrap();
        assert_eq!(vc.name, "loop termination");
        assert!(matches!(vc.condition, VcKind::Termination { .. }));
    }

    #[test]
    fn test_convert_auto_vc_termination_no_initial() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::Termination {
            loop_label: "while_loop".to_string(),
            measure: SwiftExpr::ParamRef {
                name: "count".to_string(),
                index: 0,
            },
            initial_measure: None,
            next_measure: SwiftExpr::Sub {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "count".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            },
            description: "while loop termination".to_string(),
            source_line: 180,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(18), &bundle).unwrap();
        match &vc.condition {
            VcKind::Termination {
                initial_measure, ..
            } => {
                assert!(initial_measure.is_none());
            }
            _ => panic!("Expected Termination"),
        }
    }

    #[test]
    fn test_convert_auto_vc_recursive_termination() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::RecursiveTermination {
            function_name: "factorial".to_string(),
            decreasing_param: "n".to_string(),
            param_index: 0,
            measure: SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 0,
            },
            recursive_measure: SwiftExpr::Sub {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "n".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            },
            description: "recursive termination".to_string(),
            source_line: 190,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(19), &bundle).unwrap();
        assert_eq!(vc.name, "recursive termination");
        assert!(matches!(vc.condition, VcKind::Termination { .. }));
    }

    #[test]
    fn test_convert_auto_vc_mutual_recursive_termination() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::MutualRecursiveTermination {
            function_cycle: vec!["even".to_string(), "odd".to_string()],
            decreasing_param: "n".to_string(),
            description: "mutual recursion termination".to_string(),
            source_line: 200,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(20), &bundle).unwrap();
        assert!(vc.name.contains("mutual recursion termination"));
        assert!(vc.name.contains("even -> odd"));
    }

    #[test]
    fn test_convert_auto_vc_lexicographic_termination() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::LexicographicTermination {
            function_name: "ackermann".to_string(),
            measure_params: vec!["m".to_string(), "n".to_string()],
            call_site_decreases: vec![("call1".to_string(), 0), ("call2".to_string(), 1)],
            description: "lex termination".to_string(),
            source_line: 210,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(21), &bundle).unwrap();
        assert!(vc.name.contains("lex termination"));
        assert!(vc.name.contains("call1: param 0 decreases"));
    }

    #[test]
    fn test_convert_auto_vc_lexicographic_termination_empty_params() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::LexicographicTermination {
            function_name: "empty_lex".to_string(),
            measure_params: vec![],
            call_site_decreases: vec![],
            description: "empty lex termination".to_string(),
            source_line: 220,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(22), &bundle).unwrap();
        // Should handle empty params gracefully
        assert!(vc.name.contains("empty lex termination"));
    }

    #[test]
    fn test_convert_auto_vc_lexicographic_mutual_recursive_termination() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::LexicographicMutualRecursiveTermination {
            function_cycle: vec!["f".to_string(), "g".to_string(), "h".to_string()],
            measure_params: vec!["x".to_string(), "y".to_string()],
            description: "lex mutual recursion".to_string(),
            source_line: 230,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(23), &bundle).unwrap();
        assert_eq!(vc.name, "lex mutual recursion");
    }

    #[test]
    fn test_convert_auto_vc_state_invariant() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::StateInvariant {
            type_name: "Counter".to_string(),
            property_name: "count".to_string(),
            invariant: SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "count".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            },
            description: "count >= 0".to_string(),
            path_condition: None,
            source_line: 240,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(24), &bundle).unwrap();
        assert_eq!(vc.name, "count >= 0");
        assert!(matches!(vc.condition, VcKind::Predicate(_)));
    }

    #[test]
    fn test_convert_auto_vc_state_invariant_with_path_condition() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::StateInvariant {
            type_name: "Counter".to_string(),
            property_name: "count".to_string(),
            invariant: SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "count".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            },
            description: "count >= 0 (conditional)".to_string(),
            path_condition: Some(SwiftExpr::BoolLit { value: true }),
            source_line: 250,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(25), &bundle).unwrap();
        assert!(matches!(vc.condition, VcKind::Implies { .. }));
    }

    #[test]
    fn test_convert_auto_vc_type_invariant() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::TypeInvariant {
            type_name: "BankAccount".to_string(),
            property_name: "balance".to_string(),
            invariant: SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "balance".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            },
            description: "balance >= 0".to_string(),
            path_condition: None,
            mutating_method: "withdraw".to_string(),
            source_line: 260,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(26), &bundle).unwrap();
        assert_eq!(vc.name, "balance >= 0");
    }

    #[test]
    fn test_convert_auto_vc_type_invariant_with_path_condition() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::TypeInvariant {
            type_name: "BankAccount".to_string(),
            property_name: "balance".to_string(),
            invariant: SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "balance".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            },
            description: "balance >= 0".to_string(),
            path_condition: Some(SwiftExpr::BoolLit { value: true }),
            mutating_method: "deposit".to_string(),
            source_line: 270,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(27), &bundle).unwrap();
        assert!(matches!(vc.condition, VcKind::Implies { .. }));
    }

    #[test]
    fn test_convert_auto_vc_method_call_state_effect() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::MethodCallStateEffect {
            type_name: "Logger".to_string(),
            invariant: SwiftExpr::BoolLit { value: true },
            callee_method: "log".to_string(),
            affected_properties: vec!["buffer".to_string()],
            description: "logger state valid after log".to_string(),
            path_condition: None,
            caller_method: "process".to_string(),
            source_line: 280,
            source_column: 1,
            call_chain: vec![],
        };

        let vc = convert_auto_vc(&auto_vc, VcId(28), &bundle).unwrap();
        assert_eq!(vc.name, "logger state valid after log");
    }

    #[test]
    fn test_convert_auto_vc_method_call_state_effect_with_path_condition() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::MethodCallStateEffect {
            type_name: "Logger".to_string(),
            invariant: SwiftExpr::BoolLit { value: true },
            callee_method: "log".to_string(),
            affected_properties: vec!["buffer".to_string()],
            description: "conditional state effect".to_string(),
            path_condition: Some(SwiftExpr::BoolLit { value: true }),
            caller_method: "process".to_string(),
            source_line: 290,
            source_column: 1,
            call_chain: vec![],
        };

        let vc = convert_auto_vc(&auto_vc, VcId(29), &bundle).unwrap();
        assert!(matches!(vc.condition, VcKind::Implies { .. }));
    }

    #[test]
    fn test_convert_auto_vc_shift_overflow() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::ShiftOverflow {
            operation: "shl".to_string(),
            value: SwiftExpr::IntLit { value: 1 },
            shift_amount: SwiftExpr::ParamRef {
                name: "s".to_string(),
                index: 0,
            },
            bits: 64,
            description: "shift overflow check".to_string(),
            path_condition: None,
            source_line: 300,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(30), &bundle).unwrap();
        assert_eq!(vc.name, "shift overflow check");
    }

    #[test]
    fn test_convert_auto_vc_shift_overflow_with_path_condition() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::ShiftOverflow {
            operation: "shr".to_string(),
            value: SwiftExpr::IntLit { value: 256 },
            shift_amount: SwiftExpr::IntLit { value: 4 },
            bits: 32,
            description: "conditional shift check".to_string(),
            path_condition: Some(SwiftExpr::BoolLit { value: true }),
            source_line: 310,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(31), &bundle).unwrap();
        assert!(matches!(vc.condition, VcKind::Implies { .. }));
    }

    #[test]
    fn test_convert_auto_vc_unowned_access() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::UnownedAccess {
            reference: SwiftExpr::ParamRef {
                name: "ref".to_string(),
                index: 0,
            },
            reference_name: "myRef".to_string(),
            description: "unowned reference valid".to_string(),
            path_condition: None,
            source_line: 320,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(32), &bundle).unwrap();
        assert_eq!(vc.name, "unowned reference valid");
    }

    #[test]
    fn test_convert_auto_vc_unowned_access_with_path_condition() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::UnownedAccess {
            reference: SwiftExpr::ParamRef {
                name: "ref".to_string(),
                index: 0,
            },
            reference_name: "myRef".to_string(),
            description: "conditional unowned access".to_string(),
            path_condition: Some(SwiftExpr::BoolLit { value: true }),
            source_line: 330,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(33), &bundle).unwrap();
        assert!(matches!(vc.condition, VcKind::Implies { .. }));
    }

    #[test]
    fn test_convert_auto_vc_actor_isolation_crossing() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::ActorIsolationCrossing {
            callee_name: "doWork".to_string(),
            caller_isolation: "MainActor".to_string(),
            callee_isolation: "BackgroundActor".to_string(),
            description: "actor crossing safe".to_string(),
            path_condition: None,
            source_line: 340,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(34), &bundle).unwrap();
        assert_eq!(vc.name, "actor crossing safe");
    }

    #[test]
    fn test_convert_auto_vc_actor_isolation_crossing_with_path_condition() {
        let bundle = make_test_bundle();
        let auto_vc = SwiftAutoVc::ActorIsolationCrossing {
            callee_name: "fetch".to_string(),
            caller_isolation: "MainActor".to_string(),
            callee_isolation: "nonisolated".to_string(),
            description: "conditional actor crossing".to_string(),
            path_condition: Some(SwiftExpr::BoolLit { value: true }),
            source_line: 350,
            source_column: 1,
        };

        let vc = convert_auto_vc(&auto_vc, VcId(35), &bundle).unwrap();
        assert!(matches!(vc.condition, VcKind::Implies { .. }));
    }

    // ============================================================
    // Bundle conversion edge cases
    // ============================================================

    #[test]
    fn test_convert_bundle_empty() {
        let bundle = make_test_bundle();
        let fvcs = convert_bundle(&bundle).unwrap();
        assert_eq!(fvcs.name, "test_func");
        assert!(fvcs.requires.is_empty());
        assert!(fvcs.ensures.is_empty());
        assert!(fvcs.loop_invariants.is_empty());
        assert!(fvcs.assertions.is_empty());
    }

    #[test]
    fn test_convert_bundle_with_void_return() {
        let bundle = SwiftVcBundle {
            function_name: "void_func".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 1,
            parameters: vec![],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let fvcs = convert_bundle(&bundle).unwrap();
        // Void should become empty tuple
        assert!(matches!(fvcs.signature.return_type, VcType::Tuple(ref v) if v.is_empty()));
    }

    #[test]
    fn test_convert_bundle_with_multiple_params() {
        let bundle = SwiftVcBundle {
            function_name: "multi_param".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 1,
            parameters: vec![
                SwiftParam {
                    name: "a".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "b".to_string(),
                    param_type: SwiftType::Bool,
                    index: 1,
                },
                SwiftParam {
                    name: "c".to_string(),
                    param_type: SwiftType::Float { bits: 64 },
                    index: 2,
                },
            ],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 64,
            }),
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let fvcs = convert_bundle(&bundle).unwrap();
        assert_eq!(fvcs.signature.params.len(), 3);
        assert_eq!(fvcs.signature.params[0].0, "a");
        assert_eq!(fvcs.signature.params[1].0, "b");
        assert_eq!(fvcs.signature.params[2].0, "c");
    }

    #[test]
    fn test_convert_bundle_with_invariants() {
        let bundle = SwiftVcBundle {
            function_name: "with_inv".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 1,
            parameters: vec![SwiftParam {
                name: "i".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
                index: 0,
            }],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![
                SwiftExpr::Ge {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "i".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
                },
                SwiftExpr::Lt {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "i".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 100 }),
                },
            ],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let fvcs = convert_bundle(&bundle).unwrap();
        assert_eq!(fvcs.loop_invariants.len(), 2);
        assert_eq!(fvcs.loop_invariants[0].name, "invariant_0");
        assert_eq!(fvcs.loop_invariants[1].name, "invariant_1");
    }

    #[test]
    fn test_convert_bundle_with_auto_vcs() {
        let bundle = SwiftVcBundle {
            function_name: "with_auto_vc".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 1,
            parameters: vec![],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![
                SwiftAutoVc::DivByZero {
                    divisor: SwiftExpr::IntLit { value: 2 },
                    description: "div check 1".to_string(),
                    source_line: 10,
                    source_column: 1,
                    path_condition: None,
                },
                SwiftAutoVc::BoundsCheck {
                    index: SwiftExpr::IntLit { value: 0 },
                    length: SwiftExpr::IntLit { value: 10 },
                    description: "bounds check 1".to_string(),
                    source_line: 20,
                    source_column: 1,
                    path_condition: None,
                },
            ],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let fvcs = convert_bundle(&bundle).unwrap();
        assert_eq!(fvcs.assertions.len(), 2);
        assert_eq!(fvcs.assertions[0].name, "div check 1");
        assert_eq!(fvcs.assertions[1].name, "bounds check 1");
    }

    #[test]
    fn test_convert_bundle_vc_id_incrementing() {
        let bundle = SwiftVcBundle {
            function_name: "inc_ids".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 1,
            parameters: vec![],
            return_type: None,
            requires: vec![SwiftExpr::BoolLit { value: true }],
            ensures: vec![SwiftExpr::BoolLit { value: true }],
            invariants: vec![SwiftExpr::BoolLit { value: true }],
            auto_vcs: vec![SwiftAutoVc::DivByZero {
                divisor: SwiftExpr::IntLit { value: 1 },
                description: "div".to_string(),
                source_line: 1,
                source_column: 1,
                path_condition: None,
            }],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let fvcs = convert_bundle(&bundle).unwrap();
        // IDs should be 0, 1, 2, 3 for requires, ensures, invariant, assertion
        assert_eq!(fvcs.requires[0].id, VcId(0));
        assert_eq!(fvcs.ensures[0].id, VcId(1));
        assert_eq!(fvcs.loop_invariants[0].id, VcId(2));
        assert_eq!(fvcs.assertions[0].id, VcId(3));
    }

    // ============================================================
    // Nested type conversion tests
    // ============================================================

    #[test]
    fn test_convert_nested_optional_array() {
        let swift_type = SwiftType::Optional {
            inner: Box::new(SwiftType::Array {
                element: Box::new(SwiftType::Int {
                    signed: true,
                    bits: 64,
                }),
            }),
        };
        let vc_type = convert_type(&swift_type).unwrap();
        match vc_type {
            VcType::Struct { name, fields } => {
                assert_eq!(name, "Optional");
                match &fields[1].1 {
                    VcType::Array { elem, .. } => {
                        assert!(matches!(
                            elem.as_ref(),
                            VcType::Int {
                                signed: true,
                                bits: 64
                            }
                        ));
                    }
                    _ => panic!("Expected Array"),
                }
            }
            _ => panic!("Expected Struct"),
        }
    }

    #[test]
    fn test_convert_array_of_optionals() {
        let swift_type = SwiftType::Array {
            element: Box::new(SwiftType::Optional {
                inner: Box::new(SwiftType::Bool),
            }),
        };
        let vc_type = convert_type(&swift_type).unwrap();
        match vc_type {
            VcType::Array { elem, .. } => match elem.as_ref() {
                VcType::Struct { name, .. } => {
                    assert_eq!(name, "Optional");
                }
                _ => panic!("Expected Struct for Optional"),
            },
            _ => panic!("Expected Array"),
        }
    }

    #[test]
    fn test_convert_pointer_to_pointer() {
        let swift_type = SwiftType::Pointer {
            mutable: true,
            pointee: Box::new(SwiftType::Pointer {
                mutable: false,
                pointee: Box::new(SwiftType::Int {
                    signed: false,
                    bits: 8,
                }),
            }),
        };
        let vc_type = convert_type(&swift_type).unwrap();
        match vc_type {
            VcType::Ref { mutable, inner } => {
                assert!(mutable);
                match inner.as_ref() {
                    VcType::Ref {
                        mutable: inner_mut,
                        inner: inner_inner,
                    } => {
                        assert!(!inner_mut);
                        assert!(matches!(
                            inner_inner.as_ref(),
                            VcType::Int {
                                signed: false,
                                bits: 8
                            }
                        ));
                    }
                    _ => panic!("Expected nested Ref"),
                }
            }
            _ => panic!("Expected Ref"),
        }
    }

    // ============================================================
    // Complex expression conversion tests
    // ============================================================

    #[test]
    fn test_convert_deeply_nested_expression() {
        // ((a + b) * c) - d
        let expr = SwiftExpr::Sub {
            lhs: Box::new(SwiftExpr::Mul {
                lhs: Box::new(SwiftExpr::Add {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "a".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::ParamRef {
                        name: "b".to_string(),
                        index: 1,
                    }),
                }),
                rhs: Box::new(SwiftExpr::ParamRef {
                    name: "c".to_string(),
                    index: 2,
                }),
            }),
            rhs: Box::new(SwiftExpr::ParamRef {
                name: "d".to_string(),
                index: 3,
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Sub(_, _)));
    }

    #[test]
    fn test_convert_complex_boolean_expression() {
        // (a > 0 && b < 10) || (c == true)
        let expr = SwiftExpr::Or {
            lhs: Box::new(SwiftExpr::And {
                lhs: Box::new(SwiftExpr::Gt {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "a".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
                }),
                rhs: Box::new(SwiftExpr::Lt {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "b".to_string(),
                        index: 1,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 10 }),
                }),
            }),
            rhs: Box::new(SwiftExpr::Eq {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "c".to_string(),
                    index: 2,
                }),
                rhs: Box::new(SwiftExpr::BoolLit { value: true }),
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::Or(_, _)));
    }

    #[test]
    fn test_convert_nested_ite() {
        // if a then (if b then 1 else 2) else 3
        let expr = SwiftExpr::Ite {
            cond: Box::new(SwiftExpr::ParamRef {
                name: "a".to_string(),
                index: 0,
            }),
            then_expr: Box::new(SwiftExpr::Ite {
                cond: Box::new(SwiftExpr::ParamRef {
                    name: "b".to_string(),
                    index: 1,
                }),
                then_expr: Box::new(SwiftExpr::IntLit { value: 1 }),
                else_expr: Box::new(SwiftExpr::IntLit { value: 2 }),
            }),
            else_expr: Box::new(SwiftExpr::IntLit { value: 3 }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Ite { then_, .. } => {
                assert!(matches!(then_.as_ref(), VcExpr::Ite { .. }));
            }
            _ => panic!("Expected Ite"),
        }
    }

    #[test]
    fn test_convert_forall_with_complex_body() {
        let expr = SwiftExpr::Forall {
            vars: vec![
                (
                    "i".to_string(),
                    SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
                (
                    "j".to_string(),
                    SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
            ],
            body: Box::new(SwiftExpr::Or {
                lhs: Box::new(SwiftExpr::Lt {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "i".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::ParamRef {
                        name: "j".to_string(),
                        index: 1,
                    }),
                }),
                rhs: Box::new(SwiftExpr::Eq {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "i".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::ParamRef {
                        name: "j".to_string(),
                        index: 1,
                    }),
                }),
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Forall { vars, .. } => {
                assert_eq!(vars.len(), 2);
            }
            _ => panic!("Expected Forall"),
        }
    }

    #[test]
    fn test_convert_call_with_nested_args() {
        let expr = SwiftExpr::Call {
            func: "max".to_string(),
            args: vec![
                SwiftExpr::Add {
                    lhs: Box::new(SwiftExpr::IntLit { value: 1 }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 2 }),
                },
                SwiftExpr::Mul {
                    lhs: Box::new(SwiftExpr::IntLit { value: 3 }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 4 }),
                },
            ],
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Apply { func, args } => {
                assert_eq!(func, "max");
                assert_eq!(args.len(), 2);
                assert!(matches!(args[0], VcExpr::Add(_, _)));
                assert!(matches!(args[1], VcExpr::Mul(_, _)));
            }
            _ => panic!("Expected Apply"),
        }
    }

    #[test]
    fn test_convert_nested_field_access() {
        // obj.inner.value
        let expr = SwiftExpr::Field {
            base: Box::new(SwiftExpr::Field {
                base: Box::new(SwiftExpr::ParamRef {
                    name: "obj".to_string(),
                    index: 0,
                }),
                field: "inner".to_string(),
            }),
            field: "value".to_string(),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::StructField(base, field) => {
                assert_eq!(field, "value");
                match base.as_ref() {
                    VcExpr::StructField(_, inner_field) => {
                        assert_eq!(inner_field, "inner");
                    }
                    _ => panic!("Expected nested StructField"),
                }
            }
            _ => panic!("Expected StructField"),
        }
    }

    #[test]
    fn test_convert_nested_array_index() {
        // arr[i][j]
        let expr = SwiftExpr::Index {
            base: Box::new(SwiftExpr::Index {
                base: Box::new(SwiftExpr::ParamRef {
                    name: "arr".to_string(),
                    index: 0,
                }),
                index: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: 1,
                }),
            }),
            index: Box::new(SwiftExpr::ParamRef {
                name: "j".to_string(),
                index: 2,
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::ArrayIndex(base, _) => {
                assert!(matches!(base.as_ref(), VcExpr::ArrayIndex(_, _)));
            }
            _ => panic!("Expected ArrayIndex"),
        }
    }

    #[test]
    fn test_convert_old_with_complex_expr() {
        let expr = SwiftExpr::Old {
            expr: Box::new(SwiftExpr::Field {
                base: Box::new(SwiftExpr::ParamRef {
                    name: "self".to_string(),
                    index: 0,
                }),
                field: "count".to_string(),
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Old(inner) => {
                assert!(matches!(inner.as_ref(), VcExpr::StructField(_, _)));
            }
            _ => panic!("Expected Old"),
        }
    }

    #[test]
    fn test_convert_negative_int_literal() {
        let expr = SwiftExpr::IntLit { value: -42 };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::IntLit(-42)));
    }

    #[test]
    fn test_convert_large_int_literal() {
        let expr = SwiftExpr::IntLit { value: i64::MAX };
        let vc_expr = convert_expr(&expr).unwrap();
        assert!(matches!(vc_expr, VcExpr::IntLit(v) if v == i128::from(i64::MAX)));
    }

    #[test]
    fn test_convert_double_negation() {
        let expr = SwiftExpr::Not {
            operand: Box::new(SwiftExpr::Not {
                operand: Box::new(SwiftExpr::BoolLit { value: true }),
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Not(inner) => {
                assert!(matches!(inner.as_ref(), VcExpr::Not(_)));
            }
            _ => panic!("Expected Not"),
        }
    }

    #[test]
    fn test_convert_arithmetic_negation() {
        let expr = SwiftExpr::Neg {
            operand: Box::new(SwiftExpr::Neg {
                operand: Box::new(SwiftExpr::IntLit { value: 5 }),
            }),
        };
        let vc_expr = convert_expr(&expr).unwrap();
        match vc_expr {
            VcExpr::Neg(inner) => {
                assert!(matches!(inner.as_ref(), VcExpr::Neg(_)));
            }
            _ => panic!("Expected Neg"),
        }
    }
}
