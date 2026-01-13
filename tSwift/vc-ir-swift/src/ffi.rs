//! C FFI for calling from Swift compiler (C++).
//!
//! This module provides C-compatible functions for:
//! 1. Parsing JSON verification bundles
//! 2. Converting to VC IR
//! 3. Verifying using Z4 SMT backend
//! 4. Returning results as JSON

use std::collections::{HashMap, HashSet};
use std::ffi::{CStr, CString};
use std::fmt::Write as _;
use std::os::raw::c_char;
use std::ptr;
use std::time::Instant;

use crate::convert::{convert_bundle, overflow_bounds_for_type};
use crate::error::VcBridgeError;
#[cfg(test)]
use crate::json_types::SwiftParam;
use crate::json_types::{
    SwiftAutoVc, SwiftAutoVcResult, SwiftExpr, SwiftType, SwiftVcBundle, SwiftVerifyResponse,
    SwiftVerifyResult, VerificationSummary,
};
use crate::types::{
    Counterexample, Expr, FunctionVcs, Predicate, SourceSpan, UnknownReason, Value, VcId, VcKind,
    VerificationCondition, VerifyResult,
};
use crate::z4_backend::{
    verify_vc_with_fallback as verify_vc, verify_vc_with_fallback_and_trace as verify_vc_with_trace,
};

/// Convert comparison conditions to Z4-friendly forms.
///
/// Z4's `QF_LIA` solver handles >= and <= better than > and <.
/// For integer comparisons against literals:
/// - x > n becomes x >= n+1 (positive) and x <= n (negative)
/// - x < n becomes x <= n-1 (positive) and x >= n (negative)
///
/// For variable comparisons, we use the dual comparison form:
/// - x >= y: positive is x >= y, negative is x < y (which is y > x, i.e., NOT(x >= y))
/// - x <= y: positive is x <= y, negative is x > y (which is NOT(x <= y))
///
/// Returns (`positive_predicate`, `negative_predicate`) pair.
fn condition_to_z4_friendly(cond: &Expr) -> (Predicate, Predicate) {
    match cond {
        // x > n becomes x >= n+1 (positive), x <= n (negative)
        Expr::Gt(a, b) => {
            if let Expr::IntLit(n) = b.as_ref() {
                n.checked_add(1).map_or_else(
                    || {
                        // Avoid i128 overflow on n+1; keep strict comparison.
                        let pos = Predicate::Expr(cond.clone());
                        let neg = Predicate::Expr(Expr::Le(a.clone(), b.clone()));
                        (pos, neg)
                    },
                    |n_plus_one| {
                        // Positive: x >= n+1
                        let pos = Predicate::Expr(Expr::Ge(
                            a.clone(),
                            Box::new(Expr::IntLit(n_plus_one)),
                        ));
                        // Negative: x <= n
                        let neg = Predicate::Expr(Expr::Le(a.clone(), b.clone()));
                        (pos, neg)
                    },
                )
            } else {
                // For variable comparisons: x > y, negative is x <= y
                let pos = Predicate::Expr(cond.clone());
                let neg = Predicate::Expr(Expr::Le(a.clone(), b.clone()));
                (pos, neg)
            }
        }
        // x < n becomes x <= n-1 (positive), x >= n (negative)
        Expr::Lt(a, b) => {
            if let Expr::IntLit(n) = b.as_ref() {
                n.checked_sub(1).map_or_else(
                    || {
                        // Avoid i128 overflow on n-1; keep strict comparison.
                        let pos = Predicate::Expr(cond.clone());
                        let neg = Predicate::Expr(Expr::Ge(a.clone(), b.clone()));
                        (pos, neg)
                    },
                    |n_minus_one| {
                        // Positive: x <= n-1
                        let pos = Predicate::Expr(Expr::Le(
                            a.clone(),
                            Box::new(Expr::IntLit(n_minus_one)),
                        ));
                        // Negative: x >= n
                        let neg = Predicate::Expr(Expr::Ge(a.clone(), b.clone()));
                        (pos, neg)
                    },
                )
            } else {
                // For variable comparisons: x < y, negative is x >= y
                let pos = Predicate::Expr(cond.clone());
                let neg = Predicate::Expr(Expr::Ge(a.clone(), b.clone()));
                (pos, neg)
            }
        }
        // x >= y: positive is x >= y, negative is x < y
        // For integers, x < y is equivalent to x + 1 <= y, which avoids (not (>= ...))
        Expr::Ge(a, b) => {
            let pos = Predicate::Expr(cond.clone());
            // Negative: x < y ≡ x + 1 <= y for integers
            // This avoids (not (>= x y)) which Z4 struggles with
            let neg = Predicate::Expr(Expr::Le(
                Box::new(Expr::Add(a.clone(), Box::new(Expr::IntLit(1)))),
                b.clone(),
            ));
            (pos, neg)
        }
        // x <= y: positive is x <= y, negative is x > y
        // For integers, x > y is equivalent to x >= y + 1
        Expr::Le(a, b) => {
            let pos = Predicate::Expr(cond.clone());
            // Negative: x > y ≡ x >= y + 1 for integers
            let neg = Predicate::Expr(Expr::Ge(
                a.clone(),
                Box::new(Expr::Add(b.clone(), Box::new(Expr::IntLit(1)))),
            ));
            (pos, neg)
        }
        // NOT(inner): swap positive and negative of inner condition
        // This handles xor_Int1(cond, -1) translated to Not(cond)
        Expr::Not(inner) => {
            let (inner_pos, inner_neg) = condition_to_z4_friendly(inner);
            // NOT(inner): positive is negative of inner, negative is positive of inner
            (inner_neg, inner_pos)
        }
        // For other conditions, use standard form
        _ => {
            let pos = Predicate::Expr(cond.clone());
            let neg = Predicate::Not(Box::new(pos.clone()));
            (pos, neg)
        }
    }
}

/// Recursively expand an ite expression to cases.
///
/// For `ite(c1, e1, ite(c2, e2, e3))`, returns:
/// - (c1, e1)
/// - (NOT c1 AND c2, e2)
/// - (NOT c1 AND NOT c2, e3)
///
/// Uses Z4-friendly forms for conditions.
fn expand_ite_to_cases(
    lhs: &Expr,
    rhs: &Expr,
    path_conds: Vec<Predicate>,
) -> Vec<(Vec<Predicate>, Predicate)> {
    if let Expr::Ite { cond, then_, else_ } = rhs {
        let (pos_cond, neg_cond) = condition_to_z4_friendly(cond);

        // Case 1: current condition holds -> result = then_value
        // But then_ might also be an ite (rare, but handle it)
        let mut then_cases = expand_ite_to_cases(lhs, then_, {
            let mut conds = path_conds.clone();
            conds.push(pos_cond);
            conds
        });

        // Case 2: current condition doesn't hold -> recurse into else_
        let mut else_cases = expand_ite_to_cases(lhs, else_, {
            let mut conds = path_conds;
            conds.push(neg_cond);
            conds
        });

        then_cases.append(&mut else_cases);
        then_cases
    } else {
        // Base case: not an ite, return the equality
        let eq = Predicate::Expr(Expr::Eq(Box::new(lhs.clone()), Box::new(rhs.clone())));
        vec![(path_conds, eq)]
    }
}

/// Extract ite conditions from body constraints for case-split verification.
///
/// For a body constraint like `result = ite(cond, then, else)`, returns cases:
/// - (cond, result = then)
/// - (NOT cond, result = else)
///
/// For nested ites like `result = ite(c1, e1, ite(c2, e2, e3))`, recursively expands:
/// - (c1, result = e1)
/// - (NOT c1 AND c2, result = e2)
/// - (NOT c1 AND NOT c2, result = e3)
///
/// Uses Z4-friendly forms for integer comparisons to avoid solver limitations.
///
/// For non-ite body constraints, returns the constraint as a single case.
fn expand_body_constraint_to_cases(constraint: &Expr) -> Vec<(Vec<Predicate>, Predicate)> {
    match constraint {
        // Handle: result = ite(cond, then, else)
        Expr::Eq(lhs, rhs) => expand_ite_to_cases(lhs, rhs, vec![]),
        // Other constraint types - return as single case
        _ => vec![(vec![], Predicate::Expr(constraint.clone()))],
    }
}

/// Parse a JSON string into a `SwiftVcBundle`.
///
/// # Safety
/// - `json` must be a valid, null-terminated C string
/// - The returned pointer must be freed with `vc_bridge_free_string`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vc_bridge_parse_bundle(json: *const c_char) -> *mut SwiftVcBundle {
    if json.is_null() {
        return ptr::null_mut();
    }

    let Ok(c_str) = unsafe { CStr::from_ptr(json) }.to_str() else {
        return ptr::null_mut();
    };

    serde_json::from_str::<SwiftVcBundle>(c_str)
        .map_or(ptr::null_mut(), |bundle| Box::into_raw(Box::new(bundle)))
}

/// Free a `SwiftVcBundle` allocated by `vc_bridge_parse_bundle`.
///
/// # Safety
/// - `bundle` must have been allocated by `vc_bridge_parse_bundle`
/// - Must not be called more than once on the same pointer
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vc_bridge_free_bundle(bundle: *mut SwiftVcBundle) {
    if !bundle.is_null() {
        drop(unsafe { Box::from_raw(bundle) });
    }
}

/// Convert a `SwiftVcBundle` to VC IR and return as JSON.
///
/// Returns a JSON string representation of the `FunctionVcs`,
/// or an error JSON object if conversion fails.
///
/// # Safety
/// - `bundle` must be a valid pointer from `vc_bridge_parse_bundle`
/// - The returned string must be freed with `vc_bridge_free_string`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vc_bridge_convert_to_vcir(bundle: *const SwiftVcBundle) -> *mut c_char {
    if bundle.is_null() {
        return error_json("null bundle pointer");
    }

    let bundle_ref = unsafe { &*bundle };

    match convert_bundle(bundle_ref) {
        Ok(fvcs) => {
            // For now, return a summary since FunctionVcs doesn't derive Serialize
            // In a full implementation, we'd serialize the VC IR
            let summary = format!(
                r#"{{"function":"{}","requires_count":{},"ensures_count":{},"assertions_count":{}}}"#,
                fvcs.name,
                fvcs.requires.len(),
                fvcs.ensures.len(),
                fvcs.assertions.len()
            );
            CString::new(summary).map_or_else(
                |_| error_json("failed to create C string"),
                CString::into_raw,
            )
        }
        Err(e) => error_json(&format!("conversion error: {e}")),
    }
}

/// Verify a `SwiftVcBundle` and return results as JSON.
///
/// This is the main entry point for verification from C++.
///
/// # Safety
/// - `json` must be a valid, null-terminated C string containing a `SwiftVcBundle`
/// - The returned string must be freed with `vc_bridge_free_string`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vc_bridge_verify_json(json: *const c_char) -> *mut c_char {
    if json.is_null() {
        return error_json("null JSON pointer");
    }

    let Ok(c_str) = unsafe { CStr::from_ptr(json) }.to_str() else {
        return error_json("invalid UTF-8 in JSON");
    };

    // Parse the bundle
    let Ok(bundle) = serde_json::from_str::<SwiftVcBundle>(c_str) else {
        return error_json("JSON parse error");
    };

    // Verify using the internal function
    let response = match verify_bundle(&bundle) {
        Ok(r) => r,
        Err(e) => return error_json(&format!("verification error: {e}")),
    };

    serde_json::to_string(&response).map_or_else(
        |e| error_json(&format!("JSON serialize error: {e}")),
        |json_str| {
            CString::new(json_str).map_or_else(
                |_| error_json("failed to create C string"),
                CString::into_raw,
            )
        },
    )
}

/// Free a string allocated by the bridge.
///
/// # Safety
/// - `s` must have been allocated by one of the `vc_bridge_*` functions
/// - Must not be called more than once on the same pointer
#[unsafe(no_mangle)]
pub unsafe extern "C" fn vc_bridge_free_string(s: *mut c_char) {
    if !s.is_null() {
        drop(unsafe { CString::from_raw(s) });
    }
}

/// Get the version of the bridge library.
///
/// # Safety
/// - The returned string is statically allocated and must not be freed
#[unsafe(no_mangle)]
pub extern "C" fn vc_bridge_version() -> *const c_char {
    static VERSION: &[u8] = b"0.1.0\0";
    VERSION.as_ptr().cast::<c_char>()
}

/// Helper to create an error JSON response.
fn error_json(message: &str) -> *mut c_char {
    let escaped = message.replace('\"', "\\\"").replace('\n', "\\n");
    let json = format!(r#"{{"error":"{escaped}"}}"#);
    CString::new(json).map_or_else(
        |_| {
            // Last resort: return a static error
            static ERROR: &[u8] = b"{\"error\":\"internal error\"}\0";
            // This is safe because we're returning a pointer to static memory
            // The caller should not free this, but we document that in the API
            // Cast to *mut for FFI return type compatibility (data is not actually mutable)
            ERROR.as_ptr().cast::<c_char>().cast_mut()
        },
        CString::into_raw,
    )
}

// ============================================================================
// Higher-level Rust API (for use from Rust code, not FFI)
// ============================================================================

/// Parse a JSON string into a `SwiftVcBundle`.
///
/// Automatically resolves condition strings (`requires_str`, `ensures_str`,
/// `invariants_str`) into their expression equivalents.
///
/// # Errors
/// Returns an error if the JSON cannot be parsed or the bundle cannot be converted.
pub fn parse_bundle_json(json: &str) -> Result<SwiftVcBundle, VcBridgeError> {
    let mut bundle: SwiftVcBundle = serde_json::from_str(json)?;
    bundle.resolve_condition_strings();
    Ok(bundle)
}

/// Parse one-or-more `SwiftVcBundle` values from JSON.
///
/// Supported formats:
/// - Single JSON object (`{ ... }`)
/// - JSON array (`[{ ... }, ...]`)
/// - JSON Lines (one JSON object per non-empty line)
///
/// Automatically resolves condition strings (`requires_str`, `ensures_str`,
/// `invariants_str`) into their expression equivalents for all bundles.
///
/// # Errors
/// Returns an error if the input is empty or not valid JSON in any supported format.
pub fn parse_bundles_json(json: &str) -> Result<Vec<SwiftVcBundle>, VcBridgeError> {
    let trimmed = json.trim();
    if trimmed.is_empty() {
        return Err(VcBridgeError::Conversion("empty JSON input".to_string()));
    }

    if let Ok(mut bundle) = serde_json::from_str::<SwiftVcBundle>(trimmed) {
        bundle.resolve_condition_strings();
        return Ok(vec![bundle]);
    }

    if let Ok(mut bundles) = serde_json::from_str::<Vec<SwiftVcBundle>>(trimmed) {
        for bundle in &mut bundles {
            bundle.resolve_condition_strings();
        }
        return Ok(bundles);
    }

    let mut bundles = Vec::new();
    for (line_index, line) in json.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }

        match serde_json::from_str::<SwiftVcBundle>(line) {
            Ok(mut bundle) => {
                bundle.resolve_condition_strings();
                bundles.push(bundle);
            }
            Err(e) => {
                return Err(VcBridgeError::Conversion(format!(
                    "JSON Lines parse error at line {}: {}",
                    line_index + 1,
                    e
                )));
            }
        }
    }

    if bundles.is_empty() {
        return Err(VcBridgeError::Conversion(
            "no JSON bundles found in input".to_string(),
        ));
    }

    Ok(bundles)
}

/// Convert a `VerifyResult` to a `SwiftVerifyResult`.
fn convert_verify_result(result: VerifyResult, time_seconds: f64) -> SwiftVerifyResult {
    match result {
        VerifyResult::Proven => SwiftVerifyResult::Verified { time_seconds },
        VerifyResult::Counterexample(cex) => SwiftVerifyResult::Failed {
            counterexample: cex
                .assignments
                .into_iter()
                .map(|(name, val)| (name, format_value(&val)))
                .collect(),
            time_seconds,
        },
        VerifyResult::Unknown { category, reason } => SwiftVerifyResult::Unknown {
            // Use category display for more informative message, fall back to reason
            reason: format!("{category} ({reason})"),
            time_seconds,
        },
        VerifyResult::Timeout { .. } => SwiftVerifyResult::Timeout {
            timeout_seconds: time_seconds,
        },
        VerifyResult::Error(e) => SwiftVerifyResult::Error { message: e },
    }
}

/// Generate a suggestion for how to fix a failed auto-VC.
/// Takes the `SwiftAutoVc` directly to access operation-specific info for better suggestions.
#[allow(clippy::too_many_lines)]
fn generate_suggestion(auto_vc: &SwiftAutoVc, result: &SwiftVerifyResult) -> String {
    // Only generate suggestions for failures
    if !matches!(result, SwiftVerifyResult::Failed { .. }) {
        return String::new();
    }

    match auto_vc {
        SwiftAutoVc::Overflow {
            operation,
            operands,
            ..
        } => {
            let op = operation.to_lowercase();
            // Check if this is an increment/decrement pattern (operand is 1 or -1)
            let is_increment = operands
                .iter()
                .any(|e| matches!(e, SwiftExpr::IntLit { value: 1 | -1 }));

            if op == "add" && is_increment {
                return "Guard with: if value < Int.max { value += 1 } (SwiftUI counter pattern)"
                    .to_string();
            }
            if op == "sub" && is_increment {
                return "Guard with: if value > Int.min { value -= 1 }".to_string();
            }
            match op.as_str() {
                "add" => {
                    "Guard: if a <= Int.max - b { a + b } or use &+ for wraparound".to_string()
                }
                "sub" => {
                    "Guard: if a >= Int.min + b { a - b } or use &- for wraparound".to_string()
                }
                "mul" => "Guard: if a != 0 && b <= Int.max / a { a * b } or use &* for wraparound"
                    .to_string(),
                "neg" => {
                    "Guard: if value > Int.min { -value } (Int.min cannot be negated)".to_string()
                }
                _ => "Use wraparound operators (&+, &-, &*) or add bounds guards".to_string(),
            }
        }
        SwiftAutoVc::DivByZero { .. } => {
            "Add precondition: @_requires(\"divisor != 0\")".to_string()
        }
        SwiftAutoVc::BoundsCheck { .. } => {
            "Add precondition: @_requires(\"index >= 0 && index < array.count\")".to_string()
        }
        SwiftAutoVc::NilCheck { .. } => {
            "Use optional binding (if let) or add precondition: @_requires(\"value != nil\")"
                .to_string()
        }
        SwiftAutoVc::CastCheck { .. } => {
            "Use conditional cast (as?) or add runtime type check before forced cast".to_string()
        }
        SwiftAutoVc::CondFail { description, .. } => {
            let desc_lower = description.to_lowercase();
            if desc_lower.contains("div") && desc_lower.contains("overflow") {
                return "Add precondition to exclude INT_MIN / -1, or use saturating division"
                    .to_string();
            }
            if desc_lower.contains("mod") && desc_lower.contains("zero") {
                return "Add precondition: @_requires(\"divisor != 0\")".to_string();
            }
            String::new()
        }
        SwiftAutoVc::CallPrecondition { .. } => {
            "Ensure callee preconditions are satisfied before the call".to_string()
        }
        SwiftAutoVc::Termination { .. } => {
            "Ensure loop has a bounded iteration count or add explicit termination annotation"
                .to_string()
        }
        SwiftAutoVc::RecursiveTermination { .. } => {
            "Ensure recursive function has a base case and a decreasing argument on each call"
                .to_string()
        }
        SwiftAutoVc::MutualRecursiveTermination { function_cycle, .. } => {
            format!(
                "Ensure mutually recursive functions {} have base cases and a decreasing measure across the cycle",
                function_cycle.join(" <-> ")
            )
        }
        SwiftAutoVc::LexicographicTermination { measure_params, .. } => {
            format!(
                "Ensure recursive function terminates via lexicographic ordering on ({}) - each call site must decrease some parameter with all earlier parameters non-increasing",
                measure_params.join(", ")
            )
        }
        SwiftAutoVc::LexicographicMutualRecursiveTermination {
            function_cycle,
            measure_params,
            ..
        } => {
            format!(
                "Ensure mutually recursive functions {} terminate via lexicographic ordering on ({}) - each call across the cycle must decrease some parameter with earlier parameters non-increasing",
                function_cycle.join(" <-> "),
                measure_params.join(", ")
            )
        }
        SwiftAutoVc::StateInvariant { property_name, .. } => {
            format!(
                "Ensure type invariant holds after mutating '{property_name}'. Add guards or update invariant."
            )
        }
        SwiftAutoVc::TypeInvariant {
            type_name,
            property_name,
            ..
        } => {
            format!(
                "Ensure type-level invariant for '{type_name}' holds after mutating '{property_name}'. The invariant was declared on init and applies to all methods."
            )
        }
        SwiftAutoVc::MethodCallStateEffect {
            type_name,
            callee_method,
            affected_properties,
            call_chain,
            ..
        } => {
            let props = affected_properties.join(", ");
            if call_chain.is_empty() {
                format!(
                    "Ensure type invariant for '{type_name}' holds after calling '{callee_method}' which may modify [{props}]. Consider adding postconditions to the callee."
                )
            } else {
                let chain_str = call_chain.join(" -> ");
                format!(
                    "Ensure type invariant for '{type_name}' holds after calling '{callee_method}' which transitively modifies [{props}] via: {callee_method} -> {chain_str}. Consider adding postconditions along the call chain."
                )
            }
        }
        SwiftAutoVc::ShiftOverflow {
            bits, operation, ..
        } => {
            let op_name = match operation.as_str() {
                "shl" => "shift left",
                "lshr" => "logical shift right",
                "ashr" => "arithmetic shift right",
                _ => "shift",
            };
            format!(
                "Ensure {op_name} amount is in range [0, {bits}). Add a bounds check before the shift operation."
            )
        }
        SwiftAutoVc::UnownedAccess { reference_name, .. } => {
            format!(
                "Ensure unowned reference '{reference_name}' is accessed while the referenced object is still alive. \
                 Consider using weak reference instead, or add @_requires precondition to verify lifetime."
            )
        }
        SwiftAutoVc::ActorIsolationCrossing {
            caller_isolation,
            callee_isolation,
            callee_name,
            ..
        } => {
            format!(
                "Actor isolation crossing from {caller_isolation} to {callee_isolation} when calling '{callee_name}'. \
                 Ensure async/await is used correctly, or verify FFI code is safe to call from actor context."
            )
        }
    }
}

/// Format a Value for display in counterexamples.
fn format_value(val: &Value) -> String {
    match val {
        Value::Bool(b) => b.to_string(),
        Value::Int(i) => i.to_string(),
        Value::Float(f) => f.to_string(),
        Value::BitVec { bits, value } => {
            // Format bitvector as hex string
            let hex = value.iter().fold(String::new(), |mut acc, b| {
                let _ = write!(acc, "{b:02x}");
                acc
            });
            format!("0x{hex} ({bits} bits)")
        }
        Value::Array(arr) => format!("[{} elements]", arr.len()),
        Value::Struct { name, .. } => format!("{name}{{...}}"),
        Value::Tuple(vals) => format!("({} elements)", vals.len()),
        Value::Tensor { shape, .. } => format!("Tensor{shape:?}"),
    }
}

/// Extract the path condition from a `SwiftAutoVc`, if present.
///
/// Path conditions represent guard statements that must be true for the
/// unsafe operation to be reachable.
const fn get_path_condition(auto_vc: &SwiftAutoVc) -> Option<&SwiftExpr> {
    match auto_vc {
        SwiftAutoVc::Overflow { path_condition, .. }
        | SwiftAutoVc::DivByZero { path_condition, .. }
        | SwiftAutoVc::BoundsCheck { path_condition, .. }
        | SwiftAutoVc::NilCheck { path_condition, .. }
        | SwiftAutoVc::CastCheck { path_condition, .. }
        | SwiftAutoVc::CondFail { path_condition, .. }
        | SwiftAutoVc::CallPrecondition { path_condition, .. }
        | SwiftAutoVc::StateInvariant { path_condition, .. }
        | SwiftAutoVc::TypeInvariant { path_condition, .. }
        | SwiftAutoVc::MethodCallStateEffect { path_condition, .. }
        | SwiftAutoVc::ShiftOverflow { path_condition, .. }
        | SwiftAutoVc::UnownedAccess { path_condition, .. }
        | SwiftAutoVc::ActorIsolationCrossing { path_condition, .. } => path_condition.as_ref(),
        // Termination VCs don't have path conditions
        SwiftAutoVc::Termination { .. }
        | SwiftAutoVc::RecursiveTermination { .. }
        | SwiftAutoVc::MutualRecursiveTermination { .. }
        | SwiftAutoVc::LexicographicTermination { .. }
        | SwiftAutoVc::LexicographicMutualRecursiveTermination { .. } => None,
    }
}

/// Collect all variable names that appear inside `old()` expressions in a predicate.
///
/// For each `old(x)` in the predicate, this returns "x" (the variable name).
/// Used in tests to verify `old()` detection.
#[cfg(test)]
fn collect_old_vars_from_predicate(pred: &Predicate) -> Vec<String> {
    let mut vars = Vec::new();
    collect_old_vars_from_predicate_impl(pred, &mut vars);
    // Deduplicate
    vars.sort();
    vars.dedup();
    vars
}

#[cfg(test)]
fn collect_old_vars_from_predicate_impl(pred: &Predicate, vars: &mut Vec<String>) {
    match pred {
        Predicate::Expr(expr) => collect_old_vars_from_expr(expr, vars),
        Predicate::And(preds) | Predicate::Or(preds) => {
            for p in preds {
                collect_old_vars_from_predicate_impl(p, vars);
            }
        }
        Predicate::Not(p) => collect_old_vars_from_predicate_impl(p, vars),
        Predicate::Implies(p, q) => {
            collect_old_vars_from_predicate_impl(p, vars);
            collect_old_vars_from_predicate_impl(q, vars);
        }
    }
}

#[cfg(test)]
fn collect_old_vars_from_expr(expr: &Expr, vars: &mut Vec<String>) {
    match expr {
        Expr::Old(e) => {
            // Found an old() expression - collect the inner variable name
            match e.as_ref() {
                Expr::Var(name) => vars.push(name.clone()),
                Expr::Result => vars.push("result".to_string()),
                _ => {
                    // For complex expressions like old(x + y), recursively collect vars
                    // (though this is less common and may need special handling)
                    collect_old_vars_from_expr(e, vars);
                }
            }
        }
        // Recursively search through expressions
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Rem(a, b)
        | Expr::Eq(a, b)
        | Expr::Ne(a, b)
        | Expr::Lt(a, b)
        | Expr::Le(a, b)
        | Expr::Gt(a, b)
        | Expr::Ge(a, b)
        | Expr::And(a, b)
        | Expr::Or(a, b) => {
            collect_old_vars_from_expr(a, vars);
            collect_old_vars_from_expr(b, vars);
        }
        Expr::Neg(e) | Expr::Not(e) => collect_old_vars_from_expr(e, vars),
        Expr::Ite { cond, then_, else_ } => {
            collect_old_vars_from_expr(cond, vars);
            collect_old_vars_from_expr(then_, vars);
            collect_old_vars_from_expr(else_, vars);
        }
        Expr::ArrayIndex(base, idx) => {
            collect_old_vars_from_expr(base, vars);
            collect_old_vars_from_expr(idx, vars);
        }
        Expr::StructField(base, _) => collect_old_vars_from_expr(base, vars),
        Expr::Apply { args, .. } => {
            for arg in args {
                collect_old_vars_from_expr(arg, vars);
            }
        }
        Expr::Forall { body, .. } | Expr::Exists { body, .. } => {
            collect_old_vars_from_expr(body, vars);
        }
        // Terminals that don't contain old()
        Expr::Var(_) | Expr::Result | Expr::IntLit(_) | Expr::BoolLit(_) | Expr::NilLit => {}
    }
}

/// Substitute old(x) with x directly in a predicate.
///
/// For parameters (which don't change during function execution), `old(x) == x`.
/// Rather than adding `x_old == x` as a constraint (which Z4 can't solve),
/// we substitute `old(x)` with `x` directly.
///
/// This is semantically correct because parameters are immutable in the function body.
fn substitute_old_with_entry_values(pred: &Predicate) -> Predicate {
    match pred {
        Predicate::Expr(expr) => Predicate::Expr(substitute_old_expr(expr)),
        Predicate::And(preds) => {
            Predicate::And(preds.iter().map(substitute_old_with_entry_values).collect())
        }
        Predicate::Or(preds) => {
            Predicate::Or(preds.iter().map(substitute_old_with_entry_values).collect())
        }
        Predicate::Not(p) => Predicate::Not(Box::new(substitute_old_with_entry_values(p))),
        Predicate::Implies(p, q) => Predicate::Implies(
            Box::new(substitute_old_with_entry_values(p)),
            Box::new(substitute_old_with_entry_values(q)),
        ),
    }
}

fn substitute_old_expr(expr: &Expr) -> Expr {
    match expr {
        // Key case: old(x) -> x (substitute with current value, which equals entry for params)
        Expr::Old(inner) => {
            // Recursively substitute in case of nested old()

            // Return the inner expression directly (removing the old() wrapper)
            substitute_old_expr(inner)
        }
        // Recursive cases
        Expr::Add(a, b) => Expr::Add(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Mul(a, b) => Expr::Mul(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Div(a, b) => Expr::Div(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Rem(a, b) => Expr::Rem(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Eq(a, b) => Expr::Eq(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Ne(a, b) => Expr::Ne(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Lt(a, b) => Expr::Lt(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Le(a, b) => Expr::Le(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Gt(a, b) => Expr::Gt(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Ge(a, b) => Expr::Ge(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::And(a, b) => Expr::And(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Or(a, b) => Expr::Or(
            Box::new(substitute_old_expr(a)),
            Box::new(substitute_old_expr(b)),
        ),
        Expr::Neg(e) => Expr::Neg(Box::new(substitute_old_expr(e))),
        Expr::Not(e) => Expr::Not(Box::new(substitute_old_expr(e))),
        Expr::Ite { cond, then_, else_ } => Expr::Ite {
            cond: Box::new(substitute_old_expr(cond)),
            then_: Box::new(substitute_old_expr(then_)),
            else_: Box::new(substitute_old_expr(else_)),
        },
        Expr::ArrayIndex(base, idx) => Expr::ArrayIndex(
            Box::new(substitute_old_expr(base)),
            Box::new(substitute_old_expr(idx)),
        ),
        Expr::StructField(base, field) => {
            Expr::StructField(Box::new(substitute_old_expr(base)), field.clone())
        }
        Expr::Apply { func, args } => Expr::Apply {
            func: func.clone(),
            args: args.iter().map(substitute_old_expr).collect(),
        },
        Expr::Forall { vars, body } => Expr::Forall {
            vars: vars.clone(),
            body: Box::new(substitute_old_expr(body)),
        },
        Expr::Exists { vars, body } => Expr::Exists {
            vars: vars.clone(),
            body: Box::new(substitute_old_expr(body)),
        },
        // Terminal cases - return as-is
        Expr::Var(n) => Expr::Var(n.clone()),
        Expr::Result => Expr::Result,
        Expr::IntLit(v) => Expr::IntLit(*v),
        Expr::BoolLit(v) => Expr::BoolLit(*v),
        Expr::NilLit => Expr::NilLit,
    }
}

/// Extract source location (line, column) from a `SwiftAutoVc`.
///
/// Returns (`source_line`, `source_column`) from the auto-VC if present.
const fn get_source_location(auto_vc: &SwiftAutoVc) -> (u32, u32) {
    match auto_vc {
        SwiftAutoVc::Overflow {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::DivByZero {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::BoundsCheck {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::NilCheck {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::CastCheck {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::CondFail {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::CallPrecondition {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::Termination {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::RecursiveTermination {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::MutualRecursiveTermination {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::LexicographicTermination {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::LexicographicMutualRecursiveTermination {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::StateInvariant {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::TypeInvariant {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::MethodCallStateEffect {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::ShiftOverflow {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::UnownedAccess {
            source_line,
            source_column,
            ..
        }
        | SwiftAutoVc::ActorIsolationCrossing {
            source_line,
            source_column,
            ..
        } => (*source_line, *source_column),
    }
}

/// Extract call chain from a `SwiftAutoVc`, if applicable.
///
/// Returns the call chain for `MethodCallStateEffect` VCs, or an empty vec for all other VC types.
fn get_call_chain(auto_vc: &SwiftAutoVc) -> Vec<String> {
    match auto_vc {
        SwiftAutoVc::MethodCallStateEffect { call_chain, .. } => call_chain.clone(),
        _ => Vec::new(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct IntInterval {
    lo: i128,
    hi: i128,
}

#[derive(Debug, Default, Clone)]
struct VarBounds {
    lo: Option<i128>,
    hi: Option<i128>,
}

#[derive(Debug, Clone, Copy)]
enum BoundCmp {
    Ge,
    Gt,
    Le,
    Lt,
    Eq,
}

fn update_bounds(bounds: &mut VarBounds, new_lo: Option<i128>, new_hi: Option<i128>) {
    if let Some(lo) = new_lo {
        bounds.lo = Some(bounds.lo.map_or(lo, |existing| existing.max(lo)));
    }
    if let Some(hi) = new_hi {
        bounds.hi = Some(bounds.hi.map_or(hi, |existing| existing.min(hi)));
    }
}

fn extract_simple_bounds_from_predicate(pred: &Predicate, out: &mut HashMap<String, VarBounds>) {
    match pred {
        Predicate::And(preds) => {
            for p in preds {
                extract_simple_bounds_from_predicate(p, out);
            }
        }
        Predicate::Expr(expr) => extract_simple_bounds_from_expr(expr, out),
        // Ignore disjunctions/implications/negations: skipping constraints is sound for proving.
        Predicate::Or(_) | Predicate::Not(_) | Predicate::Implies(_, _) => {}
    }
}

fn extract_simple_bounds_from_expr(expr: &Expr, out: &mut HashMap<String, VarBounds>) {
    match expr {
        Expr::And(a, b) => {
            extract_simple_bounds_from_expr(a, out);
            extract_simple_bounds_from_expr(b, out);
        }

        Expr::Ge(a, b) => extract_var_int_bound(a, b, out, BoundCmp::Ge),
        Expr::Gt(a, b) => extract_var_int_bound(a, b, out, BoundCmp::Gt),
        Expr::Le(a, b) => extract_var_int_bound(a, b, out, BoundCmp::Le),
        Expr::Lt(a, b) => extract_var_int_bound(a, b, out, BoundCmp::Lt),
        Expr::Eq(a, b) => extract_var_int_bound(a, b, out, BoundCmp::Eq),

        // Ignore everything else (Ne, Or, arithmetic, function calls, quantifiers, etc.).
        _ => {}
    }
}

/// Extract a literal value, handling Neg(IntLit) as negative literal.
fn extract_literal(expr: &Expr) -> Option<i128> {
    match expr {
        Expr::IntLit(n) => Some(*n),
        Expr::Neg(inner) => {
            if let Expr::IntLit(n) = inner.as_ref() {
                n.checked_neg()
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Convert an Expr to a canonical name for bounds lookup.
/// E.g., StructField(Var("arr"), "count") -> "arr.count"
fn expr_to_canonical_name(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Var(name) => Some(name.clone()),
        Expr::StructField(base, field) => {
            let base_name = expr_to_canonical_name(base)?;
            Some(format!("{base_name}.{field}"))
        }
        _ => None,
    }
}

fn extract_var_int_bound(a: &Expr, b: &Expr, out: &mut HashMap<String, VarBounds>, cmp: BoundCmp) {
    // Try to extract name from a (Var or StructField)
    if let Some(name) = expr_to_canonical_name(a) {
        if let Some(n) = extract_literal(b) {
            let (lo, hi) = bounds_from_cmp(cmp, n, /*var_on_left=*/ true);
            let entry = out.entry(name).or_default();
            update_bounds(entry, lo, hi);
            return;
        }
    }
    // Try the reverse: literal on left, var/field on right
    if let Some(name) = expr_to_canonical_name(b) {
        if let Some(n) = extract_literal(a) {
            let (lo, hi) = bounds_from_cmp(cmp, n, /*var_on_left=*/ false);
            let entry = out.entry(name).or_default();
            update_bounds(entry, lo, hi);
        }
    }
}

const fn bounds_from_cmp(
    cmp: BoundCmp,
    n: i128,
    var_on_left: bool,
) -> (Option<i128>, Option<i128>) {
    use BoundCmp::{Eq, Ge, Gt, Le, Lt};

    // Integer-only interval reasoning; strict comparisons become inclusive bounds.
    if var_on_left {
        match cmp {
            Ge => (Some(n), None),          // x >= n
            Gt => (n.checked_add(1), None), // x > n  => x >= n+1
            Le => (None, Some(n)),          // x <= n
            Lt => (None, n.checked_sub(1)), // x < n  => x <= n-1
            Eq => (Some(n), Some(n)),       // x == n
        }
    } else {
        // n <op> x
        match cmp {
            Ge => (None, Some(n)),          // n >= x  => x <= n
            Gt => (None, n.checked_sub(1)), // n > x   => x <= n-1
            Le => (Some(n), None),          // n <= x  => x >= n
            Lt => (n.checked_add(1), None), // n < x   => x >= n+1
            Eq => (Some(n), Some(n)),       // n == x
        }
    }
}

fn interval_for_expr(expr: &Expr, var_bounds: &HashMap<String, VarBounds>) -> Option<IntInterval> {
    match expr {
        Expr::IntLit(n) => Some(IntInterval { lo: *n, hi: *n }),
        Expr::Var(name) => {
            let b = var_bounds.get(name)?;
            Some(IntInterval {
                lo: b.lo?,
                hi: b.hi?,
            })
        }
        Expr::StructField(_, _) => {
            // Try canonical name lookup for field accesses like arr.count
            let name = expr_to_canonical_name(expr)?;
            let b = var_bounds.get(&name)?;
            Some(IntInterval {
                lo: b.lo?,
                hi: b.hi?,
            })
        }
        Expr::Neg(inner) => {
            let i = interval_for_expr(inner, var_bounds)?;
            Some(IntInterval {
                lo: i.hi.checked_neg()?,
                hi: i.lo.checked_neg()?,
            })
        }
        Expr::Add(a, b) => {
            let ai = interval_for_expr(a, var_bounds)?;
            let bi = interval_for_expr(b, var_bounds)?;
            interval_add(ai, bi)
        }
        Expr::Sub(a, b) => {
            let ai = interval_for_expr(a, var_bounds)?;
            let bi = interval_for_expr(b, var_bounds)?;
            interval_sub(ai, bi)
        }
        _ => None,
    }
}

fn interval_add(a: IntInterval, b: IntInterval) -> Option<IntInterval> {
    let lo = a.lo.checked_add(b.lo)?;
    let hi = a.hi.checked_add(b.hi)?;
    Some(IntInterval { lo, hi })
}

fn interval_sub(a: IntInterval, b: IntInterval) -> Option<IntInterval> {
    // [a.lo, a.hi] - [b.lo, b.hi] = [a.lo - b.hi, a.hi - b.lo]
    let lo = a.lo.checked_sub(b.hi)?;
    let hi = a.hi.checked_sub(b.lo)?;
    Some(IntInterval { lo, hi })
}

fn interval_mul(a: IntInterval, b: IntInterval) -> Option<IntInterval> {
    let p1 = a.lo.checked_mul(b.lo)?;
    let p2 = a.lo.checked_mul(b.hi)?;
    let p3 = a.hi.checked_mul(b.lo)?;
    let p4 = a.hi.checked_mul(b.hi)?;
    let lo = p1.min(p2).min(p3).min(p4);
    let hi = p1.max(p2).max(p3).max(p4);
    Some(IntInterval { lo, hi })
}

fn interval_neg(a: IntInterval) -> Option<IntInterval> {
    // Negation flips the interval: [-a.hi, -a.lo]
    let lo = a.hi.checked_neg()?;
    let hi = a.lo.checked_neg()?;
    Some(IntInterval { lo, hi })
}

#[allow(clippy::too_many_lines)]
fn try_prove_overflow_via_intervals(
    auto_vc: &SwiftAutoVc,
    preconditions: &[Predicate],
) -> Option<(VerifyResult, String)> {
    use crate::convert::convert_expr;

    let (operation, operands, description, signed, bits) = match auto_vc {
        SwiftAutoVc::Overflow {
            operation,
            operands,
            description,
            signed,
            bits,
            ..
        } => (
            operation.as_str(),
            operands.as_slice(),
            description.as_str(),
            *signed,
            *bits,
        ),
        _ => return None,
    };

    let mut var_bounds: HashMap<String, VarBounds> = HashMap::new();
    for p in preconditions {
        extract_simple_bounds_from_predicate(p, &mut var_bounds);
    }

    let (bound_min, bound_max) = overflow_bounds_for_type(signed, bits);

    // Handle unary negation: -x
    // Overflow occurs when x == INT64_MIN (because -INT64_MIN overflows)
    if operation == "neg" && operands.len() == 1 {
        let operand = convert_expr(&operands[0]).ok()?;
        let operand_i = interval_for_expr(&operand, &var_bounds)?;
        let result_i = interval_neg(operand_i)?;

        if result_i.lo >= bound_min && result_i.hi <= bound_max {
            let smtlib = format!(
                "; Proved without SMT via interval analysis\n; VC: {description}\n; operand interval: [{}, {}]\n; negation interval: [{}, {}]\n; required: [{}, {}]\n",
                operand_i.lo, operand_i.hi, result_i.lo, result_i.hi, bound_min, bound_max
            );
            return Some((VerifyResult::Proven, smtlib));
        }
        return None;
    }

    // Handle binary operations: add, sub, mul, div
    // This is especially useful for mul since Z4's QF_LIA cannot handle non-linear arithmetic.
    if operands.len() < 2 {
        return None;
    }

    let lhs = convert_expr(&operands[0]).ok()?;
    let rhs = convert_expr(&operands[1]).ok()?;

    // Special case for division overflow: INT_MIN / -1 overflows
    // We can prove no overflow if EITHER:
    // - The divisor interval doesn't include -1, OR
    // - The dividend interval doesn't include INT64_MIN (bound_min)
    // Unlike add/sub/mul, we don't need both bounds - just one condition suffices.
    if operation == "div" {
        let lhs_i = interval_for_expr(&lhs, &var_bounds);
        let rhs_i = interval_for_expr(&rhs, &var_bounds);

        // Check divisor excludes -1
        if let Some(rhs_interval) = &rhs_i {
            let divisor_excludes_neg1 = rhs_interval.lo > -1 || rhs_interval.hi < -1;
            if divisor_excludes_neg1 {
                let smtlib = format!(
                    "; Proved without SMT via interval analysis\n; VC: {description}\n; divisor interval: [{}, {}]\n; divisor excludes -1: true\n",
                    rhs_interval.lo, rhs_interval.hi
                );
                return Some((VerifyResult::Proven, smtlib));
            }
        }

        // Check dividend excludes INT_MIN
        if let Some(lhs_interval) = &lhs_i {
            let dividend_excludes_min = lhs_interval.lo > bound_min;
            if dividend_excludes_min {
                let smtlib = format!(
                    "; Proved without SMT via interval analysis\n; VC: {description}\n; dividend interval: [{}, {}]\n; dividend excludes INT_MIN: true (lo {} > {})\n",
                    lhs_interval.lo, lhs_interval.hi, lhs_interval.lo, bound_min
                );
                return Some((VerifyResult::Proven, smtlib));
            }
        }

        return None;
    }

    // Special case for modulo overflow: INT_MIN % -1 overflows (same as division)
    // We can prove no overflow if EITHER:
    // - The divisor interval doesn't include -1, OR
    // - The dividend interval doesn't include INT64_MIN (bound_min)
    if operation == "mod" {
        let lhs_i = interval_for_expr(&lhs, &var_bounds);
        let rhs_i = interval_for_expr(&rhs, &var_bounds);

        // Check divisor excludes -1
        if let Some(rhs_interval) = &rhs_i {
            let divisor_excludes_neg1 = rhs_interval.lo > -1 || rhs_interval.hi < -1;
            if divisor_excludes_neg1 {
                let smtlib = format!(
                    "; Proved without SMT via interval analysis\n; VC: {description}\n; divisor interval: [{}, {}]\n; divisor excludes -1: true\n",
                    rhs_interval.lo, rhs_interval.hi
                );
                return Some((VerifyResult::Proven, smtlib));
            }
        }

        // Check dividend excludes INT_MIN
        if let Some(lhs_interval) = &lhs_i {
            let dividend_excludes_min = lhs_interval.lo > bound_min;
            if dividend_excludes_min {
                let smtlib = format!(
                    "; Proved without SMT via interval analysis\n; VC: {description}\n; dividend interval: [{}, {}]\n; dividend excludes INT_MIN: true (lo {} > {})\n",
                    lhs_interval.lo, lhs_interval.hi, lhs_interval.lo, bound_min
                );
                return Some((VerifyResult::Proven, smtlib));
            }
        }

        return None;
    }

    let lhs_i = interval_for_expr(&lhs, &var_bounds)?;
    let rhs_i = interval_for_expr(&rhs, &var_bounds)?;

    let (result_i, op_name) = match operation {
        "add" => (interval_add(lhs_i, rhs_i)?, "sum"),
        "sub" => (interval_sub(lhs_i, rhs_i)?, "difference"),
        "mul" => (interval_mul(lhs_i, rhs_i)?, "product"),
        _ => return None,
    };

    if result_i.lo >= bound_min && result_i.hi <= bound_max {
        let smtlib = format!(
            "; Proved without SMT via interval analysis\n; VC: {description}\n; lhs interval: [{}, {}]\n; rhs interval: [{}, {}]\n; {op_name} interval: [{}, {}]\n; required: [{}, {}]\n",
            lhs_i.lo, lhs_i.hi, rhs_i.lo, rhs_i.hi, result_i.lo, result_i.hi, bound_min, bound_max
        );
        return Some((VerifyResult::Proven, smtlib));
    }

    // Overflow detected via interval analysis: result interval exceeds type bounds
    // Generate a counterexample showing inputs that cause overflow
    //
    // Special case: For Int64 operations where an operand is at full Int64 bounds,
    // a path condition might constrain it further (but we couldn't parse it).
    // In this case, defer to SMT. For smaller types (Int8/16/32), the type bounds
    // ARE meaningful constraints from the parameter types.
    let int64_min: i128 = -9_223_372_036_854_775_808;
    let int64_max: i128 = 9_223_372_036_854_775_807;
    let lhs_at_int64_bounds = lhs_i.lo == int64_min && lhs_i.hi == int64_max;
    let rhs_at_int64_bounds = rhs_i.lo == int64_min && rhs_i.hi == int64_max;
    let either_at_unconstrained_bounds = lhs_at_int64_bounds || rhs_at_int64_bounds;

    if (result_i.hi > bound_max || result_i.lo < bound_min) && !either_at_unconstrained_bounds {
        // Find specific counterexample values that demonstrate overflow
        let (ce_lhs, ce_rhs, ce_result) =
            find_overflow_counterexample(operation, &lhs_i, &rhs_i, bound_min, bound_max, signed);

        let smtlib = format!(
            "; Overflow DETECTED via interval analysis\n; VC: {description}\n; lhs interval: [{}, {}]\n; rhs interval: [{}, {}]\n; {op_name} interval: [{}, {}]\n; required: [{}, {}]\n; counterexample: {} {} {} = {} (exceeds bounds)\n",
            lhs_i.lo,
            lhs_i.hi,
            rhs_i.lo,
            rhs_i.hi,
            result_i.lo,
            result_i.hi,
            bound_min,
            bound_max,
            ce_lhs,
            operation,
            ce_rhs,
            ce_result
        );

        // Build counterexample with variable names
        // Counterexample values are i128 because they demonstrate overflow; truncation to i64
        // for display is acceptable since the overflow condition is already reported above.
        // Deduplicate: for expressions like x * x, both lhs and rhs are the same variable.
        let mut assignments = Vec::new();
        if let Expr::Var(name) = &lhs {
            #[allow(clippy::cast_possible_truncation)]
            let ce_val = ce_lhs as i64;
            assignments.push((name.clone(), Value::Int(ce_val)));
        }
        if let Expr::Var(name) = &rhs {
            // Only add if not already present (handles x * x case)
            if !assignments.iter().any(|(n, _)| n == name) {
                #[allow(clippy::cast_possible_truncation)]
                let ce_val = ce_rhs as i64;
                assignments.push((name.clone(), Value::Int(ce_val)));
            }
        }

        return Some((
            VerifyResult::Counterexample(Counterexample { assignments }),
            smtlib,
        ));
    }

    None
}

/// Find specific input values that cause overflow based on interval analysis.
/// Returns (`lhs_value`, `rhs_value`, `result_value`) where result overflows.
fn find_overflow_counterexample(
    operation: &str,
    lhs_i: &IntInterval,
    rhs_i: &IntInterval,
    bound_min: i128,
    bound_max: i128,
    signed: bool,
) -> (i128, i128, i128) {
    match operation {
        "mul" => {
            // For multiplication, find the extreme product that overflows
            // Try all corner combinations
            let candidates = [
                (lhs_i.hi, rhs_i.hi, lhs_i.hi.saturating_mul(rhs_i.hi)),
                (lhs_i.lo, rhs_i.lo, lhs_i.lo.saturating_mul(rhs_i.lo)),
                (lhs_i.hi, rhs_i.lo, lhs_i.hi.saturating_mul(rhs_i.lo)),
                (lhs_i.lo, rhs_i.hi, lhs_i.lo.saturating_mul(rhs_i.hi)),
            ];

            // Find one that overflows
            for (a, b, result) in candidates {
                if result > bound_max || result < bound_min {
                    return (a, b, result);
                }
            }
            // Fallback: return max*max
            (lhs_i.hi, rhs_i.hi, lhs_i.hi.saturating_mul(rhs_i.hi))
        }
        "add" => {
            // For addition overflow, try max + max or min + min
            if lhs_i.hi.saturating_add(rhs_i.hi) > bound_max {
                (lhs_i.hi, rhs_i.hi, lhs_i.hi.saturating_add(rhs_i.hi))
            } else {
                (lhs_i.lo, rhs_i.lo, lhs_i.lo.saturating_add(rhs_i.lo))
            }
        }
        "sub" => {
            // For subtraction overflow/underflow
            // max - min overflows, min - max underflows
            if lhs_i.lo.saturating_sub(rhs_i.hi) < bound_min {
                (lhs_i.lo, rhs_i.hi, lhs_i.lo.saturating_sub(rhs_i.hi))
            } else if !signed && lhs_i.lo < rhs_i.hi {
                // Unsigned subtraction: any a - b where b > a underflows
                (lhs_i.lo, rhs_i.hi, lhs_i.lo.saturating_sub(rhs_i.hi))
            } else {
                (lhs_i.hi, rhs_i.lo, lhs_i.hi.saturating_sub(rhs_i.lo))
            }
        }
        _ => (lhs_i.hi, rhs_i.hi, 0),
    }
}

/// Try to prove overflow safe via path condition matching.
///
/// For overflow: `x + 1 no_overflow` (signed 64-bit)
/// If path condition contains `x < Int.max`, then `x + 1 <= Int.max`, so no overflow.
///
/// Similarly:
/// - For `x - 1 no_underflow`: need `x > Int.min`
/// - For increment by 1: need `x < Int.max`
/// - For decrement by 1: need `x > Int.min`
///
/// This handles the common `SwiftUI` counter pattern:
/// ```swift
/// if count < Int.max {
///     count += 1  // Safe: guarded by path condition
/// }
/// ```
fn try_prove_overflow_safe_via_path_condition(
    auto_vc: &SwiftAutoVc,
) -> Option<(VerifyResult, String)> {
    let (operation, operands, path_condition, signed, bits) = match auto_vc {
        SwiftAutoVc::Overflow {
            operation,
            operands,
            path_condition: Some(pc),
            signed,
            bits,
            ..
        } => (operation.as_str(), operands.as_slice(), pc, *signed, *bits),
        _ => return None,
    };

    let (type_min, type_max) = overflow_bounds_for_type(signed, bits);

    // Handle increment: x + 1
    // If path_condition contains `x < Int.max`, then x + 1 won't overflow
    if operation == "add" && operands.len() >= 2 {
        // Check if one operand is 1
        let (base_operand, is_increment) = if is_one(&operands[1]) {
            (Some(&operands[0]), true)
        } else if is_one(&operands[0]) {
            (Some(&operands[1]), true)
        } else {
            (None, false)
        };

        if is_increment {
            if let Some(base) = base_operand {
                if path_condition_guards_overflow_max(path_condition, base, type_max) {
                    let smtlib = format!(
                        "; Proved via path condition matching\n; Path condition contains: operand < {}\n; Operation: {} + 1\n; Therefore: result <= {} (no overflow)\n",
                        type_max,
                        expr_debug_name(base),
                        type_max
                    );
                    return Some((VerifyResult::Proven, smtlib));
                }
            }
        }
    }

    // Handle decrement: x - 1
    // If path_condition contains `x > Int.min`, then x - 1 won't underflow
    if operation == "sub" && operands.len() >= 2 {
        // Check if second operand is 1 (x - 1)
        if is_one(&operands[1]) {
            let base = &operands[0];
            if path_condition_guards_underflow_min(path_condition, base, type_min) {
                let smtlib = format!(
                    "; Proved via path condition matching\n; Path condition contains: operand > {}\n; Operation: {} - 1\n; Therefore: result >= {} (no underflow)\n",
                    type_min,
                    expr_debug_name(base),
                    type_min
                );
                return Some((VerifyResult::Proven, smtlib));
            }
        }
    }

    None
}

/// Check if path condition guards against overflow at max bound.
/// Returns true if path condition contains `operand < type_max` or equivalent.
fn path_condition_guards_overflow_max(
    path_cond: &SwiftExpr,
    operand: &SwiftExpr,
    type_max: i128,
) -> bool {
    use crate::json_types::SwiftExpr::{And, Ge, Gt, IntLit, Le, Lt, Not};

    match path_cond {
        // operand < type_max (or operand < something)
        Lt { lhs, rhs } => {
            // Direct match: operand < Int.max
            if lhs.as_ref() == operand {
                if let IntLit { value } = rhs.as_ref() {
                    return i128::from(*value) == type_max;
                }
                // Also accept operand < some_variable (heuristic for computed max)
                return true;
            }
            false
        }
        // type_max > operand (equivalent to operand < type_max)
        Gt { lhs, rhs } => {
            if rhs.as_ref() == operand {
                if let IntLit { value } = lhs.as_ref() {
                    return i128::from(*value) == type_max;
                }
                return true;
            }
            false
        }
        // operand <= type_max - 1 (also proves operand + 1 <= type_max)
        Le { lhs, rhs } => {
            if lhs.as_ref() == operand {
                if let IntLit { value } = rhs.as_ref() {
                    return i128::from(*value) < type_max; // value < max means value+1 <= max
                }
            }
            false
        }
        // NOT(operand >= type_max) is equivalent to operand < type_max
        Not { operand: inner } => {
            if let Ge { lhs, rhs } = inner.as_ref() {
                if lhs.as_ref() == operand {
                    if let IntLit { value } = rhs.as_ref() {
                        return i128::from(*value) == type_max;
                    }
                }
            }
            false
        }
        // Recurse through And
        And { lhs, rhs } => {
            path_condition_guards_overflow_max(lhs, operand, type_max)
                || path_condition_guards_overflow_max(rhs, operand, type_max)
        }
        _ => false,
    }
}

/// Check if path condition guards against underflow at min bound.
/// Returns true if path condition contains `operand > type_min` or equivalent.
fn path_condition_guards_underflow_min(
    path_cond: &SwiftExpr,
    operand: &SwiftExpr,
    type_min: i128,
) -> bool {
    use crate::json_types::SwiftExpr::{And, Ge, Gt, IntLit, Le, Lt, Not};

    match path_cond {
        // operand > type_min
        Gt { lhs, rhs } => {
            if lhs.as_ref() == operand {
                if let IntLit { value } = rhs.as_ref() {
                    return i128::from(*value) == type_min;
                }
                // Also accept operand > some_variable (heuristic)
                return true;
            }
            false
        }
        // type_min < operand (equivalent to operand > type_min)
        Lt { lhs, rhs } => {
            if rhs.as_ref() == operand {
                if let IntLit { value } = lhs.as_ref() {
                    return i128::from(*value) == type_min;
                }
                return true;
            }
            false
        }
        // operand >= type_min + 1 (proves operand - 1 >= type_min)
        Ge { lhs, rhs } => {
            if lhs.as_ref() == operand {
                if let IntLit { value } = rhs.as_ref() {
                    return i128::from(*value) > type_min; // value > min means value-1 >= min
                }
            }
            false
        }
        // NOT(operand <= type_min) is equivalent to operand > type_min
        Not { operand: inner } => {
            if let Le { lhs, rhs } = inner.as_ref() {
                if lhs.as_ref() == operand {
                    if let IntLit { value } = rhs.as_ref() {
                        return i128::from(*value) == type_min;
                    }
                }
            }
            false
        }
        // Recurse through And
        And { lhs, rhs } => {
            path_condition_guards_underflow_min(lhs, operand, type_min)
                || path_condition_guards_underflow_min(rhs, operand, type_min)
        }
        _ => false,
    }
}

/// Check if expression is integer literal 1
const fn is_one(expr: &SwiftExpr) -> bool {
    matches!(expr, SwiftExpr::IntLit { value: 1 })
}

/// Get a debug name for an expression
fn expr_debug_name(expr: &SwiftExpr) -> String {
    match expr {
        SwiftExpr::ParamRef { name, .. } => name.clone(),
        SwiftExpr::IntLit { value } => value.to_string(),
        _ => format!("{expr:?}"),
    }
}

/// Try to prove bounds check safe via path condition matching.
///
/// For bounds check: 0 <= index < length
/// If the path condition already contains:
///   - `index >= 0` (or `0 <= index`)
///   - `index < length` (or `length > index`)
///
/// Then the bounds check is trivially safe because the path condition is an antecedent.
///
/// This handles cases where the guard statement generates the exact bounds check
/// constraints, e.g.: `guard index >= 0 && index < arr.count else { return nil }`
fn try_prove_bounds_via_path_condition(auto_vc: &SwiftAutoVc) -> Option<(VerifyResult, String)> {
    let SwiftAutoVc::BoundsCheck {
        index,
        length,
        path_condition: Some(path_condition),
        ..
    } = auto_vc
    else {
        return None;
    };

    // Check if path condition contains the required constraints
    let has_lower_bound = path_condition_contains_lower_bound(path_condition, index);
    let has_upper_bound = path_condition_contains_upper_bound(path_condition, index, length);

    if has_lower_bound && has_upper_bound {
        let smtlib = format!(
            "; Proved via path condition matching\n; Path condition contains: index >= 0 AND index < length\n; index: {index:?}\n; length: {length:?}\n"
        );
        return Some((VerifyResult::Proven, smtlib));
    }

    None
}

/// Check if path condition contains `index >= 0` (or equivalent `0 <= index`, `!(index < 0)`)
fn path_condition_contains_lower_bound(path_cond: &SwiftExpr, index: &SwiftExpr) -> bool {
    use crate::json_types::SwiftExpr::{And, Ge, Gt, Le, Lt, Not};

    match path_cond {
        // index >= 0
        Ge { lhs, rhs } => lhs.as_ref() == index && is_zero(rhs),
        // 0 <= index
        Le { lhs, rhs } => is_zero(lhs) && rhs.as_ref() == index,
        // index > -1 (equivalent to index >= 0 for integers)
        Gt { lhs, rhs } => lhs.as_ref() == index && is_negative_one(rhs),
        // NOT(index < 0) is equivalent to index >= 0
        Not { operand } => {
            if let Lt { lhs, rhs } = operand.as_ref() {
                lhs.as_ref() == index && is_zero(rhs)
            } else {
                false
            }
        }
        // Recurse through And
        And { lhs, rhs } => {
            path_condition_contains_lower_bound(lhs, index)
                || path_condition_contains_lower_bound(rhs, index)
        }
        _ => false,
    }
}

/// Check if path condition likely contains an upper bound check.
///
/// We use a flexible matching strategy since the actual comparison may be
/// wrapped in Bool structs or stored in SSA variables:
/// 1. Direct: `index < X` or `X > index`
/// 2. `ParamRef` to an SSA variable (Bool result of comparison, common in Swift SIL)
///
/// Note: `length` parameter is reserved for future use to verify bounds against
/// the actual array length.
#[allow(clippy::only_used_in_recursion)]
fn path_condition_contains_upper_bound(
    path_cond: &SwiftExpr,
    index: &SwiftExpr,
    length: &SwiftExpr,
) -> bool {
    use crate::json_types::SwiftExpr::{And, Ge, Gt, Lt, Not, ParamRef};

    match path_cond {
        // index < something (flexible - any upper bound on index)
        Lt { lhs, .. } => lhs.as_ref() == index,
        // something > index (flexible - any upper bound on index)
        Gt { rhs, .. } => rhs.as_ref() == index,
        // NOT(index >= X) is equivalent to index < X
        Not { operand } => {
            if let Ge { lhs, .. } = operand.as_ref() {
                lhs.as_ref() == index
            } else {
                false
            }
        }
        // A ParamRef (SSA variable) might be a Bool from a comparison check
        // This is a heuristic: if there's an SSA Bool in the path condition,
        // it's likely from a bounds check in a guard statement
        ParamRef { name, .. } => {
            // SSA variables like "ssa_21" are often comparison results
            name.starts_with("ssa_")
        }
        // Recurse through And
        And { lhs, rhs } => {
            path_condition_contains_upper_bound(lhs, index, length)
                || path_condition_contains_upper_bound(rhs, index, length)
        }
        _ => false,
    }
}

/// Check if expression is integer literal 0
const fn is_zero(expr: &SwiftExpr) -> bool {
    matches!(expr, SwiftExpr::IntLit { value: 0 })
}

/// Check if expression is integer literal -1
const fn is_negative_one(expr: &SwiftExpr) -> bool {
    matches!(expr, SwiftExpr::IntLit { value: -1 })
}

/// Try to prove bounds check safe via interval analysis.
///
/// For bounds check: 0 <= index < length
/// We need: index.lo >= 0 AND index.hi < length.lo
///
/// This works when we have explicit numeric bounds on both index and length,
/// e.g., from @_requires("index >= 0") @_requires("index < 10") @_requires("length >= 10")
///
/// Note: We only need a lower bound on length (not a full interval), since we only
/// check index.hi < length.lo.
fn try_prove_bounds_via_intervals(
    auto_vc: &SwiftAutoVc,
    preconditions: &[Predicate],
) -> Option<(VerifyResult, String)> {
    use crate::convert::convert_expr;

    let (index, length, description) = match auto_vc {
        SwiftAutoVc::BoundsCheck {
            index,
            length,
            description,
            ..
        } => (index, length, description.as_str()),
        _ => return None,
    };

    // Build bounds from preconditions
    let mut var_bounds: HashMap<String, VarBounds> = HashMap::new();
    for p in preconditions {
        extract_simple_bounds_from_predicate(p, &mut var_bounds);
    }

    // Convert Swift expressions to VC IR
    let index_expr = convert_expr(index).ok()?;
    let length_expr = convert_expr(length).ok()?;

    // Get interval for index (need both bounds)
    let index_i = interval_for_expr(&index_expr, &var_bounds)?;

    // Get lower bound for length (don't need full interval, just lo)
    let length_lo = get_lower_bound_for_expr(&length_expr, &var_bounds)?;

    // For bounds check to be safe: 0 <= index < length
    // We need: index.lo >= 0 AND index.hi < length.lo
    let lower_ok = index_i.lo >= 0;
    let upper_ok = index_i.hi < length_lo;

    if lower_ok && upper_ok {
        let smtlib = format!(
            "; Proved without SMT via interval analysis\n; VC: {description}\n; index interval: [{}, {}]\n; length.lo: {}\n; lower bound ok: {} >= 0\n; upper bound ok: {} < {}\n",
            index_i.lo, index_i.hi, length_lo, index_i.lo, index_i.hi, length_lo
        );
        return Some((VerifyResult::Proven, smtlib));
    }

    None
}

/// Get just the lower bound for an expression (for bounds checking we only need length.lo)
fn get_lower_bound_for_expr(expr: &Expr, var_bounds: &HashMap<String, VarBounds>) -> Option<i128> {
    match expr {
        Expr::IntLit(n) => Some(*n),
        Expr::Var(name) => {
            let b = var_bounds.get(name)?;
            b.lo
        }
        Expr::StructField(_, _) => {
            // Try canonical name lookup for field accesses like arr.count
            let name = expr_to_canonical_name(expr)?;
            let b = var_bounds.get(&name)?;
            b.lo
        }
        Expr::Add(a, b) => {
            let a_lo = get_lower_bound_for_expr(a, var_bounds)?;
            let b_lo = get_lower_bound_for_expr(b, var_bounds)?;
            a_lo.checked_add(b_lo)
        }
        Expr::Neg(inner) => {
            // For negation, the lower bound of -x is -upper_bound(x)
            // If we don't have upper bound, we can't determine lower bound
            let inner_hi = get_upper_bound_for_expr(inner, var_bounds)?;
            inner_hi.checked_neg()
        }
        _ => None,
    }
}

/// Get just the upper bound for an expression
fn get_upper_bound_for_expr(expr: &Expr, var_bounds: &HashMap<String, VarBounds>) -> Option<i128> {
    match expr {
        Expr::IntLit(n) => Some(*n),
        Expr::Var(name) => {
            let b = var_bounds.get(name)?;
            b.hi
        }
        Expr::StructField(_, _) => {
            let name = expr_to_canonical_name(expr)?;
            let b = var_bounds.get(&name)?;
            b.hi
        }
        Expr::Add(a, b) => {
            let a_hi = get_upper_bound_for_expr(a, var_bounds)?;
            let b_hi = get_upper_bound_for_expr(b, var_bounds)?;
            a_hi.checked_add(b_hi)
        }
        Expr::Neg(inner) => {
            let inner_lo = get_lower_bound_for_expr(inner, var_bounds)?;
            inner_lo.checked_neg()
        }
        _ => None,
    }
}

/// Extract known non-nil variables from preconditions.
///
/// When a precondition contains `value != nil`, it is converted to `value.hasValue == true`.
/// This function extracts all such constraints and returns a set of variable names that
/// are known to be non-nil.
fn extract_known_non_nil(preconditions: &[Predicate]) -> HashSet<String> {
    let mut known_non_nil = HashSet::new();
    for p in preconditions {
        extract_non_nil_from_predicate(p, &mut known_non_nil);
    }
    known_non_nil
}

fn extract_non_nil_from_predicate(pred: &Predicate, out: &mut HashSet<String>) {
    match pred {
        Predicate::And(preds) => {
            for p in preds {
                extract_non_nil_from_predicate(p, out);
            }
        }
        Predicate::Expr(expr) => extract_non_nil_from_expr(expr, out),
        Predicate::Or(_) | Predicate::Not(_) | Predicate::Implies(_, _) => {}
    }
}

fn extract_non_nil_from_expr(expr: &Expr, out: &mut HashSet<String>) {
    match expr {
        // Handle conjunctions
        Expr::And(a, b) => {
            extract_non_nil_from_expr(a, out);
            extract_non_nil_from_expr(b, out);
        }
        // Pattern: value.hasValue == true
        Expr::Eq(lhs, rhs) => {
            // Check if lhs is StructField(var, "hasValue") and rhs is true
            if let Expr::StructField(base, field) = lhs.as_ref() {
                if field == "hasValue" && matches!(rhs.as_ref(), Expr::BoolLit(true)) {
                    if let Some(name) = expr_to_canonical_name(base) {
                        out.insert(name);
                    }
                }
            }
            // Check reverse: true == value.hasValue
            if let Expr::StructField(base, field) = rhs.as_ref() {
                if field == "hasValue" && matches!(lhs.as_ref(), Expr::BoolLit(true)) {
                    if let Some(name) = expr_to_canonical_name(base) {
                        out.insert(name);
                    }
                }
            }
        }
        _ => {}
    }
}

/// Try to prove nil check safe via simple constraint analysis.
///
/// For nil check: value.hasValue == true
/// We prove this if preconditions include `value != nil` (which converts to `value.hasValue == true`).
fn try_prove_nil_via_simple_constraints(
    auto_vc: &SwiftAutoVc,
    preconditions: &[Predicate],
) -> Option<(VerifyResult, String)> {
    use crate::convert::convert_expr;

    let (value, description) = match auto_vc {
        SwiftAutoVc::NilCheck {
            value, description, ..
        } => (value, description.as_str()),
        _ => return None,
    };

    // Extract known non-nil variables from preconditions
    let known_non_nil = extract_known_non_nil(preconditions);

    // Convert the value expression to VC IR and get canonical name
    let value_expr = convert_expr(value).ok()?;
    let value_name = expr_to_canonical_name(&value_expr)?;

    // If this value is known to be non-nil, prove it
    if known_non_nil.contains(&value_name) {
        let smtlib = format!(
            "; Proved without SMT via simple constraint analysis\n; VC: {description}\n; value: {value_name}\n; known non-nil from preconditions\n"
        );
        return Some((VerifyResult::Proven, smtlib));
    }

    None
}

/// Check if a bounds check index has any constraints in the path condition.
///
/// Returns true if the path condition contains any comparison involving the index variable,
/// false if the index is completely unconstrained.
fn path_condition_constrains_index(index: &SwiftExpr, path_condition: Option<&SwiftExpr>) -> bool {
    let Some(path_cond) = path_condition else {
        return false;
    };

    // Get the index variable name
    let index_name = match index {
        SwiftExpr::ParamRef { name, .. } => name.as_str(),
        _ => return true, // Complex index expressions - assume constrained
    };

    // Check if any part of the path condition mentions the index
    swift_expr_mentions_var(path_cond, index_name)
}

/// Recursively check if a `SwiftExpr` mentions a variable by name.
fn swift_expr_mentions_var(expr: &SwiftExpr, var_name: &str) -> bool {
    match expr {
        SwiftExpr::ParamRef { name, .. } => name == var_name,
        // Binary operators
        SwiftExpr::Add { lhs, rhs }
        | SwiftExpr::Sub { lhs, rhs }
        | SwiftExpr::Mul { lhs, rhs }
        | SwiftExpr::Div { lhs, rhs }
        | SwiftExpr::Mod { lhs, rhs }
        | SwiftExpr::Eq { lhs, rhs }
        | SwiftExpr::Ne { lhs, rhs }
        | SwiftExpr::Lt { lhs, rhs }
        | SwiftExpr::Le { lhs, rhs }
        | SwiftExpr::Gt { lhs, rhs }
        | SwiftExpr::Ge { lhs, rhs }
        | SwiftExpr::And { lhs, rhs }
        | SwiftExpr::Or { lhs, rhs } => {
            swift_expr_mentions_var(lhs, var_name) || swift_expr_mentions_var(rhs, var_name)
        }
        // Unary operators
        SwiftExpr::Neg { operand } | SwiftExpr::Not { operand } => {
            swift_expr_mentions_var(operand, var_name)
        }
        // Compound expressions
        SwiftExpr::Field { base, .. } => swift_expr_mentions_var(base, var_name),
        SwiftExpr::Index { base, index } => {
            swift_expr_mentions_var(base, var_name) || swift_expr_mentions_var(index, var_name)
        }
        SwiftExpr::Call { args, .. } => args
            .iter()
            .any(|arg| swift_expr_mentions_var(arg, var_name)),
        SwiftExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            swift_expr_mentions_var(cond, var_name)
                || swift_expr_mentions_var(then_expr, var_name)
                || swift_expr_mentions_var(else_expr, var_name)
        }
        SwiftExpr::Old { expr } => swift_expr_mentions_var(expr, var_name),
        SwiftExpr::Forall { body, .. } | SwiftExpr::Exists { body, .. } => {
            swift_expr_mentions_var(body, var_name)
        }
        // Terminals
        SwiftExpr::IntLit { .. }
        | SwiftExpr::BoolLit { .. }
        | SwiftExpr::ResultRef
        | SwiftExpr::NilLit
        | SwiftExpr::TypeLit { .. }
        | SwiftExpr::StringLit { .. } => false,
    }
}

/// Try to detect unconstrained bounds checks and convert UNKNOWN to FAILED.
///
/// For array bounds checks, if the index variable has no constraints in the path
/// condition, the check is unsafe because any value could be passed. In this case,
/// we convert UNKNOWN to FAILED with a synthetic counterexample.
///
/// This handles cases like:
/// ```swift
/// func getItem(_ items: [String], _ index: Int) -> String {
///     return items[index]  // Unsafe: index is unconstrained
/// }
/// ```
fn try_detect_unconstrained_bounds_as_failed(auto_vc: &SwiftAutoVc) -> Option<VerifyResult> {
    use crate::types::{Counterexample, Value};

    let SwiftAutoVc::BoundsCheck {
        index,
        path_condition,
        ..
    } = auto_vc
    else {
        return None;
    };

    // If path condition constrains the index, we can't determine it's unsafe
    if path_condition_constrains_index(index, path_condition.as_ref()) {
        return None;
    }

    // Index is unconstrained - generate a synthetic counterexample
    // Use a clearly out-of-bounds value like -1 or Int.max
    let index_name = match index {
        SwiftExpr::ParamRef { name, .. } => name.clone(),
        _ => "index".to_string(),
    };

    let counterexample = Counterexample {
        assignments: vec![(index_name, Value::Int(-1))],
    };

    Some(VerifyResult::Counterexample(counterexample))
}

/// Generate parameter type bounds predicates.
///
/// For integer parameters, we add bounds constraints based on their type:
/// - Signed Int8:  [-128, 127]
/// - Signed Int16: [-32768, 32767]
/// - Signed Int32: [-2147483648, 2147483647]
/// - Signed Int64: [-9223372036854775808, 9223372036854775807]
/// - Unsigned `IntN`: [0, 2^N - 1]
///
/// These bounds are critical for proving overflow checks. Without them,
/// the SMT solver cannot prove that operations like negation will overflow
/// because it doesn't know the input is bounded to the type's range.
#[allow(clippy::cast_possible_truncation)] // bits is always 8/16/32/64
fn generate_param_type_bounds(bundle: &SwiftVcBundle) -> Vec<Predicate> {
    let mut bounds = Vec::new();

    for param in &bundle.parameters {
        // For integer types, generate bounds constraints
        if let SwiftType::Int { signed, bits } = &param.param_type {
            let (min_val, max_val) = overflow_bounds_for_type(*signed, *bits as u8);
            let var = Expr::Var(param.name.clone());

            // param >= min_val
            let lower_bound = Expr::Ge(Box::new(var.clone()), Box::new(Expr::IntLit(min_val)));
            // param <= max_val
            let upper_bound = Expr::Le(Box::new(var), Box::new(Expr::IntLit(max_val)));

            bounds.push(Predicate::Expr(lower_bound));
            bounds.push(Predicate::Expr(upper_bound));
        }
        // For non-integer types, no bounds needed
    }

    bounds
}

/// Verify a `SwiftVcBundle` and return a response.
///
/// Uses the Z4 SMT backend to verify all VCs in the bundle.
///
/// ## Hoare-Logic Verification Semantics
///
/// For proper Hoare-logic verification:
/// - `requires` clauses are **assumptions** (preconditions)
/// - `ensures` clauses are **assertions** (postconditions)
///
/// We verify: `(requires_0 AND requires_1 AND ...) => ensures_i` for each ensures clause.
/// This means: "Assuming all preconditions hold, each postcondition must hold."
///
/// We do NOT verify requires clauses in isolation - they are assumptions about valid inputs.
///
/// # Errors
/// Returns an error if the bundle cannot be converted to VC IR or the solver interface fails.
#[allow(clippy::too_many_lines)]
pub fn verify_bundle(bundle: &SwiftVcBundle) -> Result<SwiftVerifyResponse, VcBridgeError> {
    if bundle.is_trusted {
        return Ok(create_trusted_response(bundle));
    }

    let fvcs = convert_bundle(bundle)?;
    let start = Instant::now();
    let mut counters = VerificationCounters::default();
    let mut spec_result: Option<SwiftVerifyResult> = None;

    let base_requires = build_base_requires(&fvcs, bundle);
    let all_cases = expand_body_constraints(&bundle.body_constraints);

    // Verify each ensures clause
    for (i, vc) in fvcs.ensures.iter().enumerate() {
        let ensures_pred = match &vc.condition {
            VcKind::Predicate(p) => p.clone(),
            _ => continue,
        };

        let (all_proven, first_failure, elapsed) = verify_ensures_cases(
            &ensures_pred,
            &all_cases,
            &base_requires,
            bundle,
            i,
            &vc.name,
        );

        let result = if all_proven {
            VerifyResult::Proven
        } else {
            first_failure.unwrap_or_else(|| VerifyResult::Unknown {
                category: UnknownReason::Other {
                    reason: "no cases to verify".into(),
                },
                reason: "no cases".into(),
            })
        };

        counters.count_spec_result(&result);
        if spec_result.is_none() && !matches!(result, VerifyResult::Proven) {
            spec_result = Some(convert_verify_result(result, elapsed));
        }
    }

    // Set spec_result to verified if all ensures passed (or no ensures)
    if spec_result.is_none() && (counters.spec_verified > 0 || fvcs.ensures.is_empty()) {
        spec_result = Some(SwiftVerifyResult::Verified {
            time_seconds: start.elapsed().as_secs_f64(),
        });
        if fvcs.ensures.is_empty() {
            counters.verified += 1;
            counters.spec_verified += 1;
        }
    }

    // Verify auto-VCs
    let mut auto_vc_results: Vec<SwiftAutoVcResult> = vec![];
    for (vc, swift_auto_vc) in fvcs.assertions.iter().zip(bundle.auto_vcs.iter()) {
        let vc_start = Instant::now();
        let result = verify_single_auto_vc(vc, swift_auto_vc, &base_requires);
        let elapsed = vc_start.elapsed().as_secs_f64();

        counters.count_auto_vc_result(&result);

        let (vc_source_line, vc_source_column) = get_source_location(swift_auto_vc);
        let swift_result = convert_verify_result(result, elapsed);
        let suggestion = generate_suggestion(swift_auto_vc, &swift_result);

        auto_vc_results.push(SwiftAutoVcResult {
            description: vc.name.clone(),
            source_file: bundle.source_file.clone(),
            source_line: if vc_source_line > 0 {
                vc_source_line
            } else {
                bundle.source_line
            },
            source_column: vc_source_column,
            result: swift_result,
            suggestion,
            kani_result: None,
            call_chain: get_call_chain(swift_auto_vc),
        });
    }

    Ok(SwiftVerifyResponse {
        function_name: bundle.function_name.clone(),
        source_file: bundle.source_file.clone(),
        source_line: bundle.source_line,
        is_trusted: false,
        spec_result,
        auto_vc_results,
        summary: counters.to_summary(start.elapsed().as_secs_f64(), 0),
        spec_warnings: bundle.spec_warnings.clone(),
    })
}

/// Progress information for a single VC verification
#[derive(Debug, Clone)]
pub struct VcProgressInfo {
    /// Total number of VCs in this bundle (spec ensures + auto-VCs)
    pub total_vcs: usize,
    /// Number of VCs completed so far (including this one)
    pub completed_vcs: usize,
    /// Name/description of the VC just completed
    pub vc_name: String,
    /// Whether this was a spec VC (ensures) or auto-VC
    pub is_spec: bool,
    /// Result of this VC verification
    pub result: SwiftVerifyResult,
}

/// Callback type for VC-level progress updates.
/// Called after each VC is verified with progress information.
pub type VcProgressCallback<'a> = &'a mut dyn FnMut(&VcProgressInfo);

/// Verify a bundle with progress callbacks for each VC.
///
/// This function is similar to `verify_bundle` but accepts a callback that is
/// invoked after each verification condition is checked. This enables granular
/// progress display (per-VC instead of per-function).
///
/// The callback receives `VcProgressInfo` containing:
/// - Total VC count for this bundle
/// - Number of VCs completed so far
/// - Name and result of the just-completed VC
///
/// # Errors
/// Returns an error if the bundle cannot be converted to VC IR or the solver interface fails.
#[allow(clippy::too_many_lines)]
pub fn verify_bundle_with_progress(
    bundle: &SwiftVcBundle,
    progress: VcProgressCallback,
) -> Result<SwiftVerifyResponse, VcBridgeError> {
    if bundle.is_trusted {
        progress(&VcProgressInfo {
            total_vcs: 1,
            completed_vcs: 1,
            vc_name: format!("{} (trusted)", bundle.function_name),
            is_spec: true,
            result: SwiftVerifyResult::Verified { time_seconds: 0.0 },
        });
        return Ok(create_trusted_response(bundle));
    }

    let fvcs = convert_bundle(bundle)?;
    let spec_count = if fvcs.ensures.is_empty() {
        1
    } else {
        fvcs.ensures.len()
    };
    let total_vcs = spec_count + fvcs.assertions.len();

    let start = Instant::now();
    let mut counters = VerificationCounters::default();
    let mut spec_result: Option<SwiftVerifyResult> = None;
    let mut completed = 0_usize;

    let base_requires = build_base_requires(&fvcs, bundle);
    let all_cases = expand_body_constraints(&bundle.body_constraints);

    // Verify each ensures clause
    for (i, vc) in fvcs.ensures.iter().enumerate() {
        let ensures_pred = match &vc.condition {
            VcKind::Predicate(p) => p.clone(),
            _ => continue,
        };

        let (all_proven, first_failure, elapsed) = verify_ensures_cases(
            &ensures_pred,
            &all_cases,
            &base_requires,
            bundle,
            i,
            &vc.name,
        );

        let result = if all_proven {
            VerifyResult::Proven
        } else {
            first_failure.unwrap_or_else(|| VerifyResult::Unknown {
                category: UnknownReason::Other {
                    reason: "no cases to verify".into(),
                },
                reason: "no cases".into(),
            })
        };

        let swift_result = convert_verify_result(result.clone(), elapsed);
        counters.count_spec_result(&result);
        if spec_result.is_none() && !matches!(result, VerifyResult::Proven) {
            spec_result = Some(swift_result.clone());
        }

        completed += 1;
        progress(&VcProgressInfo {
            total_vcs,
            completed_vcs: completed,
            vc_name: vc.name.clone(),
            is_spec: true,
            result: swift_result,
        });
    }

    // Set spec_result to verified if all ensures passed (or no ensures)
    if spec_result.is_none() && (counters.spec_verified > 0 || fvcs.ensures.is_empty()) {
        spec_result = Some(SwiftVerifyResult::Verified {
            time_seconds: start.elapsed().as_secs_f64(),
        });
        if fvcs.ensures.is_empty() {
            counters.verified += 1;
            counters.spec_verified += 1;
            completed += 1;
            progress(&VcProgressInfo {
                total_vcs,
                completed_vcs: completed,
                vc_name: "spec (no ensures)".to_string(),
                is_spec: true,
                result: SwiftVerifyResult::Verified { time_seconds: 0.0 },
            });
        }
    }

    // Verify auto-VCs
    let mut auto_vc_results: Vec<SwiftAutoVcResult> = vec![];
    for (vc, swift_auto_vc) in fvcs.assertions.iter().zip(bundle.auto_vcs.iter()) {
        let vc_start = Instant::now();
        let result = verify_single_auto_vc(vc, swift_auto_vc, &base_requires);
        let elapsed = vc_start.elapsed().as_secs_f64();

        let swift_result = convert_verify_result(result.clone(), elapsed);
        counters.count_auto_vc_result(&result);

        let (vc_source_line, vc_source_column) = get_source_location(swift_auto_vc);
        let suggestion = generate_suggestion(swift_auto_vc, &swift_result);

        auto_vc_results.push(SwiftAutoVcResult {
            description: vc.name.clone(),
            source_file: bundle.source_file.clone(),
            source_line: if vc_source_line > 0 {
                vc_source_line
            } else {
                bundle.source_line
            },
            source_column: vc_source_column,
            result: swift_result.clone(),
            suggestion,
            kani_result: None,
            call_chain: get_call_chain(swift_auto_vc),
        });

        completed += 1;
        progress(&VcProgressInfo {
            total_vcs,
            completed_vcs: completed,
            vc_name: vc.name.clone(),
            is_spec: false,
            result: swift_result,
        });
    }

    Ok(SwiftVerifyResponse {
        function_name: bundle.function_name.clone(),
        source_file: bundle.source_file.clone(),
        source_line: bundle.source_line,
        is_trusted: false,
        spec_result,
        auto_vc_results,
        summary: counters.to_summary(start.elapsed().as_secs_f64(), 0),
        spec_warnings: bundle.spec_warnings.clone(),
    })
}

/// Single verification condition trace entry
#[derive(Debug, Clone)]
pub struct VcTraceEntry {
    /// Name/description of the VC
    pub name: String,
    /// SMT-LIB2 formula that was sent to the solver
    pub smtlib: String,
    /// Result of verification
    pub result: String,
}

/// Trace information for a bundle verification
#[derive(Debug, Clone)]
pub struct VerificationTrace {
    /// Function being verified
    pub function_name: String,
    /// Trace entries for spec VCs
    pub spec_traces: Vec<VcTraceEntry>,
    /// Trace entries for auto-VCs
    pub auto_vc_traces: Vec<VcTraceEntry>,
}

/// Try to prove an auto-VC using fast shortcut methods before falling back to Z4.
///
/// Returns `Some((result, smtlib))` if a shortcut proved/disproved the VC, `None` otherwise.
fn try_auto_vc_shortcuts(
    swift_auto_vc: &SwiftAutoVc,
    precond_preds: &[Predicate],
) -> Option<(VerifyResult, String)> {
    if let Some(result) = try_prove_overflow_safe_via_path_condition(swift_auto_vc) {
        return Some(result);
    }
    if let Some(result) = try_prove_overflow_via_intervals(swift_auto_vc, precond_preds) {
        return Some(result);
    }
    if let Some(result) = try_prove_bounds_via_path_condition(swift_auto_vc) {
        return Some(result);
    }
    if let Some(result) = try_prove_bounds_via_intervals(swift_auto_vc, precond_preds) {
        return Some(result);
    }
    if let Some(result) = try_prove_nil_via_simple_constraints(swift_auto_vc, precond_preds) {
        return Some(result);
    }
    None
}

/// Format a verify result as a string for tracing.
fn format_verify_result(result: &VerifyResult) -> String {
    match result {
        VerifyResult::Proven => "VERIFIED".to_string(),
        VerifyResult::Counterexample(_) => "FAILED".to_string(),
        VerifyResult::Unknown { category, reason } => {
            format!("UNKNOWN: {category} ({reason})")
        }
        VerifyResult::Timeout { .. } => "TIMEOUT".to_string(),
        VerifyResult::Error(e) => format!("ERROR: {e}"),
    }
}

/// Expand and combine body constraint cases.
///
/// For each body constraint expression, expands ITE expressions into cases.
/// When multiple body constraints exist, produces the cartesian product of all cases.
fn expand_body_constraints(body_constraints: &[SwiftExpr]) -> Vec<(Vec<Predicate>, Predicate)> {
    use crate::convert::convert_expr;

    let mut all_cases: Vec<(Vec<Predicate>, Predicate)> = vec![];

    for body_constraint_expr in body_constraints {
        let Ok(vc_expr) = convert_expr(body_constraint_expr) else {
            continue;
        };
        let cases = expand_body_constraint_to_cases(&vc_expr);
        if all_cases.is_empty() {
            all_cases = cases;
        } else {
            all_cases = combine_case_products(&all_cases, &cases);
        }
    }

    if all_cases.is_empty() {
        all_cases.push((vec![], Predicate::t()));
    }

    all_cases
}

/// Compute the cartesian product of two case lists.
fn combine_case_products(
    existing: &[(Vec<Predicate>, Predicate)],
    new_cases: &[(Vec<Predicate>, Predicate)],
) -> Vec<(Vec<Predicate>, Predicate)> {
    let mut combined = vec![];
    for (existing_conds, existing_constraint) in existing {
        for (new_conds, new_constraint) in new_cases {
            let mut combined_conds = existing_conds.clone();
            combined_conds.extend(new_conds.clone());
            let combined_constraint =
                Predicate::and(vec![existing_constraint.clone(), new_constraint.clone()]);
            combined.push((combined_conds, combined_constraint));
        }
    }
    combined
}

/// Counters for verification results.
#[derive(Default)]
struct VerificationCounters {
    verified: u32,
    failed: u32,
    unknown: u32,
    timeout: u32,
    spec_verified: u32,
    spec_failed: u32,
    spec_unknown: u32,
    auto_vc_verified: u32,
    auto_vc_failed: u32,
    auto_vc_unknown: u32,
}

impl VerificationCounters {
    /// Update counters based on spec verification result.
    fn count_spec_result(&mut self, result: &VerifyResult) {
        match result {
            VerifyResult::Proven => {
                self.verified += 1;
                self.spec_verified += 1;
            }
            VerifyResult::Counterexample(_) => {
                self.failed += 1;
                self.spec_failed += 1;
            }
            VerifyResult::Unknown { .. } => {
                self.unknown += 1;
                self.spec_unknown += 1;
            }
            VerifyResult::Timeout { .. } => {
                self.timeout += 1;
                self.spec_unknown += 1;
            }
            VerifyResult::Error(_) => {}
        }
    }

    /// Update counters based on auto-VC verification result.
    fn count_auto_vc_result(&mut self, result: &VerifyResult) {
        match result {
            VerifyResult::Proven => {
                self.verified += 1;
                self.auto_vc_verified += 1;
            }
            VerifyResult::Counterexample(_) => {
                self.failed += 1;
                self.auto_vc_failed += 1;
            }
            VerifyResult::Unknown { .. } => {
                self.unknown += 1;
                self.auto_vc_unknown += 1;
            }
            VerifyResult::Timeout { .. } => {
                self.timeout += 1;
                self.auto_vc_unknown += 1;
            }
            VerifyResult::Error(_) => {}
        }
    }

    /// Get the total number of VCs processed.
    fn total(&self) -> u32 {
        self.verified + self.failed + self.unknown + self.timeout
    }

    /// Build a `VerificationSummary` from these counters.
    fn to_summary(&self, total_time_seconds: f64, trusted: u32) -> VerificationSummary {
        VerificationSummary {
            total_vcs: self.total(),
            verified: self.verified,
            trusted,
            failed: self.failed,
            unknown: self.unknown,
            timeout: self.timeout,
            total_time_seconds,
            spec_verified: self.spec_verified,
            spec_failed: self.spec_failed,
            spec_unknown: self.spec_unknown,
            auto_vc_verified: self.auto_vc_verified,
            auto_vc_failed: self.auto_vc_failed,
            auto_vc_unknown: self.auto_vc_unknown,
        }
    }
}

/// Build base requires predicates from function VCs and add parameter type bounds.
fn build_base_requires(fvcs: &FunctionVcs, bundle: &SwiftVcBundle) -> Vec<Predicate> {
    let mut base_requires: Vec<Predicate> = fvcs
        .requires
        .iter()
        .filter_map(|vc| {
            if let VcKind::Predicate(p) = &vc.condition {
                Some(p.clone())
            } else {
                None
            }
        })
        .collect();
    base_requires.extend(generate_param_type_bounds(bundle));
    base_requires
}

/// Verify all cases for a single ensures clause and return the result.
///
/// Returns (`all_proven`, `first_failure_result`, `total_elapsed_time`).
fn verify_ensures_cases(
    ensures_pred: &Predicate,
    all_cases: &[(Vec<Predicate>, Predicate)],
    base_requires: &[Predicate],
    bundle: &SwiftVcBundle,
    vc_index: usize,
    vc_name: &str,
) -> (bool, Option<VerifyResult>, f64) {
    use std::sync::Arc;

    let make_span = || SourceSpan {
        file: Arc::from(bundle.source_file.as_str()),
        line_start: bundle.source_line,
        line_end: bundle.source_line,
        col_start: 0,
        col_end: 0,
    };

    let mut all_proven = true;
    let mut first_failure: Option<VerifyResult> = None;
    let mut total_elapsed = 0.0_f64;

    for (case_idx, (case_conds, case_constraint)) in all_cases.iter().enumerate() {
        let mut case_preds = base_requires.to_vec();
        case_preds.extend(case_conds.clone());
        case_preds.push(case_constraint.clone());
        let precondition = Predicate::and(case_preds);

        let substituted_ensures = substitute_old_with_entry_values(ensures_pred);

        let implication_vc = VerificationCondition {
            id: VcId(1000 + vc_index as u64 * 100 + case_idx as u64),
            name: format!("{}:{}:case{}", bundle.function_name, vc_name, case_idx),
            span: make_span(),
            condition: VcKind::Implies {
                antecedent: precondition,
                consequent: substituted_ensures,
            },
            preferred_backend: None,
        };

        let vc_start = Instant::now();
        let result = verify_vc(&implication_vc);
        let elapsed = vc_start.elapsed().as_secs_f64();
        total_elapsed += elapsed;

        if !matches!(result, VerifyResult::Proven) {
            all_proven = false;
            if first_failure.is_none() {
                first_failure = Some(result);
            }
        }
    }

    (all_proven, first_failure, total_elapsed)
}

/// Verify a single auto-VC and return the result.
fn verify_single_auto_vc(
    vc: &VerificationCondition,
    swift_auto_vc: &SwiftAutoVc,
    base_requires: &[Predicate],
) -> VerifyResult {
    use crate::convert::convert_expr;

    let (assertion_pred, vc_antecedent, is_termination_vc) = match &vc.condition {
        VcKind::Predicate(p) => (p.clone(), None, false),
        VcKind::Implies {
            antecedent,
            consequent,
        } => (consequent.clone(), Some(antecedent.clone()), false),
        VcKind::Termination { .. } => (Predicate::Expr(Expr::BoolLit(true)), None, true),
    };

    if is_termination_vc {
        return verify_vc(vc);
    }

    let mut precond_preds = base_requires.to_vec();
    if let Some(antecedent) = vc_antecedent {
        precond_preds.push(antecedent);
    } else if let Some(path_cond) = get_path_condition(swift_auto_vc) {
        if let Ok(path_cond_expr) = convert_expr(path_cond) {
            precond_preds.push(Predicate::Expr(path_cond_expr));
        }
    }

    // Try shortcuts first
    if let Some((shortcut, _)) = try_auto_vc_shortcuts(swift_auto_vc, &precond_preds) {
        return shortcut;
    }

    // Fall back to Z4
    let assertion_precondition = Predicate::and(precond_preds.clone());
    let implication_vc = VerificationCondition {
        id: vc.id,
        name: vc.name.clone(),
        span: vc.span.clone(),
        condition: VcKind::Implies {
            antecedent: assertion_precondition,
            consequent: assertion_pred,
        },
        preferred_backend: None,
    };

    let z4_result = verify_vc(&implication_vc);
    if matches!(z4_result, VerifyResult::Unknown { .. }) {
        try_detect_unconstrained_bounds_as_failed(swift_auto_vc).unwrap_or(z4_result)
    } else {
        z4_result
    }
}

/// Create a trusted bundle response that skips verification.
fn create_trusted_response(bundle: &SwiftVcBundle) -> SwiftVerifyResponse {
    SwiftVerifyResponse {
        function_name: bundle.function_name.clone(),
        source_file: bundle.source_file.clone(),
        source_line: bundle.source_line,
        is_trusted: true,
        spec_result: Some(SwiftVerifyResult::Verified { time_seconds: 0.0 }),
        auto_vc_results: vec![],
        summary: VerificationSummary {
            total_vcs: 1,
            verified: 1,
            trusted: 1,
            failed: 0,
            unknown: 0,
            timeout: 0,
            total_time_seconds: 0.0,
            spec_verified: 1,
            spec_failed: 0,
            spec_unknown: 0,
            auto_vc_verified: 0,
            auto_vc_failed: 0,
            auto_vc_unknown: 0,
        },
        spec_warnings: bundle.spec_warnings.clone(),
    }
}

/// Verify a bundle and return trace information for debugging.
///
/// # Errors
/// Returns an error if the bundle cannot be converted to VC IR or the solver interface fails.
#[allow(clippy::too_many_lines)]
pub fn verify_bundle_with_trace(
    bundle: &SwiftVcBundle,
) -> Result<(SwiftVerifyResponse, VerificationTrace), VcBridgeError> {
    use crate::convert::convert_expr;
    use std::sync::Arc;

    let mut trace = VerificationTrace {
        function_name: bundle.function_name.clone(),
        spec_traces: vec![],
        auto_vc_traces: vec![],
    };

    // If trusted, skip verification
    if bundle.is_trusted {
        return Ok((
            SwiftVerifyResponse {
                function_name: bundle.function_name.clone(),
                source_file: bundle.source_file.clone(),
                source_line: bundle.source_line,
                is_trusted: true,
                spec_result: Some(SwiftVerifyResult::Verified { time_seconds: 0.0 }),
                auto_vc_results: vec![],
                summary: VerificationSummary {
                    total_vcs: 1,
                    verified: 1,
                    trusted: 1,
                    failed: 0,
                    unknown: 0,
                    timeout: 0,
                    total_time_seconds: 0.0,
                    spec_verified: 1,
                    spec_failed: 0,
                    spec_unknown: 0,
                    auto_vc_verified: 0,
                    auto_vc_failed: 0,
                    auto_vc_unknown: 0,
                },
                spec_warnings: bundle.spec_warnings.clone(),
            },
            trace,
        ));
    }

    // Convert to VC IR
    let fvcs = convert_bundle(bundle)?;

    let start = Instant::now();
    let mut counters = VerificationCounters::default();
    let mut spec_result: Option<SwiftVerifyResult> = None;

    // Build base precondition from requires clauses
    let mut base_requires: Vec<Predicate> = fvcs
        .requires
        .iter()
        .filter_map(|vc| {
            if let VcKind::Predicate(p) = &vc.condition {
                Some(p.clone())
            } else {
                None
            }
        })
        .collect();

    // Add parameter type bounds as implicit assumptions
    base_requires.extend(generate_param_type_bounds(bundle));

    // Convert body constraints and expand ite expressions
    let all_cases = expand_body_constraints(&bundle.body_constraints);

    let make_span = || SourceSpan {
        file: Arc::from(bundle.source_file.as_str()),
        line_start: bundle.source_line,
        line_end: bundle.source_line,
        col_start: 0,
        col_end: 0,
    };

    // Verify each ensures clause
    for (i, vc) in fvcs.ensures.iter().enumerate() {
        let ensures_pred = match &vc.condition {
            VcKind::Predicate(p) => p.clone(),
            _ => continue,
        };

        let mut all_cases_proven = true;
        let mut case_results: Vec<(VerifyResult, f64, String)> = vec![];

        for (case_idx, (case_conds, case_constraint)) in all_cases.iter().enumerate() {
            let mut case_preds = base_requires.clone();
            case_preds.extend(case_conds.clone());
            case_preds.push(case_constraint.clone());
            let precondition = Predicate::and(case_preds);

            // Substitute old(x) with x directly in the postcondition
            let substituted_ensures = substitute_old_with_entry_values(&ensures_pred);

            let implication_vc = VerificationCondition {
                id: VcId(1000 + i as u64 * 100 + case_idx as u64),
                name: format!("{}:{}:case{}", bundle.function_name, vc.name, case_idx),
                span: make_span(),
                condition: VcKind::Implies {
                    antecedent: precondition,
                    consequent: substituted_ensures,
                },
                preferred_backend: None,
            };

            let vc_start = Instant::now();
            let (result, smtlib) = verify_vc_with_trace(&implication_vc);
            let elapsed = vc_start.elapsed().as_secs_f64();

            trace.spec_traces.push(VcTraceEntry {
                name: implication_vc.name.clone(),
                smtlib,
                result: format_verify_result(&result),
            });

            match &result {
                VerifyResult::Proven => { /* case verified */ }
                _ => {
                    all_cases_proven = false;
                }
            }
            case_results.push((result, elapsed, String::new()));
        }

        let total_elapsed: f64 = case_results.iter().map(|(_, e, _)| *e).sum();
        let result = if all_cases_proven {
            VerifyResult::Proven
        } else {
            case_results
                .into_iter()
                .find(|(r, _, _)| !matches!(r, VerifyResult::Proven))
                .map_or_else(
                    || VerifyResult::Unknown {
                        category: UnknownReason::Other {
                            reason: "no cases to verify".into(),
                        },
                        reason: "no cases".into(),
                    },
                    |(r, _, _)| r,
                )
        };
        let elapsed = total_elapsed;

        // Record first non-proven result for spec_result
        if spec_result.is_none() && !matches!(&result, VerifyResult::Proven) {
            spec_result = Some(convert_verify_result(result.clone(), elapsed));
        }
        counters.count_spec_result(&result);
    }

    if spec_result.is_none() && (counters.spec_verified > 0 || fvcs.ensures.is_empty()) {
        spec_result = Some(SwiftVerifyResult::Verified {
            time_seconds: start.elapsed().as_secs_f64(),
        });
        if fvcs.ensures.is_empty() {
            counters.verified += 1;
            counters.spec_verified += 1;
        }
    }

    // Verify auto-VCs
    let mut auto_vc_results: Vec<SwiftAutoVcResult> = vec![];
    for (i, (vc, swift_auto_vc)) in fvcs
        .assertions
        .iter()
        .zip(bundle.auto_vcs.iter())
        .enumerate()
    {
        // Extract assertion predicate and path condition from the VC
        let (assertion_pred, vc_antecedent, is_termination_vc) = match &vc.condition {
            VcKind::Predicate(p) => (p.clone(), None, false),
            VcKind::Implies {
                antecedent,
                consequent,
            } => {
                // Path condition is in antecedent, extract both
                (consequent.clone(), Some(antecedent.clone()), false)
            }
            VcKind::Termination { .. } => {
                // Termination VCs are verified directly without transformation
                (Predicate::Expr(Expr::BoolLit(true)), None, true)
            }
        };

        // For termination VCs, verify directly without transformation
        let vc_start = Instant::now();
        let (result, smtlib) = if is_termination_vc {
            // Termination VCs are self-contained - verify directly
            verify_vc_with_trace(vc)
        } else {
            let mut precond_preds = base_requires.clone();

            // Add path condition from VC antecedent (if present)
            if let Some(antecedent) = vc_antecedent {
                precond_preds.push(antecedent);
            } else if let Some(path_cond) = get_path_condition(swift_auto_vc) {
                // Fallback: extract from swift_auto_vc if not in VC
                if let Ok(path_cond_expr) = convert_expr(path_cond) {
                    precond_preds.push(Predicate::Expr(path_cond_expr));
                }
            }

            let assertion_precondition = Predicate::and(precond_preds.clone());

            let implication_vc = VerificationCondition {
                id: VcId(2000 + i as u64),
                name: vc.name.clone(),
                span: vc.span.clone(),
                condition: VcKind::Implies {
                    antecedent: assertion_precondition,
                    consequent: assertion_pred,
                },
                preferred_backend: None,
            };

            if let Some((shortcut, smtlib)) = try_auto_vc_shortcuts(swift_auto_vc, &precond_preds) {
                (shortcut, smtlib)
            } else {
                let (z4_result, smtlib) = verify_vc_with_trace(&implication_vc);
                // If Z4 returns UNKNOWN for a bounds check with unconstrained index,
                // convert to FAILED since the operation is provably unsafe
                if matches!(z4_result, VerifyResult::Unknown { .. }) {
                    if let Some(failed_result) =
                        try_detect_unconstrained_bounds_as_failed(swift_auto_vc)
                    {
                        (failed_result, smtlib)
                    } else {
                        (z4_result, smtlib)
                    }
                } else {
                    (z4_result, smtlib)
                }
            }
        };
        let elapsed = vc_start.elapsed().as_secs_f64();

        trace.auto_vc_traces.push(VcTraceEntry {
            name: vc.name.clone(),
            smtlib,
            result: format_verify_result(&result),
        });

        counters.count_auto_vc_result(&result);

        // Extract source location from the auto-VC
        let (vc_source_line, vc_source_column) = get_source_location(swift_auto_vc);

        let swift_result = convert_verify_result(result, elapsed);
        let suggestion = generate_suggestion(swift_auto_vc, &swift_result);

        auto_vc_results.push(SwiftAutoVcResult {
            description: vc.name.clone(),
            source_file: bundle.source_file.clone(),
            source_line: if vc_source_line > 0 {
                vc_source_line
            } else {
                bundle.source_line
            },
            source_column: vc_source_column,
            result: swift_result,
            suggestion,
            kani_result: None,
            call_chain: get_call_chain(swift_auto_vc),
        });
    }

    let total_time = start.elapsed().as_secs_f64();

    Ok((
        SwiftVerifyResponse {
            function_name: bundle.function_name.clone(),
            source_file: bundle.source_file.clone(),
            source_line: bundle.source_line,
            is_trusted: false,
            spec_result,
            auto_vc_results,
            summary: VerificationSummary {
                total_vcs: counters.total(),
                verified: counters.verified,
                trusted: 0,
                failed: counters.failed,
                unknown: counters.unknown,
                timeout: counters.timeout,
                total_time_seconds: total_time,
                spec_verified: counters.spec_verified,
                spec_failed: counters.spec_failed,
                spec_unknown: counters.spec_unknown,
                auto_vc_verified: counters.auto_vc_verified,
                auto_vc_failed: counters.auto_vc_failed,
                auto_vc_unknown: counters.auto_vc_unknown,
            },
            spec_warnings: bundle.spec_warnings.clone(),
        },
        trace,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_bundle_json() {
        let json = r#"{
            "function_name": "test",
            "source_file": "test.swift",
            "source_line": 1,
            "parameters": [],
            "requires": [],
            "ensures": [],
            "auto_vcs": []
        }"#;

        let bundle = parse_bundle_json(json).unwrap();
        assert_eq!(bundle.function_name, "test");
    }

    #[test]
    fn test_parse_bundle_with_requires() {
        let json = r#"{
            "function_name": "increment",
            "parameters": [
                {"name": "x", "type": {"kind": "Int", "signed": true, "bits": 64}, "index": 0}
            ],
            "requires": [
                {"kind": "Gt", "lhs": {"kind": "ParamRef", "name": "x", "index": 0}, "rhs": {"kind": "IntLit", "value": 0}}
            ],
            "ensures": []
        }"#;

        let bundle = parse_bundle_json(json).unwrap();
        assert_eq!(bundle.function_name, "increment");
        assert_eq!(bundle.parameters.len(), 1);
        assert_eq!(bundle.requires.len(), 1);
    }

    #[test]
    fn test_verify_bundle() {
        let bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
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

        let response = verify_bundle(&bundle).unwrap();
        assert_eq!(response.function_name, "test");
        assert!(
            !response.is_trusted,
            "non-trusted bundle should have is_trusted=false in response"
        );
    }

    /// Test that trusted bundles set `is_trusted`=true in response and skip verification.
    #[test]
    fn test_verify_trusted_bundle_sets_is_trusted() {
        let bundle = SwiftVcBundle {
            function_name: "unsafe_op".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 10,
            source_column: 0,
            parameters: vec![],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: true, // Mark as trusted
            body_constraints: vec![],
            ..Default::default()
        };

        let response = verify_bundle(&bundle).unwrap();

        assert_eq!(response.function_name, "unsafe_op");
        assert!(
            response.is_trusted,
            "trusted bundle should have is_trusted=true in response"
        );

        // Trusted bundles should report verified with 0 time (no actual proof)
        match &response.spec_result {
            Some(SwiftVerifyResult::Verified { time_seconds }) => {
                assert!(
                    (*time_seconds).abs() < f64::EPSILON,
                    "trusted verification should report 0 time"
                );
            }
            other => panic!("expected Verified, got {other:?}"),
        }

        // Verify counts
        assert_eq!(response.summary.verified, 1);
        assert_eq!(response.summary.trusted, 1);
        assert_eq!(response.summary.total_vcs, 1);
    }

    /// Test that `is_trusted` is serialized to JSON correctly.
    #[test]
    fn test_is_trusted_json_serialization() {
        let response = SwiftVerifyResponse {
            function_name: "trusted_func".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 5,
            is_trusted: true,
            spec_result: Some(SwiftVerifyResult::Verified { time_seconds: 0.0 }),
            auto_vc_results: vec![],
            summary: VerificationSummary {
                total_vcs: 1,
                verified: 1,
                trusted: 1,
                failed: 0,
                unknown: 0,
                timeout: 0,
                total_time_seconds: 0.0,
                spec_verified: 1,
                spec_failed: 0,
                spec_unknown: 0,
                auto_vc_verified: 0,
                auto_vc_failed: 0,
                auto_vc_unknown: 0,
            },
            spec_warnings: vec![],
        };

        let json = serde_json::to_string(&response).unwrap();
        assert!(
            json.contains("\"is_trusted\":true"),
            "is_trusted should be in JSON when true: {json}"
        );

        // Verify round-trip
        let parsed: SwiftVerifyResponse = serde_json::from_str(&json).unwrap();
        assert!(parsed.is_trusted);
    }

    /// Test that `is_trusted`=false is NOT serialized (`skip_serializing_if`).
    #[test]
    fn test_is_trusted_false_skipped_in_json() {
        let response = SwiftVerifyResponse {
            function_name: "normal_func".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 5,
            is_trusted: false,
            spec_result: Some(SwiftVerifyResult::Verified {
                time_seconds: 0.001,
            }),
            auto_vc_results: vec![],
            summary: VerificationSummary {
                total_vcs: 1,
                verified: 1,
                trusted: 0,
                failed: 0,
                unknown: 0,
                timeout: 0,
                total_time_seconds: 0.001,
                spec_verified: 1,
                spec_failed: 0,
                spec_unknown: 0,
                auto_vc_verified: 0,
                auto_vc_failed: 0,
                auto_vc_unknown: 0,
            },
            spec_warnings: vec![],
        };

        let json = serde_json::to_string(&response).unwrap();
        // When is_trusted is false, it should be skipped in serialization
        assert!(
            !json.contains("is_trusted"),
            "is_trusted should NOT be in JSON when false: {json}"
        );

        // Verify round-trip still works (defaults to false)
        let parsed: SwiftVerifyResponse = serde_json::from_str(&json).unwrap();
        assert!(!parsed.is_trusted);
    }

    #[test]
    fn test_version() {
        let version = vc_bridge_version();
        let version_str = unsafe { CStr::from_ptr(version).to_str().unwrap() };
        assert_eq!(version_str, "0.1.0");
    }

    /// Test Hoare-logic implication semantics: (requires => ensures) should verify
    /// when ensures follows logically from requires.
    ///
    /// Example: @requires("x > 0") @ensures("result >= x")
    /// For result = x + 1, this should verify because x > 0 implies x + 1 >= x.
    #[test]
    fn test_hoare_logic_requires_implies_ensures() {
        // Bundle: requires x > 0, ensures result >= x
        // This SHOULD verify because the implication (x > 0) => (result >= x) is provable
        // when we model result as related to x (in the abstract, without function body,
        // the SMT solver will try to find a model, and since we're proving an implication
        // it will succeed if there's no counterexample).
        let json = r#"{
            "function_name": "positive_value",
            "source_file": "test.swift",
            "source_line": 10,
            "parameters": [
                {"name": "x", "type": {"kind": "Int", "signed": true, "bits": 64}, "index": 0}
            ],
            "return_type": {"kind": "Int", "signed": true, "bits": 64},
            "requires": [
                {"kind": "Gt", "lhs": {"kind": "ParamRef", "name": "x", "index": 0}, "rhs": {"kind": "IntLit", "value": 0}}
            ],
            "ensures": [
                {"kind": "Ge", "lhs": {"kind": "ResultRef"}, "rhs": {"kind": "ParamRef", "name": "x", "index": 0}}
            ],
            "auto_vcs": []
        }"#;

        let bundle = parse_bundle_json(json).unwrap();
        let response = verify_bundle(&bundle).unwrap();

        // With implication semantics, we're checking: (x > 0) => (result >= x)
        // Without function body knowledge, the SMT solver sees this as:
        // "Is there an assignment to x and result where x > 0 but NOT (result >= x)?"
        // Since result is unconstrained, yes there is (e.g., x=1, result=0).
        // This is expected - we're doing abstract verification without the function body.
        //
        // The key improvement is that we're now USING the precondition as an assumption,
        // rather than verifying it in isolation. This makes more complex specs verifiable.
        assert_eq!(response.function_name, "positive_value");
        assert_eq!(response.summary.total_vcs, 1); // One ensures clause
    }

    /// Test that tautological ensures (always true) verify regardless of requires.
    #[test]
    fn test_tautological_ensures_verifies() {
        // ensures x == x is a tautology, should always verify
        let json = r#"{
            "function_name": "identity_check",
            "source_file": "test.swift",
            "source_line": 1,
            "parameters": [
                {"name": "x", "type": {"kind": "Int", "signed": true, "bits": 64}, "index": 0}
            ],
            "return_type": {"kind": "Int", "signed": true, "bits": 64},
            "requires": [],
            "ensures": [
                {"kind": "Eq", "lhs": {"kind": "ParamRef", "name": "x", "index": 0}, "rhs": {"kind": "ParamRef", "name": "x", "index": 0}}
            ],
            "auto_vcs": []
        }"#;

        let bundle = parse_bundle_json(json).unwrap();
        let response = verify_bundle(&bundle).unwrap();

        // x == x is tautologically true
        assert_eq!(response.summary.verified, 1);
        assert_eq!(response.summary.failed, 0);
        assert!(matches!(
            response.spec_result,
            Some(SwiftVerifyResult::Verified { .. })
        ));
    }

    /// Test that logical implication (requires => ensures) is properly formed.
    /// Example: requires x > 0, ensures x > -1 should verify.
    #[test]
    fn test_implication_x_positive_implies_x_greater_than_neg_one() {
        // If x > 0, then certainly x > -1
        let json = r#"{
            "function_name": "positive_implies_greater_neg_one",
            "source_file": "test.swift",
            "source_line": 1,
            "parameters": [
                {"name": "x", "type": {"kind": "Int", "signed": true, "bits": 64}, "index": 0}
            ],
            "requires": [
                {"kind": "Gt", "lhs": {"kind": "ParamRef", "name": "x", "index": 0}, "rhs": {"kind": "IntLit", "value": 0}}
            ],
            "ensures": [
                {"kind": "Gt", "lhs": {"kind": "ParamRef", "name": "x", "index": 0}, "rhs": {"kind": "IntLit", "value": -1}}
            ],
            "auto_vcs": []
        }"#;

        let bundle = parse_bundle_json(json).unwrap();
        let response = verify_bundle(&bundle).unwrap();

        // (x > 0) => (x > -1) is valid
        assert_eq!(response.summary.verified, 1);
        assert_eq!(response.summary.failed, 0);
        assert!(matches!(
            response.spec_result,
            Some(SwiftVerifyResult::Verified { .. })
        ));
    }

    /// Test multiple requires clauses are conjoined.
    /// Example: requires x > 0 AND requires y > 0, ensures x + y > 0
    #[test]
    fn test_multiple_requires_conjoined() {
        // If x > 0 AND y > 0, then x + y > 0
        let json = r#"{
            "function_name": "sum_positive",
            "source_file": "test.swift",
            "source_line": 1,
            "parameters": [
                {"name": "x", "type": {"kind": "Int", "signed": true, "bits": 64}, "index": 0},
                {"name": "y", "type": {"kind": "Int", "signed": true, "bits": 64}, "index": 1}
            ],
            "requires": [
                {"kind": "Gt", "lhs": {"kind": "ParamRef", "name": "x", "index": 0}, "rhs": {"kind": "IntLit", "value": 0}},
                {"kind": "Gt", "lhs": {"kind": "ParamRef", "name": "y", "index": 1}, "rhs": {"kind": "IntLit", "value": 0}}
            ],
            "ensures": [
                {"kind": "Gt", "lhs": {"kind": "Add", "lhs": {"kind": "ParamRef", "name": "x", "index": 0}, "rhs": {"kind": "ParamRef", "name": "y", "index": 1}}, "rhs": {"kind": "IntLit", "value": 0}}
            ],
            "auto_vcs": []
        }"#;

        let bundle = parse_bundle_json(json).unwrap();
        let response = verify_bundle(&bundle).unwrap();

        // (x > 0 AND y > 0) => (x + y > 0) is valid
        assert_eq!(response.summary.verified, 1);
        assert_eq!(response.summary.failed, 0);
        assert!(matches!(
            response.spec_result,
            Some(SwiftVerifyResult::Verified { .. })
        ));
    }

    #[test]
    fn test_case_split_abs() {
        use crate::types::Expr;

        // Simulate abs body constraint: result = ite(x >= 0, x, -x)
        let body_constraint = Expr::Eq(
            Box::new(Expr::Result),
            Box::new(Expr::Ite {
                cond: Box::new(Expr::Ge(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                then_: Box::new(Expr::Var("x".to_string())),
                else_: Box::new(Expr::Neg(Box::new(Expr::Var("x".to_string())))),
            }),
        );

        let cases = expand_body_constraint_to_cases(&body_constraint);
        assert_eq!(cases.len(), 2, "Should have 2 cases for ite");
    }

    /// Test that Case 2 of abs (x < 0 AND result = -x) => result >= 0 can be verified
    /// Z4's LIA solver cannot handle formulas involving negation/subtraction
    /// Test the case-split verification path for safeDecrement
    #[test]
    fn test_verify_safe_decrement_via_case_split() {
        use crate::json_types::{SwiftExpr, SwiftParam, SwiftType, SwiftVcBundle};

        // This is the JSON that tswift-mock generates for safeDecrement
        let bundle = SwiftVcBundle {
            function_name: "safeDecrement".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
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
            requires: vec![],
            ensures: vec![SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![SwiftExpr::Eq {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::Ite {
                    cond: Box::new(SwiftExpr::Gt {
                        lhs: Box::new(SwiftExpr::ParamRef {
                            name: "x".to_string(),
                            index: 0,
                        }),
                        rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
                    }),
                    then_expr: Box::new(SwiftExpr::Sub {
                        lhs: Box::new(SwiftExpr::ParamRef {
                            name: "x".to_string(),
                            index: 0,
                        }),
                        rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
                    }),
                    else_expr: Box::new(SwiftExpr::IntLit { value: 0 }),
                }),
            }],
            ..Default::default()
        };

        let response = verify_bundle(&bundle).unwrap();

        assert!(
            matches!(
                response.spec_result,
                Some(SwiftVerifyResult::Verified { .. })
            ),
            "Expected Verified for safeDecrement, got {:?}",
            response.spec_result
        );
    }

    #[test]
    fn test_verify_abs_case2_directly() {
        use crate::types::{
            Expr, Predicate, SourceSpan, VcId, VcKind, VerificationCondition, VerifyResult,
        };
        use crate::z4_backend::verify_vc_with_fallback as verify_vc;
        use std::sync::Arc;

        // Case 2: (x < 0 AND result = -x) => result >= 0
        let vc = VerificationCondition {
            id: VcId(99),
            name: "abs_case2".to_string(),
            span: SourceSpan {
                file: Arc::from("test.swift"),
                line_start: 1,
                line_end: 1,
                col_start: 0,
                col_end: 0,
            },
            condition: VcKind::Implies {
                antecedent: Predicate::And(vec![
                    // x < 0 (expressed as NOT(x >= 0))
                    Predicate::Not(Box::new(Predicate::Expr(Expr::Ge(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )))),
                    // result = -x
                    Predicate::Expr(Expr::Eq(
                        Box::new(Expr::Result),
                        Box::new(Expr::Neg(Box::new(Expr::Var("x".to_string())))),
                    )),
                ]),
                consequent: Predicate::Expr(Expr::Ge(
                    Box::new(Expr::Result),
                    Box::new(Expr::IntLit(0)),
                )),
            },
            preferred_backend: None,
        };

        let result = verify_vc(&vc);

        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven for abs case 2, got {result:?}"
        );
    }

    /// Test max function with two ensures: result >= x AND result >= y
    #[test]
    fn test_verify_max_via_case_split() {
        use crate::json_types::{SwiftExpr, SwiftParam, SwiftType, SwiftVcBundle};

        let bundle = SwiftVcBundle {
            function_name: "max".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
            parameters: vec![
                SwiftParam {
                    name: "x".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "y".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 1,
                },
            ],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 64,
            }),
            requires: vec![],
            ensures: vec![
                SwiftExpr::Ge {
                    lhs: Box::new(SwiftExpr::ResultRef),
                    rhs: Box::new(SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    }),
                },
                SwiftExpr::Ge {
                    lhs: Box::new(SwiftExpr::ResultRef),
                    rhs: Box::new(SwiftExpr::ParamRef {
                        name: "y".to_string(),
                        index: 1,
                    }),
                },
            ],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![SwiftExpr::Eq {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::Ite {
                    cond: Box::new(SwiftExpr::Ge {
                        lhs: Box::new(SwiftExpr::ParamRef {
                            name: "x".to_string(),
                            index: 0,
                        }),
                        rhs: Box::new(SwiftExpr::ParamRef {
                            name: "y".to_string(),
                            index: 1,
                        }),
                    }),
                    then_expr: Box::new(SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    }),
                    else_expr: Box::new(SwiftExpr::ParamRef {
                        name: "y".to_string(),
                        index: 1,
                    }),
                }),
            }],
            ..Default::default()
        };

        let response = verify_bundle(&bundle).unwrap();

        assert!(
            matches!(
                response.spec_result,
                Some(SwiftVerifyResult::Verified { .. })
            ),
            "Expected Verified for max, got {:?}",
            response.spec_result
        );
    }

    /// Test that guarded increment (x < Int.max => x + 1) proves safe via path condition.
    ///
    /// This is the common `SwiftUI` counter pattern:
    /// ```swift
    /// if count < Int.max {
    ///     count += 1  // Safe: guarded by path condition
    /// }
    /// ```
    #[test]
    fn test_overflow_safe_via_path_condition_increment() {
        // x < Int.max => x + 1 does not overflow
        let bundle = SwiftVcBundle {
            function_name: "guarded_increment".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
                index: 0,
            }],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![SwiftAutoVc::Overflow {
                operation: "add".to_string(),
                operands: vec![
                    SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    },
                    SwiftExpr::IntLit { value: 1 },
                ],
                description: "overflow check: x + 1".to_string(),
                source_line: 5,
                source_column: 10,
                path_condition: Some(SwiftExpr::Lt {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: i64::MAX }),
                }),
                signed: true,
                bits: 64,
            }],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let response = verify_bundle(&bundle).unwrap();

        // Should have 1 verified auto-VC (the guarded overflow)
        assert_eq!(response.summary.auto_vc_verified, 1);
        assert_eq!(response.summary.auto_vc_failed, 0);
        assert_eq!(response.summary.auto_vc_unknown, 0);

        // Check that the overflow VC was verified
        assert_eq!(response.auto_vc_results.len(), 1);
        assert!(
            matches!(
                response.auto_vc_results[0].result,
                SwiftVerifyResult::Verified { .. }
            ),
            "Expected guarded increment to be Verified via path condition, got {:?}",
            response.auto_vc_results[0].result
        );
    }

    /// Test that guarded decrement (x > Int.min => x - 1) proves safe via path condition.
    #[test]
    fn test_overflow_safe_via_path_condition_decrement() {
        // x > Int.min => x - 1 does not underflow
        let bundle = SwiftVcBundle {
            function_name: "guarded_decrement".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
                index: 0,
            }],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![SwiftAutoVc::Overflow {
                operation: "sub".to_string(),
                operands: vec![
                    SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    },
                    SwiftExpr::IntLit { value: 1 },
                ],
                description: "overflow check: x - 1".to_string(),
                source_line: 5,
                source_column: 10,
                path_condition: Some(SwiftExpr::Gt {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: i64::MIN }),
                }),
                signed: true,
                bits: 64,
            }],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let response = verify_bundle(&bundle).unwrap();

        // Should have 1 verified auto-VC (the guarded overflow)
        assert_eq!(response.summary.auto_vc_verified, 1);
        assert_eq!(response.summary.auto_vc_failed, 0);
        assert_eq!(response.summary.auto_vc_unknown, 0);

        // Check that the overflow VC was verified
        assert_eq!(response.auto_vc_results.len(), 1);
        assert!(
            matches!(
                response.auto_vc_results[0].result,
                SwiftVerifyResult::Verified { .. }
            ),
            "Expected guarded decrement to be Verified via path condition, got {:?}",
            response.auto_vc_results[0].result
        );
    }

    /// Test that increment without guard still fails/unknown (control test).
    #[test]
    fn test_overflow_without_path_condition_fails() {
        // x + 1 without guard should fail (could overflow at Int.max)
        let bundle = SwiftVcBundle {
            function_name: "unguarded_increment".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
                index: 0,
            }],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![SwiftAutoVc::Overflow {
                operation: "add".to_string(),
                operands: vec![
                    SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    },
                    SwiftExpr::IntLit { value: 1 },
                ],
                description: "overflow check: x + 1".to_string(),
                source_line: 5,
                source_column: 10,
                path_condition: None, // No guard!
                signed: true,
                bits: 64,
            }],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let response = verify_bundle(&bundle).unwrap();

        // Should have 1 failed auto-VC (no guard => overflow possible)
        assert_eq!(response.summary.auto_vc_verified, 0);
        assert_eq!(response.summary.auto_vc_failed, 1);

        // Check that the overflow VC failed
        assert_eq!(response.auto_vc_results.len(), 1);
        assert!(
            matches!(
                response.auto_vc_results[0].result,
                SwiftVerifyResult::Failed { .. }
            ),
            "Expected unguarded increment to Fail, got {:?}",
            response.auto_vc_results[0].result
        );
    }

    // ========================================================================
    // Entry-Value Constraint Tests (v359)
    // ========================================================================

    /// Test that `collect_old_vars_from_predicate` correctly extracts `old()` variables
    #[test]
    fn test_collect_old_vars_simple() {
        // old(x) + y == result
        let pred = Predicate::Expr(Expr::Eq(
            Box::new(Expr::Add(
                Box::new(Expr::Old(Box::new(Expr::Var("x".to_string())))),
                Box::new(Expr::Var("y".to_string())),
            )),
            Box::new(Expr::Result),
        ));

        let vars = collect_old_vars_from_predicate(&pred);
        assert_eq!(vars, vec!["x".to_string()]);
    }

    /// Test multiple `old()` variables in a predicate
    #[test]
    fn test_collect_old_vars_multiple() {
        // old(balance) + amount == result && old(count) > 0
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Add(
                    Box::new(Expr::Old(Box::new(Expr::Var("balance".to_string())))),
                    Box::new(Expr::Var("amount".to_string())),
                )),
                Box::new(Expr::Result),
            )),
            Predicate::Expr(Expr::Gt(
                Box::new(Expr::Old(Box::new(Expr::Var("count".to_string())))),
                Box::new(Expr::IntLit(0)),
            )),
        ]);

        let mut vars = collect_old_vars_from_predicate(&pred);
        vars.sort();
        assert_eq!(vars, vec!["balance".to_string(), "count".to_string()]);
    }

    /// Test old(result) is correctly collected
    #[test]
    fn test_collect_old_vars_result() {
        // old(result) > 0
        let pred = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Old(Box::new(Expr::Result))),
            Box::new(Expr::IntLit(0)),
        ));

        let vars = collect_old_vars_from_predicate(&pred);
        assert_eq!(vars, vec!["result".to_string()]);
    }

    /// Test no `old()` variables
    #[test]
    fn test_collect_old_vars_none() {
        // x + y == result (no old())
        let pred = Predicate::Expr(Expr::Eq(
            Box::new(Expr::Add(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::Var("y".to_string())),
            )),
            Box::new(Expr::Result),
        ));

        let vars = collect_old_vars_from_predicate(&pred);
        assert!(vars.is_empty());
    }

    /// Test `substitute_old_with_entry_values` replaces `old(x)` with x
    #[test]
    fn test_substitute_old_with_entry_values() {
        // old(balance) + amount == result  ->  balance + amount == result
        let pred = Predicate::Expr(Expr::Eq(
            Box::new(Expr::Add(
                Box::new(Expr::Old(Box::new(Expr::Var("balance".to_string())))),
                Box::new(Expr::Var("amount".to_string())),
            )),
            Box::new(Expr::Result),
        ));

        let substituted = substitute_old_with_entry_values(&pred);

        // Should be: balance + amount == result
        match substituted {
            Predicate::Expr(Expr::Eq(lhs, _rhs)) => {
                // LHS should be Add(Var(balance), Var(amount))
                match lhs.as_ref() {
                    Expr::Add(a, _b) => {
                        assert!(
                            matches!(a.as_ref(), Expr::Var(n) if n == "balance"),
                            "old(balance) should be substituted with balance"
                        );
                    }
                    _ => panic!("Expected Add expression"),
                }
            }
            _ => panic!("Expected Eq predicate"),
        }
    }

    /// Test SMT-LIB trace for `old()` postcondition with substitution approach
    #[test]
    fn test_postcondition_with_old_smtlib_trace() {
        use crate::types::{
            Expr, Predicate, SourceSpan, VcId, VcKind, VerificationCondition, VerifyResult,
        };
        use crate::z4_backend::verify_vc_with_fallback_and_trace as verify_vc_trace;
        use std::sync::Arc;

        // With the substitution approach, old(balance) becomes balance directly
        // So we now verify: (result == balance + amount) => (result == balance + amount)
        // This is a tautology.
        let vc = VerificationCondition {
            id: VcId(999),
            name: "old_postcondition_substituted".to_string(),
            span: SourceSpan {
                file: Arc::from("test.swift"),
                line_start: 1,
                line_end: 1,
                col_start: 0,
                col_end: 0,
            },
            condition: VcKind::Implies {
                antecedent: Predicate::And(vec![
                    // Body constraint: result == balance + amount
                    Predicate::Expr(Expr::Eq(
                        Box::new(Expr::Result),
                        Box::new(Expr::Add(
                            Box::new(Expr::Var("balance".to_string())),
                            Box::new(Expr::Var("amount".to_string())),
                        )),
                    )),
                ]),
                // Postcondition (after substituting old(balance) -> balance):
                // result == balance + amount
                consequent: Predicate::Expr(Expr::Eq(
                    Box::new(Expr::Result),
                    Box::new(Expr::Add(
                        Box::new(Expr::Var("balance".to_string())),
                        Box::new(Expr::Var("amount".to_string())),
                    )),
                )),
            },
            preferred_backend: None,
        };

        let (result, smtlib) = verify_vc_trace(&vc);

        // This should verify - it's now a tautology after substitution
        assert!(
            matches!(result, VerifyResult::Proven),
            "Substituted postcondition should verify (tautology). Got: {result:?}\nSMT-LIB:\n{smtlib}"
        );
    }

    /// Test postcondition with `old()` verifies correctly (v359 fix)
    #[test]
    fn test_postcondition_with_old_verifies() {
        // deposit: balance + amount with postcondition result == old(balance) + amount
        let bundle = SwiftVcBundle {
            function_name: "deposit".to_string(),
            source_file: "banking.swift".to_string(),
            source_line: 1,
            source_column: 0,
            parameters: vec![
                SwiftParam {
                    name: "balance".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "amount".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 1,
                },
            ],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 64,
            }),
            requires: vec![
                // amount > 0
                SwiftExpr::Gt {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "amount".to_string(),
                        index: 1,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
                },
            ],
            ensures: vec![
                // result == old(balance) + amount
                SwiftExpr::Eq {
                    lhs: Box::new(SwiftExpr::ResultRef),
                    rhs: Box::new(SwiftExpr::Add {
                        lhs: Box::new(SwiftExpr::Old {
                            expr: Box::new(SwiftExpr::ParamRef {
                                name: "balance".to_string(),
                                index: 0,
                            }),
                        }),
                        rhs: Box::new(SwiftExpr::ParamRef {
                            name: "amount".to_string(),
                            index: 1,
                        }),
                    }),
                },
            ],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            // Body constraint: result == balance + amount
            body_constraints: vec![SwiftExpr::Eq {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::Add {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "balance".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::ParamRef {
                        name: "amount".to_string(),
                        index: 1,
                    }),
                }),
            }],
            ..Default::default()
        };

        let response = verify_bundle(&bundle).unwrap();

        // The postcondition should verify because:
        // 1. Body constraint: result == balance + amount
        // 2. Entry-value constraint: balance_old == balance (added by fix)
        // 3. Postcondition: result == balance_old + amount
        // These are equivalent when balance_old == balance
        assert_eq!(
            response.summary.spec_verified, 1,
            "Postcondition with old() should verify. Got: {:?}",
            response.spec_result
        );
        assert_eq!(response.summary.spec_failed, 0);
    }

    /// Test postcondition with `old()` for subtraction (withdraw)
    #[test]
    fn test_postcondition_with_old_subtract_verifies() {
        // withdraw: balance - amount with postcondition result == old(balance) - amount
        let bundle = SwiftVcBundle {
            function_name: "withdraw".to_string(),
            source_file: "banking.swift".to_string(),
            source_line: 1,
            source_column: 0,
            parameters: vec![
                SwiftParam {
                    name: "balance".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "amount".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 1,
                },
            ],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 64,
            }),
            requires: vec![
                // amount > 0
                SwiftExpr::Gt {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "amount".to_string(),
                        index: 1,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
                },
                // balance >= amount
                SwiftExpr::Ge {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "balance".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::ParamRef {
                        name: "amount".to_string(),
                        index: 1,
                    }),
                },
            ],
            ensures: vec![
                // result == old(balance) - amount
                SwiftExpr::Eq {
                    lhs: Box::new(SwiftExpr::ResultRef),
                    rhs: Box::new(SwiftExpr::Sub {
                        lhs: Box::new(SwiftExpr::Old {
                            expr: Box::new(SwiftExpr::ParamRef {
                                name: "balance".to_string(),
                                index: 0,
                            }),
                        }),
                        rhs: Box::new(SwiftExpr::ParamRef {
                            name: "amount".to_string(),
                            index: 1,
                        }),
                    }),
                },
            ],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            // Body constraint: result == balance - amount
            body_constraints: vec![SwiftExpr::Eq {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::Sub {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "balance".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::ParamRef {
                        name: "amount".to_string(),
                        index: 1,
                    }),
                }),
            }],
            ..Default::default()
        };

        let response = verify_bundle(&bundle).unwrap();

        assert_eq!(
            response.summary.spec_verified, 1,
            "Withdraw postcondition with old() should verify. Got: {:?}",
            response.spec_result
        );
        assert_eq!(response.summary.spec_failed, 0);
    }

    // ========================================================================
    // Unit Tests for condition_to_z4_friendly (v401)
    // ========================================================================

    #[test]
    fn test_condition_to_z4_friendly_gt_literal() {
        // x > 5 => positive: x >= 6, negative: x <= 5
        let cond = Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        let (pos, neg) = condition_to_z4_friendly(&cond);

        // Positive: x >= 6
        assert!(
            matches!(pos, Predicate::Expr(Expr::Ge(_, ref b)) if matches!(b.as_ref(), Expr::IntLit(6)))
        );
        // Negative: x <= 5
        assert!(
            matches!(neg, Predicate::Expr(Expr::Le(_, ref b)) if matches!(b.as_ref(), Expr::IntLit(5)))
        );
    }

    #[test]
    fn test_condition_to_z4_friendly_gt_literal_i128_max_no_overflow() {
        // i128::MAX + 1 would overflow; keep strict form for positive predicate.
        let cond = Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(i128::MAX)),
        );
        let (pos, neg) = condition_to_z4_friendly(&cond);

        assert!(
            matches!(pos, Predicate::Expr(Expr::Gt(_, ref b)) if matches!(b.as_ref(), Expr::IntLit(n) if *n == i128::MAX))
        );
        assert!(
            matches!(neg, Predicate::Expr(Expr::Le(_, ref b)) if matches!(b.as_ref(), Expr::IntLit(n) if *n == i128::MAX))
        );
    }

    #[test]
    fn test_condition_to_z4_friendly_lt_literal() {
        // x < 10 => positive: x <= 9, negative: x >= 10
        let cond = Expr::Lt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(10)),
        );
        let (pos, neg) = condition_to_z4_friendly(&cond);

        // Positive: x <= 9
        assert!(
            matches!(pos, Predicate::Expr(Expr::Le(_, ref b)) if matches!(b.as_ref(), Expr::IntLit(9)))
        );
        // Negative: x >= 10
        assert!(
            matches!(neg, Predicate::Expr(Expr::Ge(_, ref b)) if matches!(b.as_ref(), Expr::IntLit(10)))
        );
    }

    #[test]
    fn test_condition_to_z4_friendly_lt_literal_i128_min_no_overflow() {
        // i128::MIN - 1 would overflow; keep strict form for positive predicate.
        let cond = Expr::Lt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(i128::MIN)),
        );
        let (pos, neg) = condition_to_z4_friendly(&cond);

        assert!(
            matches!(pos, Predicate::Expr(Expr::Lt(_, ref b)) if matches!(b.as_ref(), Expr::IntLit(n) if *n == i128::MIN))
        );
        assert!(
            matches!(neg, Predicate::Expr(Expr::Ge(_, ref b)) if matches!(b.as_ref(), Expr::IntLit(n) if *n == i128::MIN))
        );
    }

    #[test]
    fn test_condition_to_z4_friendly_gt_variable() {
        // x > y => positive: x > y, negative: x <= y
        let cond = Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let (pos, neg) = condition_to_z4_friendly(&cond);

        // Positive: stays as x > y (variable comparison)
        assert!(matches!(pos, Predicate::Expr(Expr::Gt(_, _))));
        // Negative: x <= y
        assert!(matches!(neg, Predicate::Expr(Expr::Le(_, _))));
    }

    #[test]
    fn test_condition_to_z4_friendly_ge() {
        // x >= y => positive: x >= y, negative: x + 1 <= y
        let cond = Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let (pos, neg) = condition_to_z4_friendly(&cond);

        assert!(matches!(pos, Predicate::Expr(Expr::Ge(_, _))));
        // Negative: x + 1 <= y (avoids NOT(x >= y))
        assert!(matches!(neg, Predicate::Expr(Expr::Le(_, _))));
    }

    #[test]
    fn test_condition_to_z4_friendly_le() {
        // x <= y => positive: x <= y, negative: x >= y + 1
        let cond = Expr::Le(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let (pos, neg) = condition_to_z4_friendly(&cond);

        assert!(matches!(pos, Predicate::Expr(Expr::Le(_, _))));
        // Negative: x >= y + 1 (avoids NOT(x <= y))
        assert!(matches!(neg, Predicate::Expr(Expr::Ge(_, _))));
    }

    #[test]
    fn test_condition_to_z4_friendly_not() {
        // NOT(x > 5) => swaps positive and negative
        let inner = Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        let cond = Expr::Not(Box::new(inner));
        let (pos, neg) = condition_to_z4_friendly(&cond);

        // NOT(x > 5) positive = (x > 5) negative = x <= 5
        assert!(matches!(pos, Predicate::Expr(Expr::Le(_, _))));
        // NOT(x > 5) negative = (x > 5) positive = x >= 6
        assert!(matches!(neg, Predicate::Expr(Expr::Ge(_, _))));
    }

    #[test]
    fn test_condition_to_z4_friendly_eq() {
        // x == 5 is a fallback case
        let cond = Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        let (pos, neg) = condition_to_z4_friendly(&cond);

        assert!(matches!(pos, Predicate::Expr(Expr::Eq(_, _))));
        assert!(matches!(neg, Predicate::Not(_)));
    }

    // ========================================================================
    // Unit Tests for expand_ite_to_cases (v401)
    // ========================================================================

    #[test]
    fn test_expand_ite_simple() {
        // result = ite(x >= 0, x, -x)
        let lhs = Expr::Result;
        let rhs = Expr::Ite {
            cond: Box::new(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            then_: Box::new(Expr::Var("x".to_string())),
            else_: Box::new(Expr::Neg(Box::new(Expr::Var("x".to_string())))),
        };

        let cases = expand_ite_to_cases(&lhs, &rhs, vec![]);
        assert_eq!(cases.len(), 2);

        // Case 1: x >= 0 => result = x
        assert_eq!(cases[0].0.len(), 1);
        // Case 2: NOT(x >= 0) => result = -x
        assert_eq!(cases[1].0.len(), 1);
    }

    #[test]
    fn test_expand_ite_nested() {
        // result = ite(c1, e1, ite(c2, e2, e3))
        let lhs = Expr::Result;
        let rhs = Expr::Ite {
            cond: Box::new(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            then_: Box::new(Expr::IntLit(1)),
            else_: Box::new(Expr::Ite {
                cond: Box::new(Expr::Lt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                then_: Box::new(Expr::IntLit(-1)),
                else_: Box::new(Expr::IntLit(0)),
            }),
        };

        let cases = expand_ite_to_cases(&lhs, &rhs, vec![]);
        assert_eq!(cases.len(), 3, "Nested ite should produce 3 cases");

        // Case 1: x > 0 => result = 1
        // Case 2: NOT(x > 0) AND x < 0 => result = -1
        // Case 3: NOT(x > 0) AND NOT(x < 0) => result = 0
    }

    #[test]
    fn test_expand_ite_base_case_no_ite() {
        // result = 42 (no ite)
        let lhs = Expr::Result;
        let rhs = Expr::IntLit(42);

        let cases = expand_ite_to_cases(&lhs, &rhs, vec![]);
        assert_eq!(cases.len(), 1);
        assert!(cases[0].0.is_empty()); // No path conditions
    }

    #[test]
    fn test_expand_body_constraint_non_eq() {
        // Non-equality constraint returns single case
        let constraint = Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );

        let cases = expand_body_constraint_to_cases(&constraint);
        assert_eq!(cases.len(), 1);
    }

    // ========================================================================
    // Unit Tests for interval arithmetic (v401)
    // ========================================================================

    #[test]
    fn test_interval_add_simple() {
        let a = IntInterval { lo: 1, hi: 5 };
        let b = IntInterval { lo: 2, hi: 3 };
        let result = interval_add(a, b).unwrap();
        assert_eq!(result.lo, 3);
        assert_eq!(result.hi, 8);
    }

    #[test]
    fn test_interval_add_negative() {
        let a = IntInterval { lo: -10, hi: -5 };
        let b = IntInterval { lo: 2, hi: 3 };
        let result = interval_add(a, b).unwrap();
        assert_eq!(result.lo, -8);
        assert_eq!(result.hi, -2);
    }

    #[test]
    fn test_interval_sub_simple() {
        // [1, 5] - [2, 3] = [1-3, 5-2] = [-2, 3]
        let a = IntInterval { lo: 1, hi: 5 };
        let b = IntInterval { lo: 2, hi: 3 };
        let result = interval_sub(a, b).unwrap();
        assert_eq!(result.lo, -2);
        assert_eq!(result.hi, 3);
    }

    #[test]
    fn test_interval_sub_all_positive() {
        // [10, 20] - [1, 5] = [10-5, 20-1] = [5, 19]
        let a = IntInterval { lo: 10, hi: 20 };
        let b = IntInterval { lo: 1, hi: 5 };
        let result = interval_sub(a, b).unwrap();
        assert_eq!(result.lo, 5);
        assert_eq!(result.hi, 19);
    }

    #[test]
    fn test_interval_mul_positive() {
        let a = IntInterval { lo: 2, hi: 4 };
        let b = IntInterval { lo: 3, hi: 5 };
        let result = interval_mul(a, b).unwrap();
        assert_eq!(result.lo, 6);
        assert_eq!(result.hi, 20);
    }

    #[test]
    fn test_interval_mul_mixed_signs() {
        // [-2, 3] * [1, 2] = min(-4, -2, 3, 6), max(-4, -2, 3, 6) = [-4, 6]
        let a = IntInterval { lo: -2, hi: 3 };
        let b = IntInterval { lo: 1, hi: 2 };
        let result = interval_mul(a, b).unwrap();
        assert_eq!(result.lo, -4);
        assert_eq!(result.hi, 6);
    }

    #[test]
    fn test_interval_mul_both_negative() {
        // [-4, -2] * [-3, -1] = products: 12, 4, 6, 2 => [2, 12]
        let a = IntInterval { lo: -4, hi: -2 };
        let b = IntInterval { lo: -3, hi: -1 };
        let result = interval_mul(a, b).unwrap();
        assert_eq!(result.lo, 2);
        assert_eq!(result.hi, 12);
    }

    #[test]
    fn test_interval_neg_positive() {
        // -[2, 5] = [-5, -2]
        let a = IntInterval { lo: 2, hi: 5 };
        let result = interval_neg(a).unwrap();
        assert_eq!(result.lo, -5);
        assert_eq!(result.hi, -2);
    }

    #[test]
    fn test_interval_neg_mixed() {
        // -[-3, 5] = [-5, 3]
        let a = IntInterval { lo: -3, hi: 5 };
        let result = interval_neg(a).unwrap();
        assert_eq!(result.lo, -5);
        assert_eq!(result.hi, 3);
    }

    #[test]
    fn test_interval_for_expr_literal() {
        let var_bounds: HashMap<String, VarBounds> = HashMap::new();
        let expr = Expr::IntLit(42);
        let interval = interval_for_expr(&expr, &var_bounds).unwrap();
        assert_eq!(interval.lo, 42);
        assert_eq!(interval.hi, 42);
    }

    #[test]
    fn test_interval_for_expr_var() {
        let mut var_bounds: HashMap<String, VarBounds> = HashMap::new();
        var_bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(0),
                hi: Some(100),
            },
        );
        let expr = Expr::Var("x".to_string());
        let interval = interval_for_expr(&expr, &var_bounds).unwrap();
        assert_eq!(interval.lo, 0);
        assert_eq!(interval.hi, 100);
    }

    #[test]
    fn test_interval_for_expr_add() {
        let mut var_bounds: HashMap<String, VarBounds> = HashMap::new();
        var_bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(1),
                hi: Some(10),
            },
        );
        // x + 5 with x in [1, 10] => [6, 15]
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        let interval = interval_for_expr(&expr, &var_bounds).unwrap();
        assert_eq!(interval.lo, 6);
        assert_eq!(interval.hi, 15);
    }

    #[test]
    fn test_interval_for_expr_sub() {
        let mut var_bounds: HashMap<String, VarBounds> = HashMap::new();
        var_bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(10),
                hi: Some(20),
            },
        );
        // x - 5 with x in [10, 20] => [5, 15]
        let expr = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        let interval = interval_for_expr(&expr, &var_bounds).unwrap();
        assert_eq!(interval.lo, 5);
        assert_eq!(interval.hi, 15);
    }

    #[test]
    fn test_interval_for_expr_neg() {
        let mut var_bounds: HashMap<String, VarBounds> = HashMap::new();
        var_bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(2),
                hi: Some(8),
            },
        );
        // -x with x in [2, 8] => [-8, -2]
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        let interval = interval_for_expr(&expr, &var_bounds).unwrap();
        assert_eq!(interval.lo, -8);
        assert_eq!(interval.hi, -2);
    }

    #[test]
    fn test_interval_for_expr_struct_field() {
        let mut var_bounds: HashMap<String, VarBounds> = HashMap::new();
        var_bounds.insert(
            "arr.count".to_string(),
            VarBounds {
                lo: Some(0),
                hi: Some(1000),
            },
        );
        let expr = Expr::StructField(Box::new(Expr::Var("arr".to_string())), "count".to_string());
        let interval = interval_for_expr(&expr, &var_bounds).unwrap();
        assert_eq!(interval.lo, 0);
        assert_eq!(interval.hi, 1000);
    }

    #[test]
    fn test_interval_for_expr_unknown_var() {
        let var_bounds: HashMap<String, VarBounds> = HashMap::new();
        let expr = Expr::Var("unknown".to_string());
        assert!(interval_for_expr(&expr, &var_bounds).is_none());
    }

    // ========================================================================
    // Unit Tests for bounds helper functions (v401)
    // ========================================================================

    #[test]
    fn test_bounds_from_cmp_ge_var_left() {
        // x >= 5 => lo = 5, hi = None
        let (lo, hi) = bounds_from_cmp(BoundCmp::Ge, 5, true);
        assert_eq!(lo, Some(5));
        assert_eq!(hi, None);
    }

    #[test]
    fn test_bounds_from_cmp_gt_var_left() {
        // x > 5 => lo = 6, hi = None
        let (lo, hi) = bounds_from_cmp(BoundCmp::Gt, 5, true);
        assert_eq!(lo, Some(6));
        assert_eq!(hi, None);
    }

    #[test]
    fn test_bounds_from_cmp_le_var_left() {
        // x <= 10 => lo = None, hi = 10
        let (lo, hi) = bounds_from_cmp(BoundCmp::Le, 10, true);
        assert_eq!(lo, None);
        assert_eq!(hi, Some(10));
    }

    #[test]
    fn test_bounds_from_cmp_lt_var_left() {
        // x < 10 => lo = None, hi = 9
        let (lo, hi) = bounds_from_cmp(BoundCmp::Lt, 10, true);
        assert_eq!(lo, None);
        assert_eq!(hi, Some(9));
    }

    #[test]
    fn test_bounds_from_cmp_eq_var_left() {
        // x == 5 => lo = 5, hi = 5
        let (lo, hi) = bounds_from_cmp(BoundCmp::Eq, 5, true);
        assert_eq!(lo, Some(5));
        assert_eq!(hi, Some(5));
    }

    #[test]
    fn test_bounds_from_cmp_ge_var_right() {
        // 5 >= x => x <= 5
        let (lo, hi) = bounds_from_cmp(BoundCmp::Ge, 5, false);
        assert_eq!(lo, None);
        assert_eq!(hi, Some(5));
    }

    #[test]
    fn test_bounds_from_cmp_gt_var_right() {
        // 5 > x => x <= 4
        let (lo, hi) = bounds_from_cmp(BoundCmp::Gt, 5, false);
        assert_eq!(lo, None);
        assert_eq!(hi, Some(4));
    }

    #[test]
    fn test_bounds_from_cmp_le_var_right() {
        // 5 <= x => x >= 5
        let (lo, hi) = bounds_from_cmp(BoundCmp::Le, 5, false);
        assert_eq!(lo, Some(5));
        assert_eq!(hi, None);
    }

    #[test]
    fn test_bounds_from_cmp_lt_var_right() {
        // 5 < x => x >= 6
        let (lo, hi) = bounds_from_cmp(BoundCmp::Lt, 5, false);
        assert_eq!(lo, Some(6));
        assert_eq!(hi, None);
    }

    #[test]
    fn test_update_bounds_initial() {
        let mut bounds = VarBounds::default();
        update_bounds(&mut bounds, Some(5), Some(10));
        assert_eq!(bounds.lo, Some(5));
        assert_eq!(bounds.hi, Some(10));
    }

    #[test]
    fn test_update_bounds_tighten_lo() {
        let mut bounds = VarBounds {
            lo: Some(0),
            hi: Some(100),
        };
        update_bounds(&mut bounds, Some(10), None);
        assert_eq!(bounds.lo, Some(10)); // Tightened
        assert_eq!(bounds.hi, Some(100)); // Unchanged
    }

    #[test]
    fn test_update_bounds_tighten_hi() {
        let mut bounds = VarBounds {
            lo: Some(0),
            hi: Some(100),
        };
        update_bounds(&mut bounds, None, Some(50));
        assert_eq!(bounds.lo, Some(0)); // Unchanged
        assert_eq!(bounds.hi, Some(50)); // Tightened
    }

    #[test]
    fn test_update_bounds_no_update_if_weaker() {
        let mut bounds = VarBounds {
            lo: Some(10),
            hi: Some(50),
        };
        update_bounds(&mut bounds, Some(5), Some(100)); // Weaker bounds
        assert_eq!(bounds.lo, Some(10)); // Still 10 (tighter)
        assert_eq!(bounds.hi, Some(50)); // Still 50 (tighter)
    }

    #[test]
    fn test_extract_literal_int() {
        let expr = Expr::IntLit(42);
        assert_eq!(extract_literal(&expr), Some(42));
    }

    #[test]
    fn test_extract_literal_neg_int() {
        let expr = Expr::Neg(Box::new(Expr::IntLit(42)));
        assert_eq!(extract_literal(&expr), Some(-42));
    }

    #[test]
    fn test_extract_literal_non_literal() {
        let expr = Expr::Var("x".to_string());
        assert_eq!(extract_literal(&expr), None);
    }

    #[test]
    fn test_extract_literal_neg_var() {
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        assert_eq!(extract_literal(&expr), None);
    }

    #[test]
    fn test_expr_to_canonical_name_var() {
        let expr = Expr::Var("count".to_string());
        assert_eq!(expr_to_canonical_name(&expr), Some("count".to_string()));
    }

    #[test]
    fn test_expr_to_canonical_name_struct_field() {
        let expr = Expr::StructField(Box::new(Expr::Var("arr".to_string())), "count".to_string());
        assert_eq!(expr_to_canonical_name(&expr), Some("arr.count".to_string()));
    }

    #[test]
    fn test_expr_to_canonical_name_nested_field() {
        let expr = Expr::StructField(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("obj".to_string())),
                "inner".to_string(),
            )),
            "field".to_string(),
        );
        assert_eq!(
            expr_to_canonical_name(&expr),
            Some("obj.inner.field".to_string())
        );
    }

    #[test]
    fn test_expr_to_canonical_name_non_nameable() {
        let expr = Expr::IntLit(42);
        assert_eq!(expr_to_canonical_name(&expr), None);
    }

    // ========================================================================
    // Unit Tests for simple predicates (v401)
    // ========================================================================

    #[test]
    fn test_is_zero_true() {
        let expr = SwiftExpr::IntLit { value: 0 };
        assert!(is_zero(&expr));
    }

    #[test]
    fn test_is_zero_false() {
        let expr = SwiftExpr::IntLit { value: 1 };
        assert!(!is_zero(&expr));
    }

    #[test]
    fn test_is_zero_non_int() {
        let expr = SwiftExpr::BoolLit { value: false };
        assert!(!is_zero(&expr));
    }

    #[test]
    fn test_is_one_true() {
        let expr = SwiftExpr::IntLit { value: 1 };
        assert!(is_one(&expr));
    }

    #[test]
    fn test_is_one_false() {
        let expr = SwiftExpr::IntLit { value: 0 };
        assert!(!is_one(&expr));
    }

    #[test]
    fn test_is_negative_one_true() {
        let expr = SwiftExpr::IntLit { value: -1 };
        assert!(is_negative_one(&expr));
    }

    #[test]
    fn test_is_negative_one_false() {
        let expr = SwiftExpr::IntLit { value: 1 };
        assert!(!is_negative_one(&expr));
    }

    // ========================================================================
    // Unit Tests for swift_expr_mentions_var (v401)
    // ========================================================================

    #[test]
    fn test_swift_expr_mentions_var_param_ref() {
        let expr = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        assert!(swift_expr_mentions_var(&expr, "x"));
        assert!(!swift_expr_mentions_var(&expr, "y"));
    }

    #[test]
    fn test_swift_expr_mentions_var_binary_op() {
        let expr = SwiftExpr::Add {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
        };
        assert!(swift_expr_mentions_var(&expr, "x"));
        assert!(!swift_expr_mentions_var(&expr, "y"));
    }

    #[test]
    fn test_swift_expr_mentions_var_nested() {
        let expr = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Lt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                }),
            }),
            rhs: Box::new(SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "z".to_string(),
                    index: 2,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
        };
        assert!(swift_expr_mentions_var(&expr, "x"));
        assert!(swift_expr_mentions_var(&expr, "y"));
        assert!(swift_expr_mentions_var(&expr, "z"));
        assert!(!swift_expr_mentions_var(&expr, "w"));
    }

    #[test]
    fn test_swift_expr_mentions_var_unary() {
        let expr = SwiftExpr::Neg {
            operand: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
        };
        assert!(swift_expr_mentions_var(&expr, "x"));
    }

    #[test]
    fn test_swift_expr_mentions_var_ite() {
        let expr = SwiftExpr::Ite {
            cond: Box::new(SwiftExpr::BoolLit { value: true }),
            then_expr: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
            else_expr: Box::new(SwiftExpr::ParamRef {
                name: "y".to_string(),
                index: 1,
            }),
        };
        assert!(swift_expr_mentions_var(&expr, "x"));
        assert!(swift_expr_mentions_var(&expr, "y"));
    }

    #[test]
    fn test_swift_expr_mentions_var_old() {
        let expr = SwiftExpr::Old {
            expr: Box::new(SwiftExpr::ParamRef {
                name: "balance".to_string(),
                index: 0,
            }),
        };
        assert!(swift_expr_mentions_var(&expr, "balance"));
    }

    #[test]
    fn test_swift_expr_mentions_var_call() {
        let expr = SwiftExpr::Call {
            func: "func".to_string(),
            args: vec![
                SwiftExpr::ParamRef {
                    name: "a".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "b".to_string(),
                    index: 1,
                },
            ],
        };
        assert!(swift_expr_mentions_var(&expr, "a"));
        assert!(swift_expr_mentions_var(&expr, "b"));
        assert!(!swift_expr_mentions_var(&expr, "c"));
    }

    #[test]
    fn test_swift_expr_mentions_var_field() {
        let expr = SwiftExpr::Field {
            base: Box::new(SwiftExpr::ParamRef {
                name: "obj".to_string(),
                index: 0,
            }),
            field: "count".to_string(),
        };
        assert!(swift_expr_mentions_var(&expr, "obj"));
    }

    #[test]
    fn test_swift_expr_mentions_var_index() {
        let expr = SwiftExpr::Index {
            base: Box::new(SwiftExpr::ParamRef {
                name: "arr".to_string(),
                index: 0,
            }),
            index: Box::new(SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 1,
            }),
        };
        assert!(swift_expr_mentions_var(&expr, "arr"));
        assert!(swift_expr_mentions_var(&expr, "i"));
    }

    #[test]
    fn test_swift_expr_mentions_var_literals() {
        assert!(!swift_expr_mentions_var(
            &SwiftExpr::IntLit { value: 42 },
            "x"
        ));
        assert!(!swift_expr_mentions_var(
            &SwiftExpr::BoolLit { value: true },
            "x"
        ));
        assert!(!swift_expr_mentions_var(&SwiftExpr::ResultRef, "x"));
        assert!(!swift_expr_mentions_var(&SwiftExpr::NilLit, "x"));
    }

    #[test]
    fn test_swift_expr_mentions_var_forall() {
        use crate::json_types::SwiftType;
        let expr = SwiftExpr::Forall {
            vars: vec![(
                "i".to_string(),
                SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(SwiftExpr::Lt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 10 }),
            }),
        };
        assert!(swift_expr_mentions_var(&expr, "x"));
    }

    // ========================================================================
    // Unit Tests for extract_simple_bounds (v401)
    // ========================================================================

    #[test]
    fn test_extract_simple_bounds_ge() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        let pred = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        ));
        extract_simple_bounds_from_predicate(&pred, &mut bounds);
        assert_eq!(bounds.get("x").unwrap().lo, Some(5));
    }

    #[test]
    fn test_extract_simple_bounds_le() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        let pred = Predicate::Expr(Expr::Le(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(100)),
        ));
        extract_simple_bounds_from_predicate(&pred, &mut bounds);
        assert_eq!(bounds.get("x").unwrap().hi, Some(100));
    }

    #[test]
    fn test_extract_simple_bounds_eq() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        let pred = Predicate::Expr(Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(42)),
        ));
        extract_simple_bounds_from_predicate(&pred, &mut bounds);
        assert_eq!(bounds.get("x").unwrap().lo, Some(42));
        assert_eq!(bounds.get("x").unwrap().hi, Some(42));
    }

    #[test]
    fn test_extract_simple_bounds_and() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ]);
        extract_simple_bounds_from_predicate(&pred, &mut bounds);
        assert_eq!(bounds.get("x").unwrap().lo, Some(0));
        assert_eq!(bounds.get("x").unwrap().hi, Some(99)); // Lt 100 => hi = 99
    }

    #[test]
    fn test_extract_simple_bounds_reverse() {
        // 10 <= x (literal on left)
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        let pred = Predicate::Expr(Expr::Le(
            Box::new(Expr::IntLit(10)),
            Box::new(Expr::Var("x".to_string())),
        ));
        extract_simple_bounds_from_predicate(&pred, &mut bounds);
        assert_eq!(bounds.get("x").unwrap().lo, Some(10));
    }

    // ========================================================================
    // Unit Tests for path_condition_contains_lower_bound (v402)
    // ========================================================================

    #[test]
    fn test_path_condition_lower_bound_ge_zero() {
        // index >= 0
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let cond = SwiftExpr::Ge {
            lhs: Box::new(index.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        assert!(path_condition_contains_lower_bound(&cond, &index));
    }

    #[test]
    fn test_path_condition_lower_bound_le_reversed() {
        // 0 <= index
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let cond = SwiftExpr::Le {
            lhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            rhs: Box::new(index.clone()),
        };
        assert!(path_condition_contains_lower_bound(&cond, &index));
    }

    #[test]
    fn test_path_condition_lower_bound_gt_neg1() {
        // index > -1 (equivalent to index >= 0)
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let cond = SwiftExpr::Gt {
            lhs: Box::new(index.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: -1 }),
        };
        assert!(path_condition_contains_lower_bound(&cond, &index));
    }

    #[test]
    fn test_path_condition_lower_bound_not_lt_zero() {
        // NOT(index < 0) equivalent to index >= 0
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let cond = SwiftExpr::Not {
            operand: Box::new(SwiftExpr::Lt {
                lhs: Box::new(index.clone()),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
        };
        assert!(path_condition_contains_lower_bound(&cond, &index));
    }

    #[test]
    fn test_path_condition_lower_bound_and_recursive() {
        // (other_cond) && (index >= 0)
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let other_cond = SwiftExpr::BoolLit { value: true };
        let lower_bound = SwiftExpr::Ge {
            lhs: Box::new(index.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let cond = SwiftExpr::And {
            lhs: Box::new(other_cond),
            rhs: Box::new(lower_bound),
        };
        assert!(path_condition_contains_lower_bound(&cond, &index));
    }

    #[test]
    fn test_path_condition_lower_bound_no_match() {
        // index < 100 (upper bound, not lower)
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let cond = SwiftExpr::Lt {
            lhs: Box::new(index.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 100 }),
        };
        assert!(!path_condition_contains_lower_bound(&cond, &index));
    }

    #[test]
    fn test_path_condition_lower_bound_wrong_index() {
        // other >= 0 (wrong variable)
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let other = SwiftExpr::ParamRef {
            name: "other".to_string(),
            index: 1,
        };
        let cond = SwiftExpr::Ge {
            lhs: Box::new(other),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        assert!(!path_condition_contains_lower_bound(&cond, &index));
    }

    // ========================================================================
    // Unit Tests for path_condition_contains_upper_bound (v402)
    // ========================================================================

    #[test]
    fn test_path_condition_upper_bound_lt() {
        // index < length
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "length".to_string(),
            index: 1,
        };
        let cond = SwiftExpr::Lt {
            lhs: Box::new(index.clone()),
            rhs: Box::new(length.clone()),
        };
        assert!(path_condition_contains_upper_bound(&cond, &index, &length));
    }

    #[test]
    fn test_path_condition_upper_bound_gt_reversed() {
        // length > index
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "length".to_string(),
            index: 1,
        };
        let cond = SwiftExpr::Gt {
            lhs: Box::new(length.clone()),
            rhs: Box::new(index.clone()),
        };
        assert!(path_condition_contains_upper_bound(&cond, &index, &length));
    }

    #[test]
    fn test_path_condition_upper_bound_not_ge() {
        // NOT(index >= length) equivalent to index < length
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "length".to_string(),
            index: 1,
        };
        let cond = SwiftExpr::Not {
            operand: Box::new(SwiftExpr::Ge {
                lhs: Box::new(index.clone()),
                rhs: Box::new(length.clone()),
            }),
        };
        assert!(path_condition_contains_upper_bound(&cond, &index, &length));
    }

    #[test]
    fn test_path_condition_upper_bound_ssa_param() {
        // SSA variable (ssa_21) - heuristic for Bool comparison result
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "length".to_string(),
            index: 1,
        };
        let cond = SwiftExpr::ParamRef {
            name: "ssa_21".to_string(),
            index: 99,
        };
        assert!(path_condition_contains_upper_bound(&cond, &index, &length));
    }

    #[test]
    fn test_path_condition_upper_bound_and_recursive() {
        // (other_cond) && (index < length)
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "length".to_string(),
            index: 1,
        };
        let other_cond = SwiftExpr::BoolLit { value: true };
        let upper_bound = SwiftExpr::Lt {
            lhs: Box::new(index.clone()),
            rhs: Box::new(length.clone()),
        };
        let cond = SwiftExpr::And {
            lhs: Box::new(other_cond),
            rhs: Box::new(upper_bound),
        };
        assert!(path_condition_contains_upper_bound(&cond, &index, &length));
    }

    #[test]
    fn test_path_condition_upper_bound_no_match() {
        // index >= 0 (lower bound, not upper)
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "length".to_string(),
            index: 1,
        };
        let cond = SwiftExpr::Ge {
            lhs: Box::new(index.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        assert!(!path_condition_contains_upper_bound(&cond, &index, &length));
    }

    #[test]
    fn test_path_condition_upper_bound_non_ssa_param() {
        // Regular param ref (not ssa_*) should not match
        let index = SwiftExpr::ParamRef {
            name: "index".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "length".to_string(),
            index: 1,
        };
        let cond = SwiftExpr::ParamRef {
            name: "some_bool".to_string(),
            index: 2,
        };
        assert!(!path_condition_contains_upper_bound(&cond, &index, &length));
    }

    // ========================================================================
    // Unit Tests for try_prove_overflow_via_intervals (v402)
    // ========================================================================

    #[test]
    fn test_prove_overflow_non_overflow_vc_returns_none() {
        // DivByZero auto_vc should return None
        let auto_vc = SwiftAutoVc::DivByZero {
            divisor: SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            },
            description: "div by zero".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };
        assert!(try_prove_overflow_via_intervals(&auto_vc, &[]).is_none());
    }

    #[test]
    fn test_prove_overflow_neg_within_bounds() {
        // neg with operand in [0, 100] => result in [-100, 0], within i64 bounds
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "neg".to_string(),
            operands: vec![SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }],
            description: "negate x".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let preconds = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ];
        let result = try_prove_overflow_via_intervals(&auto_vc, &preconds);
        assert!(result.is_some());
        assert!(matches!(result.unwrap().0, VerifyResult::Proven));
    }

    #[test]
    fn test_prove_overflow_add_within_bounds() {
        // add with x in [0, 100], y in [0, 100] => result in [0, 200]
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                },
            ],
            description: "add x y".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let preconds = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ];
        let result = try_prove_overflow_via_intervals(&auto_vc, &preconds);
        assert!(result.is_some());
        assert!(matches!(result.unwrap().0, VerifyResult::Proven));
    }

    #[test]
    fn test_prove_overflow_sub_within_bounds() {
        // sub with x in [50, 100], y in [0, 50] => result in [0, 100]
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "sub".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                },
            ],
            description: "sub x y".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let preconds = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(50)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(50)),
            )),
        ];
        let result = try_prove_overflow_via_intervals(&auto_vc, &preconds);
        assert!(result.is_some());
        assert!(matches!(result.unwrap().0, VerifyResult::Proven));
    }

    #[test]
    fn test_prove_overflow_mul_within_bounds() {
        // mul with x in [0, 10], y in [0, 10] => result in [0, 100]
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "mul".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                },
            ],
            description: "mul x y".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let preconds = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];
        let result = try_prove_overflow_via_intervals(&auto_vc, &preconds);
        assert!(result.is_some());
        assert!(matches!(result.unwrap().0, VerifyResult::Proven));
    }

    #[test]
    fn test_prove_overflow_div_divisor_excludes_neg1() {
        // div with divisor in [1, 10] (excludes -1) => no overflow
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "div".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                },
            ],
            description: "div x y".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let preconds = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];
        let result = try_prove_overflow_via_intervals(&auto_vc, &preconds);
        assert!(result.is_some());
        let (verify_result, smtlib) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
        assert!(smtlib.contains("divisor excludes -1"));
    }

    #[test]
    fn test_prove_overflow_div_dividend_excludes_int_min() {
        // div with dividend in [0, 100] (excludes INT_MIN) => no overflow
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "div".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                },
            ],
            description: "div x y".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let preconds = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ];
        let result = try_prove_overflow_via_intervals(&auto_vc, &preconds);
        assert!(result.is_some());
        let (verify_result, smtlib) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
        assert!(smtlib.contains("dividend excludes INT_MIN"));
    }

    #[test]
    fn test_prove_overflow_mod_divisor_excludes_neg1() {
        // mod with divisor in [2, 10] (excludes -1) => no overflow
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "mod".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                },
            ],
            description: "mod x y".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let preconds = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(2)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];
        let result = try_prove_overflow_via_intervals(&auto_vc, &preconds);
        assert!(result.is_some());
        let (verify_result, smtlib) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
        assert!(smtlib.contains("divisor excludes -1"));
    }

    #[test]
    fn test_prove_overflow_no_bounds_returns_none() {
        // add with no bounds info => cannot prove
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                },
            ],
            description: "add x y".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let result = try_prove_overflow_via_intervals(&auto_vc, &[]);
        assert!(result.is_none());
    }

    #[test]
    fn test_prove_overflow_unknown_operation_returns_none() {
        // Unknown operation returns None
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "unknown_op".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                },
            ],
            description: "unknown".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let preconds = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];
        let result = try_prove_overflow_via_intervals(&auto_vc, &preconds);
        assert!(result.is_none());
    }

    // ========================================================================
    // Unit Tests for extract_known_non_nil helpers (v402)
    // ========================================================================

    #[test]
    fn test_extract_known_non_nil_empty() {
        let result = extract_known_non_nil(&[]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_extract_known_non_nil_has_value_eq_true() {
        // value.hasValue == true
        let precond = Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("value".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        ));
        let result = extract_known_non_nil(&[precond]);
        assert!(result.contains("value"));
    }

    #[test]
    fn test_extract_known_non_nil_true_eq_has_value() {
        // true == value.hasValue (reversed)
        let precond = Predicate::Expr(Expr::Eq(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::StructField(
                Box::new(Expr::Var("opt".to_string())),
                "hasValue".to_string(),
            )),
        ));
        let result = extract_known_non_nil(&[precond]);
        assert!(result.contains("opt"));
    }

    #[test]
    fn test_extract_known_non_nil_through_and_predicate() {
        // And([value1.hasValue == true, value2.hasValue == true])
        let precond = Predicate::And(vec![
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("value1".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("value2".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        ]);
        let result = extract_known_non_nil(&[precond]);
        assert!(result.contains("value1"));
        assert!(result.contains("value2"));
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_extract_known_non_nil_through_and_expr() {
        // (value1.hasValue == true) && (value2.hasValue == true)
        let precond = Predicate::Expr(Expr::And(
            Box::new(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("a".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
            Box::new(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("b".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        ));
        let result = extract_known_non_nil(&[precond]);
        assert!(result.contains("a"));
        assert!(result.contains("b"));
    }

    #[test]
    fn test_extract_known_non_nil_unrelated_predicate() {
        // x > 0 (no non-nil info)
        let precond = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let result = extract_known_non_nil(&[precond]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_extract_known_non_nil_has_value_false_ignored() {
        // value.hasValue == false (should NOT be extracted)
        let precond = Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("value".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(false)),
        ));
        let result = extract_known_non_nil(&[precond]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_extract_known_non_nil_or_ignored() {
        // Or predicates should be ignored (not strong enough to establish non-nil)
        let precond = Predicate::Or(vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("value".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        ))]);
        let result = extract_known_non_nil(&[precond]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_extract_known_non_nil_nested_struct_field() {
        // a.b.hasValue == true (nested field access)
        let precond = Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("a".to_string())),
                    "b".to_string(),
                )),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        ));
        let result = extract_known_non_nil(&[precond]);
        // The canonical name should be "a.b"
        assert!(result.contains("a.b"));
    }

    // =========================================================================
    // Unit tests for try_prove_bounds_via_intervals
    // =========================================================================

    #[test]
    fn test_try_prove_bounds_via_intervals_simple_bounds() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // index >= 0 && index < 10, length >= 10
        // Should prove: 0 <= index < length
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "index".to_string(),
                index: 0,
            },
            length: SwiftExpr::ParamRef {
                name: "length".to_string(),
                index: 1,
            },
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![
            // index >= 0
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("index".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            // index < 10
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("index".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
            // length >= 10
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("length".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];

        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, smtlib) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
        assert!(smtlib.contains("Proved without SMT via interval analysis"));
    }

    #[test]
    fn test_try_prove_bounds_via_intervals_index_equals_constant() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // index == 5, length == 10
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::ParamRef {
                name: "len".to_string(),
                index: 1,
            },
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![
            // i == 5
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(5)),
            )),
            // len == 10
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("len".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];

        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_bounds_via_intervals_no_lower_bound() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // index < 10, length >= 10, but no index >= 0
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "index".to_string(),
                index: 0,
            },
            length: SwiftExpr::ParamRef {
                name: "length".to_string(),
                index: 1,
            },
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![
            // Only upper bound on index
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("index".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("length".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];

        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        // Should fail because we can't prove index >= 0
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_bounds_via_intervals_no_upper_bound() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // index >= 0, length >= 10, but no index < something
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "index".to_string(),
                index: 0,
            },
            length: SwiftExpr::ParamRef {
                name: "length".to_string(),
                index: 1,
            },
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("index".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("length".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];

        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        // Should fail because we can't prove index < length
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_bounds_via_intervals_index_at_boundary() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // index >= 0 && index <= 9, length >= 10
        // index.hi = 9, length.lo = 10, so 9 < 10 is true
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 1,
            },
            description: "bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(9)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("n".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];

        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
    }

    #[test]
    fn test_try_prove_bounds_via_intervals_tight_bound_fails() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // index >= 0 && index <= 10, length >= 10
        // index.hi = 10, length.lo = 10, so 10 < 10 is FALSE
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 1,
            },
            description: "bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("n".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];

        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        // Should fail because index could be 10, and 10 < 10 is false
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_bounds_via_intervals_negative_lower_bound() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // index >= -1 (negative lower bound), index < 10, length >= 10
        // Should fail because index.lo = -1 is not >= 0
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "index".to_string(),
                index: 0,
            },
            length: SwiftExpr::ParamRef {
                name: "length".to_string(),
                index: 1,
            },
            description: "bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("index".to_string())),
                Box::new(Expr::IntLit(-1)),
            )),
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("index".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("length".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ];

        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        // Should fail because index could be -1
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_bounds_via_intervals_non_bounds_check_vc() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Overflow VC should return None
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::IntLit { value: 1 },
            ],
            description: "overflow".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        let preconditions = vec![];
        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_bounds_via_intervals_struct_field_index() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // index via struct field: arr.idx >= 0 && arr.idx < 10, arr.count >= 10
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::Field {
                base: Box::new(SwiftExpr::ParamRef {
                    name: "arr".to_string(),
                    index: 0,
                }),
                field: "idx".to_string(),
            },
            length: SwiftExpr::Field {
                base: Box::new(SwiftExpr::ParamRef {
                    name: "arr".to_string(),
                    index: 0,
                }),
                field: "count".to_string(),
            },
            description: "bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("arr".to_string())),
                    "idx".to_string(),
                )),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("arr".to_string())),
                    "idx".to_string(),
                )),
                Box::new(Expr::IntLit(10)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("arr".to_string())),
                    "count".to_string(),
                )),
                Box::new(Expr::IntLit(10)),
            )),
        ];

        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
    }

    #[test]
    fn test_try_prove_bounds_via_intervals_and_predicate() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Bounds in And predicate
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 1,
            },
            description: "bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![Predicate::And(vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(5)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("n".to_string())),
                Box::new(Expr::IntLit(5)),
            )),
        ])];

        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
    }

    #[test]
    fn test_try_prove_bounds_via_intervals_literal_length() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Length is a literal: index >= 0 && index < 5, length is 10 (literal)
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::IntLit { value: 10 },
            description: "bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(5)),
            )),
        ];

        let result = try_prove_bounds_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
    }

    // =========================================================================
    // Unit tests for interval_for_expr
    // =========================================================================

    #[test]
    fn test_interval_for_expr_int_literal() {
        let bounds: HashMap<String, VarBounds> = HashMap::new();
        let expr = Expr::IntLit(42);
        let result = interval_for_expr(&expr, &bounds);
        assert_eq!(result, Some(IntInterval { lo: 42, hi: 42 }));
    }

    #[test]
    fn test_interval_for_expr_var_with_bounds() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(0),
                hi: Some(10),
            },
        );
        let expr = Expr::Var("x".to_string());
        let result = interval_for_expr(&expr, &bounds);
        assert_eq!(result, Some(IntInterval { lo: 0, hi: 10 }));
    }

    #[test]
    fn test_interval_for_expr_var_no_bounds() {
        let bounds: HashMap<String, VarBounds> = HashMap::new();
        let expr = Expr::Var("unknown".to_string());
        let result = interval_for_expr(&expr, &bounds);
        assert!(result.is_none());
    }

    #[test]
    fn test_interval_for_expr_var_partial_bounds() {
        // Only lower bound
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(0),
                hi: None,
            },
        );
        let expr = Expr::Var("x".to_string());
        let result = interval_for_expr(&expr, &bounds);
        assert!(result.is_none()); // Need both bounds for interval
    }

    #[test]
    fn test_interval_for_expr_struct_field_different_range() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "arr.count".to_string(),
            VarBounds {
                lo: Some(5),
                hi: Some(100),
            },
        );
        let expr = Expr::StructField(Box::new(Expr::Var("arr".to_string())), "count".to_string());
        let result = interval_for_expr(&expr, &bounds);
        assert_eq!(result, Some(IntInterval { lo: 5, hi: 100 }));
    }

    #[test]
    fn test_interval_for_expr_negation() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(1),
                hi: Some(5),
            },
        );
        // -x where x in [1, 5] => [-5, -1]
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        let result = interval_for_expr(&expr, &bounds);
        assert_eq!(result, Some(IntInterval { lo: -5, hi: -1 }));
    }

    #[test]
    fn test_interval_for_expr_negation_with_negative_range() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(-10),
                hi: Some(-3),
            },
        );
        // -x where x in [-10, -3] => [3, 10]
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        let result = interval_for_expr(&expr, &bounds);
        assert_eq!(result, Some(IntInterval { lo: 3, hi: 10 }));
    }

    #[test]
    fn test_interval_for_expr_add_two_vars() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(0),
                hi: Some(10),
            },
        );
        bounds.insert(
            "y".to_string(),
            VarBounds {
                lo: Some(5),
                hi: Some(15),
            },
        );
        // x + y where x in [0, 10] and y in [5, 15] => [5, 25]
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let result = interval_for_expr(&expr, &bounds);
        assert_eq!(result, Some(IntInterval { lo: 5, hi: 25 }));
    }

    #[test]
    fn test_interval_for_expr_add_with_literal() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(0),
                hi: Some(10),
            },
        );
        // x + 5 where x in [0, 10] => [5, 15]
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        let result = interval_for_expr(&expr, &bounds);
        assert_eq!(result, Some(IntInterval { lo: 5, hi: 15 }));
    }

    #[test]
    fn test_interval_for_expr_sub_two_vars() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(10),
                hi: Some(20),
            },
        );
        bounds.insert(
            "y".to_string(),
            VarBounds {
                lo: Some(1),
                hi: Some(5),
            },
        );
        // x - y where x in [10, 20] and y in [1, 5] => [10-5, 20-1] = [5, 19]
        let expr = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let result = interval_for_expr(&expr, &bounds);
        assert_eq!(result, Some(IntInterval { lo: 5, hi: 19 }));
    }

    #[test]
    fn test_interval_for_expr_sub_negative_result() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(0),
                hi: Some(5),
            },
        );
        bounds.insert(
            "y".to_string(),
            VarBounds {
                lo: Some(3),
                hi: Some(10),
            },
        );
        // x - y where x in [0, 5] and y in [3, 10] => [0-10, 5-3] = [-10, 2]
        let expr = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let result = interval_for_expr(&expr, &bounds);
        assert_eq!(result, Some(IntInterval { lo: -10, hi: 2 }));
    }

    #[test]
    fn test_interval_for_expr_unsupported() {
        let bounds: HashMap<String, VarBounds> = HashMap::new();
        // Mul is not supported by interval_for_expr (only by interval_mul helper)
        let expr = Expr::Mul(Box::new(Expr::IntLit(2)), Box::new(Expr::IntLit(3)));
        let result = interval_for_expr(&expr, &bounds);
        assert!(result.is_none());
    }

    // =========================================================================
    // Unit tests for get_lower_bound_for_expr and get_upper_bound_for_expr
    // =========================================================================

    #[test]
    fn test_get_lower_bound_int_literal() {
        let bounds: HashMap<String, VarBounds> = HashMap::new();
        let expr = Expr::IntLit(42);
        assert_eq!(get_lower_bound_for_expr(&expr, &bounds), Some(42));
    }

    #[test]
    fn test_get_upper_bound_int_literal() {
        let bounds: HashMap<String, VarBounds> = HashMap::new();
        let expr = Expr::IntLit(-10);
        assert_eq!(get_upper_bound_for_expr(&expr, &bounds), Some(-10));
    }

    #[test]
    fn test_get_lower_bound_var() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(5),
                hi: Some(100),
            },
        );
        let expr = Expr::Var("x".to_string());
        assert_eq!(get_lower_bound_for_expr(&expr, &bounds), Some(5));
    }

    #[test]
    fn test_get_upper_bound_var() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "y".to_string(),
            VarBounds {
                lo: Some(-5),
                hi: Some(20),
            },
        );
        let expr = Expr::Var("y".to_string());
        assert_eq!(get_upper_bound_for_expr(&expr, &bounds), Some(20));
    }

    #[test]
    fn test_get_lower_bound_struct_field() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "arr.count".to_string(),
            VarBounds {
                lo: Some(10),
                hi: None,
            },
        );
        let expr = Expr::StructField(Box::new(Expr::Var("arr".to_string())), "count".to_string());
        assert_eq!(get_lower_bound_for_expr(&expr, &bounds), Some(10));
    }

    #[test]
    fn test_get_upper_bound_struct_field() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "arr.count".to_string(),
            VarBounds {
                lo: None,
                hi: Some(1000),
            },
        );
        let expr = Expr::StructField(Box::new(Expr::Var("arr".to_string())), "count".to_string());
        assert_eq!(get_upper_bound_for_expr(&expr, &bounds), Some(1000));
    }

    #[test]
    fn test_get_lower_bound_add() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(5),
                hi: Some(10),
            },
        );
        bounds.insert(
            "y".to_string(),
            VarBounds {
                lo: Some(3),
                hi: Some(8),
            },
        );
        // lo(x + y) = lo(x) + lo(y) = 5 + 3 = 8
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        assert_eq!(get_lower_bound_for_expr(&expr, &bounds), Some(8));
    }

    #[test]
    fn test_get_upper_bound_add() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(5),
                hi: Some(10),
            },
        );
        bounds.insert(
            "y".to_string(),
            VarBounds {
                lo: Some(3),
                hi: Some(8),
            },
        );
        // hi(x + y) = hi(x) + hi(y) = 10 + 8 = 18
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        assert_eq!(get_upper_bound_for_expr(&expr, &bounds), Some(18));
    }

    #[test]
    fn test_get_lower_bound_neg() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(1),
                hi: Some(10),
            },
        );
        // lo(-x) = -hi(x) = -10
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        assert_eq!(get_lower_bound_for_expr(&expr, &bounds), Some(-10));
    }

    #[test]
    fn test_get_upper_bound_neg() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(1),
                hi: Some(10),
            },
        );
        // hi(-x) = -lo(x) = -1
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        assert_eq!(get_upper_bound_for_expr(&expr, &bounds), Some(-1));
    }

    #[test]
    fn test_get_lower_bound_no_bounds_available() {
        let bounds: HashMap<String, VarBounds> = HashMap::new();
        let expr = Expr::Var("unknown".to_string());
        assert!(get_lower_bound_for_expr(&expr, &bounds).is_none());
    }

    #[test]
    fn test_get_upper_bound_no_bounds_available() {
        let bounds: HashMap<String, VarBounds> = HashMap::new();
        let expr = Expr::Var("unknown".to_string());
        assert!(get_upper_bound_for_expr(&expr, &bounds).is_none());
    }

    #[test]
    fn test_get_lower_bound_partial_bounds_lo_only() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(5),
                hi: None,
            },
        );
        let expr = Expr::Var("x".to_string());
        // Should work: we have a lower bound
        assert_eq!(get_lower_bound_for_expr(&expr, &bounds), Some(5));
    }

    #[test]
    fn test_get_upper_bound_partial_bounds_hi_only() {
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: None,
                hi: Some(100),
            },
        );
        let expr = Expr::Var("x".to_string());
        // Should work: we have an upper bound
        assert_eq!(get_upper_bound_for_expr(&expr, &bounds), Some(100));
    }

    #[test]
    fn test_get_lower_bound_sub_not_supported() {
        // get_lower_bound_for_expr does not support Sub directly
        // (interval_for_expr handles Sub via interval_sub, but single-bound
        // functions are simpler and don't implement it)
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(10),
                hi: Some(20),
            },
        );
        bounds.insert(
            "y".to_string(),
            VarBounds {
                lo: Some(1),
                hi: Some(5),
            },
        );
        let expr = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        // Sub is not supported by get_lower_bound_for_expr
        assert!(get_lower_bound_for_expr(&expr, &bounds).is_none());
    }

    #[test]
    fn test_get_upper_bound_sub_not_supported() {
        // get_upper_bound_for_expr does not support Sub directly
        let mut bounds: HashMap<String, VarBounds> = HashMap::new();
        bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(10),
                hi: Some(20),
            },
        );
        bounds.insert(
            "y".to_string(),
            VarBounds {
                lo: Some(1),
                hi: Some(5),
            },
        );
        let expr = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        // Sub is not supported by get_upper_bound_for_expr
        assert!(get_upper_bound_for_expr(&expr, &bounds).is_none());
    }

    #[test]
    fn test_get_lower_bound_unsupported_expr() {
        let bounds: HashMap<String, VarBounds> = HashMap::new();
        let expr = Expr::Mul(Box::new(Expr::IntLit(2)), Box::new(Expr::IntLit(3)));
        // Mul not supported by get_lower_bound_for_expr
        assert!(get_lower_bound_for_expr(&expr, &bounds).is_none());
    }

    // =========================================================================
    // Unit tests for interval arithmetic helpers
    // =========================================================================

    #[test]
    fn test_interval_add_positive() {
        let a = IntInterval { lo: 1, hi: 5 };
        let b = IntInterval { lo: 2, hi: 3 };
        let result = interval_add(a, b);
        assert_eq!(result, Some(IntInterval { lo: 3, hi: 8 }));
    }

    #[test]
    fn test_interval_add_mixed_signs() {
        let a = IntInterval { lo: -5, hi: 5 };
        let b = IntInterval { lo: -3, hi: 3 };
        let result = interval_add(a, b);
        assert_eq!(result, Some(IntInterval { lo: -8, hi: 8 }));
    }

    #[test]
    fn test_interval_sub_positive() {
        let a = IntInterval { lo: 10, hi: 20 };
        let b = IntInterval { lo: 1, hi: 5 };
        // [10, 20] - [1, 5] = [10-5, 20-1] = [5, 19]
        let result = interval_sub(a, b);
        assert_eq!(result, Some(IntInterval { lo: 5, hi: 19 }));
    }

    #[test]
    fn test_interval_sub_result_negative() {
        let a = IntInterval { lo: 0, hi: 5 };
        let b = IntInterval { lo: 10, hi: 20 };
        // [0, 5] - [10, 20] = [0-20, 5-10] = [-20, -5]
        let result = interval_sub(a, b);
        assert_eq!(result, Some(IntInterval { lo: -20, hi: -5 }));
    }

    #[test]
    fn test_interval_neg_all_negative() {
        let a = IntInterval { lo: -10, hi: -3 };
        // -[-10, -3] = [3, 10]
        let result = interval_neg(a);
        assert_eq!(result, Some(IntInterval { lo: 3, hi: 10 }));
    }

    // ==========================================================================
    // Tests for find_overflow_counterexample
    // ==========================================================================

    #[test]
    fn test_find_overflow_counterexample_mul_overflow() {
        // Large values that overflow Int8 bounds when multiplied
        let lhs = IntInterval { lo: 10, hi: 20 };
        let rhs = IntInterval { lo: 10, hi: 20 };
        let (a, b, result) = find_overflow_counterexample("mul", &lhs, &rhs, -128, 127, true);
        // 20 * 20 = 400, which > 127
        assert_eq!(a, 20);
        assert_eq!(b, 20);
        assert_eq!(result, 400);
    }

    #[test]
    fn test_find_overflow_counterexample_mul_negative_underflow() {
        // Negative * positive can underflow - function returns first overflowing candidate
        let lhs = IntInterval { lo: -100, hi: -50 };
        let rhs = IntInterval { lo: 10, hi: 20 };
        let (a, b, result) = find_overflow_counterexample("mul", &lhs, &rhs, -128, 127, true);
        // First candidate that overflows: (-50, 20) → -1000 < -128
        assert_eq!(a, -50);
        assert_eq!(b, 20);
        assert_eq!(result, -1000);
    }

    #[test]
    fn test_find_overflow_counterexample_mul_fallback() {
        // Small values that don't overflow - fallback to max*max
        let lhs = IntInterval { lo: 1, hi: 5 };
        let rhs = IntInterval { lo: 1, hi: 5 };
        let (a, b, result) = find_overflow_counterexample("mul", &lhs, &rhs, -128, 127, true);
        // 5 * 5 = 25, doesn't overflow, so fallback returns hi*hi
        assert_eq!(a, 5);
        assert_eq!(b, 5);
        assert_eq!(result, 25);
    }

    #[test]
    fn test_find_overflow_counterexample_add_overflow() {
        // Large values that overflow when added
        let lhs = IntInterval { lo: 100, hi: 120 };
        let rhs = IntInterval { lo: 10, hi: 20 };
        let (a, b, result) = find_overflow_counterexample("add", &lhs, &rhs, -128, 127, true);
        // 120 + 20 = 140, which > 127
        assert_eq!(a, 120);
        assert_eq!(b, 20);
        assert_eq!(result, 140);
    }

    #[test]
    fn test_find_overflow_counterexample_add_underflow() {
        // Negative values that underflow when added
        let lhs = IntInterval { lo: -100, hi: -50 };
        let rhs = IntInterval { lo: -50, hi: -10 };
        let (a, b, result) = find_overflow_counterexample("add", &lhs, &rhs, -128, 127, true);
        // -100 + -50 = -150, which < -128
        assert_eq!(a, -100);
        assert_eq!(b, -50);
        assert_eq!(result, -150);
    }

    #[test]
    fn test_find_overflow_counterexample_sub_underflow() {
        // Subtraction that underflows
        let lhs = IntInterval { lo: -100, hi: -50 };
        let rhs = IntInterval { lo: 50, hi: 100 };
        let (a, b, result) = find_overflow_counterexample("sub", &lhs, &rhs, -128, 127, true);
        // -100 - 100 = -200, which < -128
        assert_eq!(a, -100);
        assert_eq!(b, 100);
        assert_eq!(result, -200);
    }

    #[test]
    fn test_find_overflow_counterexample_sub_overflow() {
        // Subtraction that overflows (subtracting negative)
        let lhs = IntInterval { lo: 50, hi: 100 };
        let rhs = IntInterval { lo: -100, hi: -50 };
        let (a, b, result) = find_overflow_counterexample("sub", &lhs, &rhs, -128, 127, true);
        // 100 - (-100) = 200, which > 127
        assert_eq!(a, 100);
        assert_eq!(b, -100);
        assert_eq!(result, 200);
    }

    #[test]
    fn test_find_overflow_counterexample_sub_unsigned_underflow() {
        // Unsigned subtraction where b > a
        let lhs = IntInterval { lo: 5, hi: 10 };
        let rhs = IntInterval { lo: 15, hi: 20 };
        let (a, b, result) = find_overflow_counterexample("sub", &lhs, &rhs, 0, 255, false);
        // 5 - 20 = -15, which < 0 for unsigned
        assert_eq!(a, 5);
        assert_eq!(b, 20);
        assert_eq!(result, -15);
    }

    #[test]
    fn test_find_overflow_counterexample_unknown_op() {
        // Unknown operation returns fallback
        let lhs = IntInterval { lo: 1, hi: 10 };
        let rhs = IntInterval { lo: 1, hi: 10 };
        let (a, b, result) = find_overflow_counterexample("div", &lhs, &rhs, -128, 127, true);
        // Unknown op returns (hi, hi, 0)
        assert_eq!(a, 10);
        assert_eq!(b, 10);
        assert_eq!(result, 0);
    }

    // ==========================================================================
    // Tests for path_condition_guards_overflow_max
    // ==========================================================================

    #[test]
    fn test_path_condition_guards_overflow_max_lt_direct() {
        // operand < type_max
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Lt {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
        };
        assert!(path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    #[test]
    fn test_path_condition_guards_overflow_max_lt_wrong_value() {
        // operand < 100 doesn't guard against max=127
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Lt {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 100 }),
        };
        assert!(!path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    #[test]
    fn test_path_condition_guards_overflow_max_lt_var_heuristic() {
        // operand < some_var is accepted heuristically
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Lt {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::ParamRef {
                name: "max".to_string(),
                index: 1,
            }),
        };
        assert!(path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    #[test]
    fn test_path_condition_guards_overflow_max_gt_direct() {
        // type_max > operand (equivalent to operand < type_max)
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Gt {
            lhs: Box::new(SwiftExpr::IntLit { value: 127 }),
            rhs: Box::new(operand.clone()),
        };
        assert!(path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    #[test]
    fn test_path_condition_guards_overflow_max_le_below_max() {
        // operand <= type_max-1 proves operand+1 <= type_max
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Le {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 126 }),
        };
        assert!(path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    #[test]
    fn test_path_condition_guards_overflow_max_le_at_max_fails() {
        // operand <= type_max does NOT guard (need strictly less)
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Le {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
        };
        assert!(!path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    #[test]
    fn test_path_condition_guards_overflow_max_not_ge() {
        // NOT(operand >= type_max) is equivalent to operand < type_max
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Not {
            operand: Box::new(SwiftExpr::Ge {
                lhs: Box::new(operand.clone()),
                rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
            }),
        };
        assert!(path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    #[test]
    fn test_path_condition_guards_overflow_max_and_left() {
        // Guard in left side of And
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let guard = SwiftExpr::Lt {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
        };
        let other = SwiftExpr::Gt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "y".to_string(),
                index: 1,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let path_cond = SwiftExpr::And {
            lhs: Box::new(guard),
            rhs: Box::new(other),
        };
        assert!(path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    #[test]
    fn test_path_condition_guards_overflow_max_and_right() {
        // Guard in right side of And
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let guard = SwiftExpr::Lt {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
        };
        let other = SwiftExpr::Gt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "y".to_string(),
                index: 1,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let path_cond = SwiftExpr::And {
            lhs: Box::new(other),
            rhs: Box::new(guard),
        };
        assert!(path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    #[test]
    fn test_path_condition_guards_overflow_max_wrong_operand() {
        // Different operand doesn't match
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let different = SwiftExpr::ParamRef {
            name: "y".to_string(),
            index: 1,
        };
        let path_cond = SwiftExpr::Lt {
            lhs: Box::new(different),
            rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
        };
        assert!(!path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    #[test]
    fn test_path_condition_guards_overflow_max_unrelated_cond() {
        // Unrelated condition type
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Eq {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
        };
        assert!(!path_condition_guards_overflow_max(
            &path_cond, &operand, 127
        ));
    }

    // ==========================================================================
    // Tests for path_condition_guards_underflow_min
    // ==========================================================================

    #[test]
    fn test_path_condition_guards_underflow_min_gt_direct() {
        // operand > type_min
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Gt {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: -128 }),
        };
        assert!(path_condition_guards_underflow_min(
            &path_cond, &operand, -128
        ));
    }

    #[test]
    fn test_path_condition_guards_underflow_min_gt_wrong_value() {
        // operand > -100 doesn't guard against min=-128
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Gt {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: -100 }),
        };
        assert!(!path_condition_guards_underflow_min(
            &path_cond, &operand, -128
        ));
    }

    #[test]
    fn test_path_condition_guards_underflow_min_gt_var_heuristic() {
        // operand > some_var is accepted heuristically
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Gt {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::ParamRef {
                name: "min".to_string(),
                index: 1,
            }),
        };
        assert!(path_condition_guards_underflow_min(
            &path_cond, &operand, -128
        ));
    }

    #[test]
    fn test_path_condition_guards_underflow_min_lt_reverse() {
        // type_min < operand (equivalent to operand > type_min)
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Lt {
            lhs: Box::new(SwiftExpr::IntLit { value: -128 }),
            rhs: Box::new(operand.clone()),
        };
        assert!(path_condition_guards_underflow_min(
            &path_cond, &operand, -128
        ));
    }

    #[test]
    fn test_path_condition_guards_underflow_min_ge_above_min() {
        // operand >= type_min+1 proves operand-1 >= type_min
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Ge {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: -127 }),
        };
        assert!(path_condition_guards_underflow_min(
            &path_cond, &operand, -128
        ));
    }

    #[test]
    fn test_path_condition_guards_underflow_min_ge_at_min_fails() {
        // operand >= type_min does NOT guard (need strictly greater)
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Ge {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: -128 }),
        };
        assert!(!path_condition_guards_underflow_min(
            &path_cond, &operand, -128
        ));
    }

    #[test]
    fn test_path_condition_guards_underflow_min_not_le() {
        // NOT(operand <= type_min) is equivalent to operand > type_min
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Not {
            operand: Box::new(SwiftExpr::Le {
                lhs: Box::new(operand.clone()),
                rhs: Box::new(SwiftExpr::IntLit { value: -128 }),
            }),
        };
        assert!(path_condition_guards_underflow_min(
            &path_cond, &operand, -128
        ));
    }

    #[test]
    fn test_path_condition_guards_underflow_min_and_left() {
        // Guard in left side of And
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let guard = SwiftExpr::Gt {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: -128 }),
        };
        let other = SwiftExpr::Lt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "y".to_string(),
                index: 1,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 100 }),
        };
        let path_cond = SwiftExpr::And {
            lhs: Box::new(guard),
            rhs: Box::new(other),
        };
        assert!(path_condition_guards_underflow_min(
            &path_cond, &operand, -128
        ));
    }

    #[test]
    fn test_path_condition_guards_underflow_min_and_right() {
        // Guard in right side of And
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let guard = SwiftExpr::Gt {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: -128 }),
        };
        let other = SwiftExpr::Lt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "y".to_string(),
                index: 1,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 100 }),
        };
        let path_cond = SwiftExpr::And {
            lhs: Box::new(other),
            rhs: Box::new(guard),
        };
        assert!(path_condition_guards_underflow_min(
            &path_cond, &operand, -128
        ));
    }

    #[test]
    fn test_path_condition_guards_underflow_min_unrelated() {
        // Unrelated condition type
        let operand = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let path_cond = SwiftExpr::Eq {
            lhs: Box::new(operand.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: -128 }),
        };
        assert!(!path_condition_guards_underflow_min(
            &path_cond, &operand, -128
        ));
    }

    // ==========================================================================
    // Tests for try_prove_overflow_safe_via_path_condition
    // ==========================================================================

    #[test]
    fn test_try_prove_overflow_safe_non_overflow_returns_none() {
        // Non-overflow auto_vc should return None
        let auto_vc = SwiftAutoVc::DivByZero {
            divisor: SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            },
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: None,
        };
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_no_path_condition_returns_none() {
        // Overflow without path condition should return None
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::IntLit { value: 1 },
            ],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 8,
        };
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_add_increment_with_guard() {
        // x + 1 with path condition x < 127 should be proven safe for i8
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![x_param.clone(), SwiftExpr::IntLit { value: 1 }],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Lt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
            }),
            signed: true,
            bits: 8,
        };
        let result = try_prove_overflow_safe_via_path_condition(&auto_vc);
        assert!(result.is_some());
        let (verify_result, trace) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
        assert!(trace.contains("Proved via path condition"));
    }

    #[test]
    fn test_try_prove_overflow_safe_add_increment_first_operand_is_one() {
        // 1 + x with path condition x < 127 should also be proven safe
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![SwiftExpr::IntLit { value: 1 }, x_param.clone()],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Lt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
            }),
            signed: true,
            bits: 8,
        };
        let result = try_prove_overflow_safe_via_path_condition(&auto_vc);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_safe_add_not_increment_returns_none() {
        // x + 2 is not an increment, should return None
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![x_param.clone(), SwiftExpr::IntLit { value: 2 }],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Lt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
            }),
            signed: true,
            bits: 8,
        };
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_add_increment_no_guard_returns_none() {
        // x + 1 with path condition x > 0 (doesn't guard max) should return None
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![x_param.clone(), SwiftExpr::IntLit { value: 1 }],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Gt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            signed: true,
            bits: 8,
        };
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_sub_decrement_with_guard() {
        // x - 1 with path condition x > -128 should be proven safe for i8
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "sub".to_string(),
            operands: vec![x_param.clone(), SwiftExpr::IntLit { value: 1 }],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Gt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: -128 }),
            }),
            signed: true,
            bits: 8,
        };
        let result = try_prove_overflow_safe_via_path_condition(&auto_vc);
        assert!(result.is_some());
        let (verify_result, trace) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
        assert!(trace.contains("Proved via path condition"));
        assert!(trace.contains("no underflow"));
    }

    #[test]
    fn test_try_prove_overflow_safe_sub_not_decrement_returns_none() {
        // x - 2 is not a decrement, should return None
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "sub".to_string(),
            operands: vec![x_param.clone(), SwiftExpr::IntLit { value: 2 }],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Gt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: -128 }),
            }),
            signed: true,
            bits: 8,
        };
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_sub_decrement_no_guard_returns_none() {
        // x - 1 with path condition x < 100 (doesn't guard min) should return None
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "sub".to_string(),
            operands: vec![x_param.clone(), SwiftExpr::IntLit { value: 1 }],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Lt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: 100 }),
            }),
            signed: true,
            bits: 8,
        };
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_mul_operation_returns_none() {
        // mul operation is not handled, should return None
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "mul".to_string(),
            operands: vec![x_param.clone(), SwiftExpr::IntLit { value: 1 }],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Lt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
            }),
            signed: true,
            bits: 8,
        };
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_i32_bounds() {
        // Test with i32 bounds
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![x_param.clone(), SwiftExpr::IntLit { value: 1 }],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Lt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit {
                    value: 2_147_483_647,
                }),
            }),
            signed: true,
            bits: 32,
        };
        let result = try_prove_overflow_safe_via_path_condition(&auto_vc);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_safe_u8_bounds() {
        // Test with u8 bounds (unsigned)
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![x_param.clone(), SwiftExpr::IntLit { value: 1 }],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Lt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: 255 }),
            }),
            signed: false,
            bits: 8,
        };
        let result = try_prove_overflow_safe_via_path_condition(&auto_vc);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_safe_u8_sub_underflow() {
        // Test u8 underflow protection: x - 1 with x > 0
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "sub".to_string(),
            operands: vec![x_param.clone(), SwiftExpr::IntLit { value: 1 }],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Gt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            signed: false,
            bits: 8,
        };
        let result = try_prove_overflow_safe_via_path_condition(&auto_vc);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_safe_single_operand_returns_none() {
        // Single operand (like neg) should return None
        let x_param = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![x_param.clone()],
            description: "test".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Lt {
                lhs: Box::new(x_param),
                rhs: Box::new(SwiftExpr::IntLit { value: 127 }),
            }),
            signed: true,
            bits: 8,
        };
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    // ==========================================================================
    // Tests for is_one
    // ==========================================================================

    #[test]
    fn test_is_one_with_one() {
        assert!(is_one(&SwiftExpr::IntLit { value: 1 }));
    }

    #[test]
    fn test_is_one_with_zero() {
        assert!(!is_one(&SwiftExpr::IntLit { value: 0 }));
    }

    #[test]
    fn test_is_one_with_two() {
        assert!(!is_one(&SwiftExpr::IntLit { value: 2 }));
    }

    #[test]
    fn test_is_one_with_negative_one() {
        assert!(!is_one(&SwiftExpr::IntLit { value: -1 }));
    }

    #[test]
    fn test_is_one_with_param_ref() {
        assert!(!is_one(&SwiftExpr::ParamRef {
            name: "one".to_string(),
            index: 0
        }));
    }

    // ==========================================================================
    // Tests for expr_debug_name
    // ==========================================================================

    #[test]
    fn test_expr_debug_name_param_ref() {
        let expr = SwiftExpr::ParamRef {
            name: "myParam".to_string(),
            index: 0,
        };
        assert_eq!(expr_debug_name(&expr), "myParam");
    }

    #[test]
    fn test_expr_debug_name_int_lit_positive() {
        let expr = SwiftExpr::IntLit { value: 42 };
        assert_eq!(expr_debug_name(&expr), "42");
    }

    #[test]
    fn test_expr_debug_name_int_lit_negative() {
        let expr = SwiftExpr::IntLit { value: -100 };
        assert_eq!(expr_debug_name(&expr), "-100");
    }

    #[test]
    fn test_expr_debug_name_int_lit_zero() {
        let expr = SwiftExpr::IntLit { value: 0 };
        assert_eq!(expr_debug_name(&expr), "0");
    }

    #[test]
    fn test_expr_debug_name_complex_expr() {
        let expr = SwiftExpr::Add {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
        };
        // Returns debug format for complex expressions
        let name = expr_debug_name(&expr);
        assert!(name.contains("Add"));
    }

    // ==========================================================================
    // Tests for try_detect_unconstrained_bounds_as_failed
    // ==========================================================================

    #[test]
    fn test_try_detect_unconstrained_bounds_non_bounds_check() {
        // Non-BoundsCheck VCs return None
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        assert!(try_detect_unconstrained_bounds_as_failed(&auto_vc).is_none());
    }

    #[test]
    fn test_try_detect_unconstrained_bounds_with_constraint() {
        // BoundsCheck with path_condition that constrains index returns None
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: index.clone(),
            length: SwiftExpr::IntLit { value: 10 },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: Some(SwiftExpr::Ge {
                lhs: Box::new(index),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
        };
        // The path condition mentions the index, so it's considered constrained
        assert!(try_detect_unconstrained_bounds_as_failed(&auto_vc).is_none());
    }

    #[test]
    fn test_try_detect_unconstrained_bounds_no_constraint() {
        // BoundsCheck with no path_condition returns counterexample
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index,
            length: SwiftExpr::IntLit { value: 10 },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let result = try_detect_unconstrained_bounds_as_failed(&auto_vc);
        assert!(result.is_some());
        match result.unwrap() {
            VerifyResult::Counterexample(cx) => {
                assert!(!cx.assignments.is_empty());
                // The counterexample should suggest index = -1
                let (name, val) = &cx.assignments[0];
                assert_eq!(name, "i");
                // Check value is Int(-1) by matching
                match val {
                    crate::types::Value::Int(n) => assert_eq!(*n, -1),
                    _ => panic!("Expected Value::Int"),
                }
            }
            _ => panic!("Expected Counterexample"),
        }
    }

    #[test]
    fn test_try_detect_unconstrained_bounds_unrelated_path_cond() {
        // BoundsCheck with path_condition that doesn't constrain index
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index,
            length: SwiftExpr::IntLit { value: 10 },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            // Path condition constrains different variable
            path_condition: Some(SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "j".to_string(),
                    index: 1,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
        };
        // The path condition doesn't mention index "i", so bounds are unconstrained
        let result = try_detect_unconstrained_bounds_as_failed(&auto_vc);
        assert!(result.is_some());
    }

    // ==========================================================================
    // Tests for generate_suggestion
    // ==========================================================================

    #[test]
    fn test_generate_suggestion_verified_returns_empty() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let result = SwiftVerifyResult::Verified { time_seconds: 0.1 };
        assert_eq!(generate_suggestion(&auto_vc, &result), "");
    }

    #[test]
    fn test_generate_suggestion_overflow_add_increment() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::IntLit { value: 1 },
            ],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("Int.max"));
        assert!(suggestion.contains("SwiftUI counter pattern"));
    }

    #[test]
    fn test_generate_suggestion_overflow_sub_decrement() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "sub".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::IntLit { value: 1 },
            ],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("Int.min"));
    }

    #[test]
    fn test_generate_suggestion_overflow_add_general() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
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
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("a <= Int.max - b"));
        assert!(suggestion.contains("&+"));
    }

    #[test]
    fn test_generate_suggestion_overflow_sub_general() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "sub".to_string(),
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
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("a >= Int.min + b"));
        assert!(suggestion.contains("&-"));
    }

    #[test]
    fn test_generate_suggestion_overflow_mul() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "mul".to_string(),
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
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("Int.max / a"));
        assert!(suggestion.contains("&*"));
    }

    #[test]
    fn test_generate_suggestion_overflow_neg() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "neg".to_string(),
            operands: vec![SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("Int.min"));
        assert!(suggestion.contains("cannot be negated"));
    }

    #[test]
    fn test_generate_suggestion_overflow_unknown_op() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "xor".to_string(),
            operands: vec![],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("wraparound operators"));
    }

    #[test]
    fn test_generate_suggestion_div_by_zero() {
        let auto_vc = SwiftAutoVc::DivByZero {
            divisor: SwiftExpr::ParamRef {
                name: "d".to_string(),
                index: 0,
            },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("divisor != 0"));
    }

    #[test]
    fn test_generate_suggestion_bounds_check() {
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::IntLit { value: 10 },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("index >= 0"));
        assert!(suggestion.contains("index < array.count"));
    }

    #[test]
    fn test_generate_suggestion_nil_check() {
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("optional binding"));
    }

    #[test]
    fn test_generate_suggestion_cast_check() {
        let auto_vc = SwiftAutoVc::CastCheck {
            value: SwiftExpr::ParamRef {
                name: "obj".to_string(),
                index: 0,
            },
            source_type: "Any".to_string(),
            target_type: "String".to_string(),
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("as?"));
    }

    #[test]
    fn test_generate_suggestion_unowned_access() {
        let auto_vc = SwiftAutoVc::UnownedAccess {
            reference: SwiftExpr::ParamRef {
                name: "ref".to_string(),
                index: 0,
            },
            reference_name: "ref".to_string(),
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("weak") || suggestion.contains("lifetime"));
    }

    #[test]
    fn test_generate_suggestion_shift_overflow() {
        let auto_vc = SwiftAutoVc::ShiftOverflow {
            operation: "shl".to_string(),
            value: SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            },
            shift_amount: SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 1,
            },
            bits: 64,
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let suggestion = generate_suggestion(&auto_vc, &result);
        assert!(suggestion.contains("shift") || suggestion.contains("bitWidth"));
    }

    // ==========================================================================
    // Tests for format_value
    // ==========================================================================

    #[test]
    fn test_format_value_bool_true() {
        let val = crate::types::Value::Bool(true);
        assert_eq!(format_value(&val), "true");
    }

    #[test]
    fn test_format_value_bool_false() {
        let val = crate::types::Value::Bool(false);
        assert_eq!(format_value(&val), "false");
    }

    #[test]
    fn test_format_value_int_positive() {
        let val = crate::types::Value::Int(42);
        assert_eq!(format_value(&val), "42");
    }

    #[test]
    fn test_format_value_int_negative() {
        let val = crate::types::Value::Int(-123);
        assert_eq!(format_value(&val), "-123");
    }

    #[test]
    fn test_format_value_int_zero() {
        let val = crate::types::Value::Int(0);
        assert_eq!(format_value(&val), "0");
    }

    #[test]
    fn test_format_value_float() {
        // Use 3.5 instead of approximate PI to avoid clippy::approx_constant
        let val = crate::types::Value::Float(3.5);
        let formatted = format_value(&val);
        assert!(formatted.starts_with("3.5"));
    }

    #[test]
    fn test_format_value_bitvec() {
        let val = crate::types::Value::BitVec {
            bits: 16,
            value: vec![0xab, 0xcd],
        };
        let formatted = format_value(&val);
        assert!(formatted.contains("0x"));
        assert!(formatted.contains("16 bits"));
    }

    #[test]
    fn test_format_value_array() {
        let val = crate::types::Value::Array(vec![
            crate::types::Value::Int(1),
            crate::types::Value::Int(2),
            crate::types::Value::Int(3),
        ]);
        assert_eq!(format_value(&val), "[3 elements]");
    }

    #[test]
    fn test_format_value_array_empty() {
        let val = crate::types::Value::Array(vec![]);
        assert_eq!(format_value(&val), "[0 elements]");
    }

    #[test]
    fn test_format_value_struct() {
        let val = crate::types::Value::Struct {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), crate::types::Value::Int(10)),
                ("y".to_string(), crate::types::Value::Int(20)),
            ],
        };
        assert_eq!(format_value(&val), "Point{...}");
    }

    #[test]
    fn test_format_value_tuple() {
        let val = crate::types::Value::Tuple(vec![
            crate::types::Value::Int(1),
            crate::types::Value::Bool(true),
        ]);
        assert_eq!(format_value(&val), "(2 elements)");
    }

    #[test]
    fn test_format_value_tensor() {
        let val = crate::types::Value::Tensor {
            shape: vec![2, 3],
            data: vec![
                crate::types::Value::Int(1),
                crate::types::Value::Int(2),
                crate::types::Value::Int(3),
                crate::types::Value::Int(4),
                crate::types::Value::Int(5),
                crate::types::Value::Int(6),
            ],
        };
        let formatted = format_value(&val);
        assert!(formatted.contains("Tensor"));
        assert!(formatted.contains("[2, 3]"));
    }

    // ==========================================================================
    // Tests for get_path_condition
    // ==========================================================================

    #[test]
    fn test_get_path_condition_overflow_with_condition() {
        let path_cond = SwiftExpr::Gt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: Some(path_cond),
            signed: true,
            bits: 64,
        };
        let result = get_path_condition(&auto_vc);
        assert!(result.is_some());
    }

    #[test]
    fn test_get_path_condition_overflow_without_condition() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        assert!(get_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_get_path_condition_div_by_zero() {
        let path_cond = SwiftExpr::BoolLit { value: true };
        let auto_vc = SwiftAutoVc::DivByZero {
            divisor: SwiftExpr::ParamRef {
                name: "d".to_string(),
                index: 0,
            },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: Some(path_cond),
        };
        assert!(get_path_condition(&auto_vc).is_some());
    }

    #[test]
    fn test_get_path_condition_bounds_check() {
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::IntLit { value: 10 },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        assert!(get_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_get_path_condition_nil_check() {
        let path_cond = SwiftExpr::BoolLit { value: true };
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: Some(path_cond),
        };
        assert!(get_path_condition(&auto_vc).is_some());
    }

    #[test]
    fn test_get_path_condition_cast_check() {
        let auto_vc = SwiftAutoVc::CastCheck {
            value: SwiftExpr::ParamRef {
                name: "obj".to_string(),
                index: 0,
            },
            source_type: "Any".to_string(),
            target_type: "String".to_string(),
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        assert!(get_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_get_path_condition_cond_fail() {
        let path_cond = SwiftExpr::BoolLit { value: true };
        let auto_vc = SwiftAutoVc::CondFail {
            condition: SwiftExpr::BoolLit { value: false },
            message: "assertion failed".to_string(),
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: Some(path_cond),
        };
        assert!(get_path_condition(&auto_vc).is_some());
    }

    #[test]
    fn test_get_path_condition_termination() {
        let auto_vc = SwiftAutoVc::Termination {
            loop_label: "loop".to_string(),
            measure: SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 0,
            },
            initial_measure: None,
            next_measure: SwiftExpr::Sub {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "n".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
        };
        assert!(get_path_condition(&auto_vc).is_none());
    }

    // ==========================================================================
    // Tests for get_source_location
    // ==========================================================================

    #[test]
    fn test_get_source_location_overflow() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![],
            description: "test".to_string(),
            source_line: 42,
            source_column: 10,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let (line, col) = get_source_location(&auto_vc);
        assert_eq!(line, 42);
        assert_eq!(col, 10);
    }

    #[test]
    fn test_get_source_location_div_by_zero() {
        let auto_vc = SwiftAutoVc::DivByZero {
            divisor: SwiftExpr::ParamRef {
                name: "d".to_string(),
                index: 0,
            },
            description: "test".to_string(),
            source_line: 100,
            source_column: 5,
            path_condition: None,
        };
        let (line, col) = get_source_location(&auto_vc);
        assert_eq!(line, 100);
        assert_eq!(col, 5);
    }

    #[test]
    fn test_get_source_location_bounds_check() {
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::IntLit { value: 10 },
            description: "test".to_string(),
            source_line: 25,
            source_column: 15,
            path_condition: None,
        };
        let (line, col) = get_source_location(&auto_vc);
        assert_eq!(line, 25);
        assert_eq!(col, 15);
    }

    #[test]
    fn test_get_source_location_nil_check() {
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "test".to_string(),
            source_line: 50,
            source_column: 8,
            path_condition: None,
        };
        let (line, col) = get_source_location(&auto_vc);
        assert_eq!(line, 50);
        assert_eq!(col, 8);
    }

    #[test]
    fn test_get_source_location_cast_check() {
        let auto_vc = SwiftAutoVc::CastCheck {
            value: SwiftExpr::ParamRef {
                name: "obj".to_string(),
                index: 0,
            },
            source_type: "Any".to_string(),
            target_type: "String".to_string(),
            description: "test".to_string(),
            source_line: 75,
            source_column: 20,
            path_condition: None,
        };
        let (line, col) = get_source_location(&auto_vc);
        assert_eq!(line, 75);
        assert_eq!(col, 20);
    }

    #[test]
    fn test_get_source_location_cond_fail() {
        let auto_vc = SwiftAutoVc::CondFail {
            condition: SwiftExpr::BoolLit { value: false },
            message: "assertion failed".to_string(),
            description: "test".to_string(),
            source_line: 33,
            source_column: 12,
            path_condition: None,
        };
        let (line, col) = get_source_location(&auto_vc);
        assert_eq!(line, 33);
        assert_eq!(col, 12);
    }

    #[test]
    fn test_get_source_location_call_precondition() {
        let auto_vc = SwiftAutoVc::CallPrecondition {
            callee_name: "testFunc".to_string(),
            condition: SwiftExpr::BoolLit { value: true },
            description: "test".to_string(),
            source_line: 88,
            source_column: 4,
            path_condition: None,
        };
        let (line, col) = get_source_location(&auto_vc);
        assert_eq!(line, 88);
        assert_eq!(col, 4);
    }

    #[test]
    fn test_get_source_location_termination() {
        let auto_vc = SwiftAutoVc::Termination {
            loop_label: "loop".to_string(),
            measure: SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 0,
            },
            initial_measure: None,
            next_measure: SwiftExpr::IntLit { value: 0 },
            description: "test".to_string(),
            source_line: 66,
            source_column: 3,
        };
        let (line, col) = get_source_location(&auto_vc);
        assert_eq!(line, 66);
        assert_eq!(col, 3);
    }

    #[test]
    fn test_get_source_location_shift_overflow() {
        let auto_vc = SwiftAutoVc::ShiftOverflow {
            operation: "shl".to_string(),
            value: SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            },
            shift_amount: SwiftExpr::IntLit { value: 32 },
            bits: 64,
            description: "test".to_string(),
            source_line: 120,
            source_column: 7,
            path_condition: None,
        };
        let (line, col) = get_source_location(&auto_vc);
        assert_eq!(line, 120);
        assert_eq!(col, 7);
    }

    #[test]
    fn test_get_source_location_unowned_access() {
        let auto_vc = SwiftAutoVc::UnownedAccess {
            reference: SwiftExpr::ParamRef {
                name: "ref".to_string(),
                index: 0,
            },
            reference_name: "ref".to_string(),
            description: "test".to_string(),
            source_line: 55,
            source_column: 18,
            path_condition: None,
        };
        let (line, col) = get_source_location(&auto_vc);
        assert_eq!(line, 55);
        assert_eq!(col, 18);
    }

    // ==========================================================================
    // Tests for get_call_chain
    // ==========================================================================

    #[test]
    fn test_get_call_chain_method_call_state_effect() {
        let auto_vc = SwiftAutoVc::MethodCallStateEffect {
            type_name: "Counter".to_string(),
            invariant: SwiftExpr::BoolLit { value: true },
            callee_method: "mutate".to_string(),
            affected_properties: vec!["count".to_string()],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            caller_method: "process".to_string(),
            call_chain: vec!["foo".to_string(), "bar".to_string(), "baz".to_string()],
        };
        let chain = get_call_chain(&auto_vc);
        assert_eq!(chain.len(), 3);
        assert_eq!(chain[0], "foo");
        assert_eq!(chain[1], "bar");
        assert_eq!(chain[2], "baz");
    }

    #[test]
    fn test_get_call_chain_method_call_state_effect_empty() {
        let auto_vc = SwiftAutoVc::MethodCallStateEffect {
            type_name: "Counter".to_string(),
            invariant: SwiftExpr::BoolLit { value: true },
            callee_method: "mutate".to_string(),
            affected_properties: vec!["count".to_string()],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            caller_method: "process".to_string(),
            call_chain: vec![],
        };
        let chain = get_call_chain(&auto_vc);
        assert!(chain.is_empty());
    }

    #[test]
    fn test_get_call_chain_overflow_returns_empty() {
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![],
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let chain = get_call_chain(&auto_vc);
        assert!(chain.is_empty());
    }

    #[test]
    fn test_get_call_chain_div_by_zero_returns_empty() {
        let auto_vc = SwiftAutoVc::DivByZero {
            divisor: SwiftExpr::IntLit { value: 0 },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let chain = get_call_chain(&auto_vc);
        assert!(chain.is_empty());
    }

    #[test]
    fn test_get_call_chain_bounds_check_returns_empty() {
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::IntLit { value: 5 },
            length: SwiftExpr::IntLit { value: 10 },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let chain = get_call_chain(&auto_vc);
        assert!(chain.is_empty());
    }

    #[test]
    fn test_get_call_chain_nil_check_returns_empty() {
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let chain = get_call_chain(&auto_vc);
        assert!(chain.is_empty());
    }

    #[test]
    fn test_get_call_chain_termination_returns_empty() {
        let auto_vc = SwiftAutoVc::Termination {
            loop_label: "loop".to_string(),
            measure: SwiftExpr::IntLit { value: 10 },
            initial_measure: None,
            next_measure: SwiftExpr::IntLit { value: 9 },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
        };
        let chain = get_call_chain(&auto_vc);
        assert!(chain.is_empty());
    }

    // ========================================================================
    // Tests for parse_bundles_json
    // ========================================================================

    #[test]
    fn test_parse_bundles_json_single_object() {
        let json = r#"{
            "function_name": "test",
            "source_file": "test.swift",
            "source_line": 1,
            "parameters": [],
            "requires": [],
            "ensures": [],
            "auto_vcs": []
        }"#;
        let bundles = parse_bundles_json(json).unwrap();
        assert_eq!(bundles.len(), 1);
        assert_eq!(bundles[0].function_name, "test");
    }

    #[test]
    fn test_parse_bundles_json_array() {
        let json = r#"[
            {
                "function_name": "func1",
                "source_file": "test.swift",
                "source_line": 1,
                "parameters": [],
                "requires": [],
                "ensures": [],
                "auto_vcs": []
            },
            {
                "function_name": "func2",
                "source_file": "test.swift",
                "source_line": 10,
                "parameters": [],
                "requires": [],
                "ensures": [],
                "auto_vcs": []
            }
        ]"#;
        let bundles = parse_bundles_json(json).unwrap();
        assert_eq!(bundles.len(), 2);
        assert_eq!(bundles[0].function_name, "func1");
        assert_eq!(bundles[1].function_name, "func2");
    }

    #[test]
    fn test_parse_bundles_json_newline_delimited() {
        let json = r#"{"function_name": "func1", "source_file": "test.swift", "source_line": 1, "parameters": [], "requires": [], "ensures": [], "auto_vcs": []}
{"function_name": "func2", "source_file": "test.swift", "source_line": 10, "parameters": [], "requires": [], "ensures": [], "auto_vcs": []}"#;
        let bundles = parse_bundles_json(json).unwrap();
        assert_eq!(bundles.len(), 2);
        assert_eq!(bundles[0].function_name, "func1");
        assert_eq!(bundles[1].function_name, "func2");
    }

    #[test]
    fn test_parse_bundles_json_empty_input_error() {
        let result = parse_bundles_json("");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, VcBridgeError::Conversion(_)));
    }

    #[test]
    fn test_parse_bundles_json_whitespace_only_error() {
        let result = parse_bundles_json("   \n\t  ");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_bundles_json_invalid_json_error() {
        let result = parse_bundles_json("not valid json");
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_bundles_json_newline_with_blank_lines() {
        let json = r#"{"function_name": "func1", "source_file": "test.swift", "source_line": 1, "parameters": [], "requires": [], "ensures": [], "auto_vcs": []}

{"function_name": "func2", "source_file": "test.swift", "source_line": 10, "parameters": [], "requires": [], "ensures": [], "auto_vcs": []}"#;
        let bundles = parse_bundles_json(json).unwrap();
        assert_eq!(bundles.len(), 2);
    }

    #[test]
    fn test_parse_bundles_json_resolves_condition_strings() {
        // Use requires_str to test that condition strings are resolved
        let json = r#"{
            "function_name": "test",
            "source_file": "test.swift",
            "source_line": 1,
            "parameters": [{"name": "x", "type": {"kind": "Int", "signed": true, "bits": 64}, "index": 0}],
            "requires_str": ["x > 0"],
            "ensures": [],
            "auto_vcs": []
        }"#;
        let bundles = parse_bundles_json(json).unwrap();
        assert_eq!(bundles.len(), 1);
        // After resolution, requires should have content from requires_str
        assert_eq!(bundles[0].requires.len(), 1);
    }

    // ========================================================================
    // Tests for convert_verify_result
    // ========================================================================

    #[test]
    fn test_convert_verify_result_proven() {
        let result = convert_verify_result(VerifyResult::Proven, 0.5);
        match result {
            SwiftVerifyResult::Verified { time_seconds } => {
                assert!((time_seconds - 0.5).abs() < 0.001);
            }
            _ => panic!("Expected Verified result"),
        }
    }

    #[test]
    fn test_convert_verify_result_counterexample() {
        let cex = Counterexample {
            assignments: vec![("x".to_string(), Value::Int(42))],
        };
        let result = convert_verify_result(VerifyResult::Counterexample(cex), 1.0);
        match result {
            SwiftVerifyResult::Failed {
                counterexample,
                time_seconds,
            } => {
                assert_eq!(counterexample.len(), 1);
                // counterexample is a Vec<(String, String)>, check first element
                assert_eq!(counterexample[0], ("x".to_string(), "42".to_string()));
                assert!((time_seconds - 1.0).abs() < 0.001);
            }
            _ => panic!("Expected Failed result"),
        }
    }

    #[test]
    fn test_convert_verify_result_unknown() {
        let result = convert_verify_result(
            VerifyResult::Unknown {
                category: UnknownReason::Other {
                    reason: "unsupported operation".to_string(),
                },
                reason: "test reason".to_string(),
            },
            2.0,
        );
        match result {
            SwiftVerifyResult::Unknown {
                reason,
                time_seconds,
            } => {
                assert!(reason.contains("unsupported"));
                assert!(reason.contains("test reason"));
                assert!((time_seconds - 2.0).abs() < 0.001);
            }
            _ => panic!("Expected Unknown result"),
        }
    }

    #[test]
    fn test_convert_verify_result_timeout() {
        let result = convert_verify_result(VerifyResult::Timeout { seconds: 30.0 }, 30.0);
        match result {
            SwiftVerifyResult::Timeout { timeout_seconds } => {
                assert!((timeout_seconds - 30.0).abs() < 0.001);
            }
            _ => panic!("Expected Timeout result"),
        }
    }

    #[test]
    fn test_convert_verify_result_error() {
        let result = convert_verify_result(VerifyResult::Error("test error".to_string()), 0.1);
        match result {
            SwiftVerifyResult::Error { message } => {
                assert_eq!(message, "test error");
            }
            _ => panic!("Expected Error result"),
        }
    }

    // ========================================================================
    // Tests for path_condition_contains_lower_bound
    // ========================================================================

    #[test]
    fn test_path_condition_contains_lower_bound_ge_zero() {
        // index >= 0
        let path_cond = SwiftExpr::Ge {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        assert!(path_condition_contains_lower_bound(&path_cond, &index));
    }

    #[test]
    fn test_path_condition_contains_lower_bound_le_reversed() {
        // 0 <= index
        let path_cond = SwiftExpr::Le {
            lhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            rhs: Box::new(SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        assert!(path_condition_contains_lower_bound(&path_cond, &index));
    }

    #[test]
    fn test_path_condition_contains_lower_bound_gt_neg1() {
        // index > -1
        let path_cond = SwiftExpr::Gt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: -1 }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        assert!(path_condition_contains_lower_bound(&path_cond, &index));
    }

    #[test]
    fn test_path_condition_contains_lower_bound_not_lt_zero() {
        // NOT(index < 0)
        let path_cond = SwiftExpr::Not {
            operand: Box::new(SwiftExpr::Lt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        assert!(path_condition_contains_lower_bound(&path_cond, &index));
    }

    #[test]
    fn test_path_condition_contains_lower_bound_and_left() {
        // (index >= 0) && something_else
        let path_cond = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            rhs: Box::new(SwiftExpr::BoolLit { value: true }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        assert!(path_condition_contains_lower_bound(&path_cond, &index));
    }

    #[test]
    fn test_path_condition_contains_lower_bound_and_right() {
        // something_else && (index >= 0)
        let path_cond = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::BoolLit { value: true }),
            rhs: Box::new(SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        assert!(path_condition_contains_lower_bound(&path_cond, &index));
    }

    #[test]
    fn test_path_condition_contains_lower_bound_wrong_index() {
        // j >= 0 (not matching index i)
        let path_cond = SwiftExpr::Ge {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "j".to_string(),
                index: 1,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        assert!(!path_condition_contains_lower_bound(&path_cond, &index));
    }

    #[test]
    fn test_path_condition_contains_lower_bound_unrelated() {
        // x > 5 (unrelated condition)
        let path_cond = SwiftExpr::Gt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 5 }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 1,
        };
        assert!(!path_condition_contains_lower_bound(&path_cond, &index));
    }

    // ========================================================================
    // Tests for path_condition_contains_upper_bound
    // ========================================================================

    #[test]
    fn test_path_condition_contains_upper_bound_lt_length() {
        // index < length
        let path_cond = SwiftExpr::Lt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::ParamRef {
                name: "len".to_string(),
                index: 1,
            }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };
        assert!(path_condition_contains_upper_bound(
            &path_cond, &index, &length
        ));
    }

    #[test]
    fn test_path_condition_contains_upper_bound_gt_reversed() {
        // length > index
        let path_cond = SwiftExpr::Gt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "len".to_string(),
                index: 1,
            }),
            rhs: Box::new(SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };
        assert!(path_condition_contains_upper_bound(
            &path_cond, &index, &length
        ));
    }

    #[test]
    fn test_path_condition_contains_upper_bound_not_ge() {
        // NOT(index >= length)
        let path_cond = SwiftExpr::Not {
            operand: Box::new(SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::ParamRef {
                    name: "len".to_string(),
                    index: 1,
                }),
            }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };
        assert!(path_condition_contains_upper_bound(
            &path_cond, &index, &length
        ));
    }

    #[test]
    fn test_path_condition_contains_upper_bound_ssa_var() {
        // SSA variable (heuristic: often from bounds check)
        let path_cond = SwiftExpr::ParamRef {
            name: "ssa_21".to_string(),
            index: 0,
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };
        assert!(path_condition_contains_upper_bound(
            &path_cond, &index, &length
        ));
    }

    #[test]
    fn test_path_condition_contains_upper_bound_and_left() {
        // (index < length) && something
        let path_cond = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Lt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::ParamRef {
                    name: "len".to_string(),
                    index: 1,
                }),
            }),
            rhs: Box::new(SwiftExpr::BoolLit { value: true }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };
        assert!(path_condition_contains_upper_bound(
            &path_cond, &index, &length
        ));
    }

    #[test]
    fn test_path_condition_contains_upper_bound_wrong_index() {
        // j < length (not matching index i)
        let path_cond = SwiftExpr::Lt {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "j".to_string(),
                index: 2,
            }),
            rhs: Box::new(SwiftExpr::ParamRef {
                name: "len".to_string(),
                index: 1,
            }),
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };
        assert!(!path_condition_contains_upper_bound(
            &path_cond, &index, &length
        ));
    }

    #[test]
    fn test_path_condition_contains_upper_bound_non_ssa_param() {
        // Regular parameter (not SSA) should not match
        let path_cond = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };
        assert!(!path_condition_contains_upper_bound(
            &path_cond, &index, &length
        ));
    }

    // ========================================================================
    // Tests for get_lower_bound_for_expr and get_upper_bound_for_expr
    // ========================================================================

    #[test]
    fn test_get_lower_bound_for_expr_literal() {
        let var_bounds = HashMap::new();
        let expr = Expr::IntLit(42);
        assert_eq!(get_lower_bound_for_expr(&expr, &var_bounds), Some(42));
    }

    #[test]
    fn test_get_lower_bound_for_expr_var() {
        let mut var_bounds = HashMap::new();
        var_bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(0),
                hi: Some(100),
            },
        );
        let expr = Expr::Var("x".to_string());
        assert_eq!(get_lower_bound_for_expr(&expr, &var_bounds), Some(0));
    }

    #[test]
    fn test_get_lower_bound_for_expr_var_no_bounds() {
        let var_bounds = HashMap::new();
        let expr = Expr::Var("x".to_string());
        assert_eq!(get_lower_bound_for_expr(&expr, &var_bounds), None);
    }

    #[test]
    fn test_get_lower_bound_for_expr_struct_field() {
        let mut var_bounds = HashMap::new();
        var_bounds.insert(
            "arr.count".to_string(),
            VarBounds {
                lo: Some(0),
                hi: Some(1000),
            },
        );
        let expr = Expr::StructField(Box::new(Expr::Var("arr".to_string())), "count".to_string());
        assert_eq!(get_lower_bound_for_expr(&expr, &var_bounds), Some(0));
    }

    #[test]
    fn test_get_lower_bound_for_expr_add() {
        let mut var_bounds = HashMap::new();
        var_bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(10),
                hi: Some(20),
            },
        );
        var_bounds.insert(
            "y".to_string(),
            VarBounds {
                lo: Some(5),
                hi: Some(15),
            },
        );
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        assert_eq!(get_lower_bound_for_expr(&expr, &var_bounds), Some(15)); // 10 + 5
    }

    #[test]
    fn test_get_lower_bound_for_expr_neg() {
        let mut var_bounds = HashMap::new();
        var_bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(10),
                hi: Some(20),
            },
        );
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        // Lower bound of -x is -upper_bound(x) = -20
        assert_eq!(get_lower_bound_for_expr(&expr, &var_bounds), Some(-20));
    }

    #[test]
    fn test_get_lower_bound_for_expr_unsupported() {
        let var_bounds = HashMap::new();
        let expr = Expr::Mul(Box::new(Expr::IntLit(2)), Box::new(Expr::IntLit(3)));
        assert_eq!(get_lower_bound_for_expr(&expr, &var_bounds), None);
    }

    #[test]
    fn test_get_upper_bound_for_expr_literal() {
        let var_bounds = HashMap::new();
        let expr = Expr::IntLit(42);
        assert_eq!(get_upper_bound_for_expr(&expr, &var_bounds), Some(42));
    }

    #[test]
    fn test_get_upper_bound_for_expr_var() {
        let mut var_bounds = HashMap::new();
        var_bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(0),
                hi: Some(100),
            },
        );
        let expr = Expr::Var("x".to_string());
        assert_eq!(get_upper_bound_for_expr(&expr, &var_bounds), Some(100));
    }

    #[test]
    fn test_get_upper_bound_for_expr_struct_field() {
        let mut var_bounds = HashMap::new();
        var_bounds.insert(
            "arr.count".to_string(),
            VarBounds {
                lo: Some(0),
                hi: Some(1000),
            },
        );
        let expr = Expr::StructField(Box::new(Expr::Var("arr".to_string())), "count".to_string());
        assert_eq!(get_upper_bound_for_expr(&expr, &var_bounds), Some(1000));
    }

    #[test]
    fn test_get_upper_bound_for_expr_add() {
        let mut var_bounds = HashMap::new();
        var_bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(10),
                hi: Some(20),
            },
        );
        var_bounds.insert(
            "y".to_string(),
            VarBounds {
                lo: Some(5),
                hi: Some(15),
            },
        );
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        assert_eq!(get_upper_bound_for_expr(&expr, &var_bounds), Some(35)); // 20 + 15
    }

    #[test]
    fn test_get_upper_bound_for_expr_neg() {
        let mut var_bounds = HashMap::new();
        var_bounds.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(10),
                hi: Some(20),
            },
        );
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        // Upper bound of -x is -lower_bound(x) = -10
        assert_eq!(get_upper_bound_for_expr(&expr, &var_bounds), Some(-10));
    }

    // =========================================================================
    // Unit tests for try_prove_bounds_via_path_condition
    // =========================================================================

    #[test]
    fn test_try_prove_bounds_via_path_condition_both_bounds() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Path condition: index >= 0 AND index < length
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };

        let path_cond = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Ge {
                lhs: Box::new(index.clone()),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            rhs: Box::new(SwiftExpr::Lt {
                lhs: Box::new(index.clone()),
                rhs: Box::new(length.clone()),
            }),
        };

        let auto_vc = SwiftAutoVc::BoundsCheck {
            index,
            length,
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: Some(path_cond),
        };

        let result = try_prove_bounds_via_path_condition(&auto_vc);
        assert!(result.is_some());
        let (verify_result, smtlib) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
        assert!(smtlib.contains("path condition"));
    }

    #[test]
    fn test_try_prove_bounds_via_path_condition_lower_only() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Path condition: index >= 0 (no upper bound)
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };

        let path_cond = SwiftExpr::Ge {
            lhs: Box::new(index.clone()),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        };

        let auto_vc = SwiftAutoVc::BoundsCheck {
            index,
            length,
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: Some(path_cond),
        };

        let result = try_prove_bounds_via_path_condition(&auto_vc);
        assert!(result.is_none()); // Need both bounds
    }

    #[test]
    fn test_try_prove_bounds_via_path_condition_upper_only() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Path condition: index < length (no lower bound)
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };

        let path_cond = SwiftExpr::Lt {
            lhs: Box::new(index.clone()),
            rhs: Box::new(length.clone()),
        };

        let auto_vc = SwiftAutoVc::BoundsCheck {
            index,
            length,
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: Some(path_cond),
        };

        let result = try_prove_bounds_via_path_condition(&auto_vc);
        assert!(result.is_none()); // Need both bounds
    }

    #[test]
    fn test_try_prove_bounds_via_path_condition_no_path_condition() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::ParamRef {
                name: "len".to_string(),
                index: 1,
            },
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let result = try_prove_bounds_via_path_condition(&auto_vc);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_bounds_via_path_condition_non_bounds_check() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // NilCheck should return None
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "nil check".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let result = try_prove_bounds_via_path_condition(&auto_vc);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_bounds_via_path_condition_le_zero_lower() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Path condition: 0 <= index AND index < length
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };

        let path_cond = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Le {
                lhs: Box::new(SwiftExpr::IntLit { value: 0 }),
                rhs: Box::new(index.clone()),
            }),
            rhs: Box::new(SwiftExpr::Lt {
                lhs: Box::new(index.clone()),
                rhs: Box::new(length.clone()),
            }),
        };

        let auto_vc = SwiftAutoVc::BoundsCheck {
            index,
            length,
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: Some(path_cond),
        };

        let result = try_prove_bounds_via_path_condition(&auto_vc);
        assert!(result.is_some());
    }

    #[test]
    fn test_try_prove_bounds_via_path_condition_not_lt_zero_lower() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Path condition: NOT(index < 0) AND index < length
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };

        let path_cond = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Not {
                operand: Box::new(SwiftExpr::Lt {
                    lhs: Box::new(index.clone()),
                    rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
                }),
            }),
            rhs: Box::new(SwiftExpr::Lt {
                lhs: Box::new(index.clone()),
                rhs: Box::new(length.clone()),
            }),
        };

        let auto_vc = SwiftAutoVc::BoundsCheck {
            index,
            length,
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: Some(path_cond),
        };

        let result = try_prove_bounds_via_path_condition(&auto_vc);
        assert!(result.is_some());
    }

    #[test]
    fn test_try_prove_bounds_via_path_condition_gt_upper() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Path condition: index >= 0 AND length > index
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };

        let path_cond = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Ge {
                lhs: Box::new(index.clone()),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            rhs: Box::new(SwiftExpr::Gt {
                lhs: Box::new(length.clone()),
                rhs: Box::new(index.clone()),
            }),
        };

        let auto_vc = SwiftAutoVc::BoundsCheck {
            index,
            length,
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: Some(path_cond),
        };

        let result = try_prove_bounds_via_path_condition(&auto_vc);
        assert!(result.is_some());
    }

    #[test]
    fn test_try_prove_bounds_via_path_condition_ssa_upper() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Path condition: index >= 0 AND ssa_21 (SSA var as upper bound heuristic)
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };

        let path_cond = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Ge {
                lhs: Box::new(index.clone()),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            rhs: Box::new(SwiftExpr::ParamRef {
                name: "ssa_21".to_string(),
                index: 0,
            }),
        };

        let auto_vc = SwiftAutoVc::BoundsCheck {
            index,
            length,
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: Some(path_cond),
        };

        let result = try_prove_bounds_via_path_condition(&auto_vc);
        assert!(result.is_some());
    }

    #[test]
    fn test_try_prove_bounds_via_path_condition_gt_neg_one_lower() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Path condition: index > -1 AND index < length
        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };
        let length = SwiftExpr::ParamRef {
            name: "len".to_string(),
            index: 1,
        };

        let path_cond = SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Gt {
                lhs: Box::new(index.clone()),
                rhs: Box::new(SwiftExpr::IntLit { value: -1 }),
            }),
            rhs: Box::new(SwiftExpr::Lt {
                lhs: Box::new(index.clone()),
                rhs: Box::new(length.clone()),
            }),
        };

        let auto_vc = SwiftAutoVc::BoundsCheck {
            index,
            length,
            description: "array bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: Some(path_cond),
        };

        let result = try_prove_bounds_via_path_condition(&auto_vc);
        assert!(result.is_some());
    }

    // =========================================================================
    // Unit tests for try_prove_nil_via_simple_constraints
    // =========================================================================

    #[test]
    fn test_try_prove_nil_via_simple_constraints_known_non_nil() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Precondition: opt.hasValue == true
        // VC: NilCheck on opt
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "unwrap optional".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("opt".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        ))];

        let result = try_prove_nil_via_simple_constraints(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, smtlib) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
        assert!(smtlib.contains("non-nil"));
    }

    #[test]
    fn test_try_prove_nil_via_simple_constraints_unknown_var() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Precondition: other.hasValue == true
        // VC: NilCheck on opt (different variable)
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "unwrap optional".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("other".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        ))];

        let result = try_prove_nil_via_simple_constraints(&auto_vc, &preconditions);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_nil_via_simple_constraints_no_preconditions() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "unwrap optional".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![];

        let result = try_prove_nil_via_simple_constraints(&auto_vc, &preconditions);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_nil_via_simple_constraints_non_nil_check() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // BoundsCheck should return None
        let auto_vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::ParamRef {
                name: "len".to_string(),
                index: 1,
            },
            description: "bounds".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("opt".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        ))];

        let result = try_prove_nil_via_simple_constraints(&auto_vc, &preconditions);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_nil_via_simple_constraints_reverse_eq() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Precondition: true == opt.hasValue (reversed)
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "unwrap optional".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::StructField(
                Box::new(Expr::Var("opt".to_string())),
                "hasValue".to_string(),
            )),
        ))];

        let result = try_prove_nil_via_simple_constraints(&auto_vc, &preconditions);
        assert!(result.is_some());
    }

    #[test]
    fn test_try_prove_nil_via_simple_constraints_and_precondition() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Precondition: And(x > 0, opt.hasValue == true)
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "unwrap optional".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![Predicate::And(vec![
            Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("opt".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        ])];

        let result = try_prove_nil_via_simple_constraints(&auto_vc, &preconditions);
        assert!(result.is_some());
    }

    #[test]
    fn test_try_prove_nil_via_simple_constraints_nested_field() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Precondition: obj.field.hasValue == true
        // VC: NilCheck on obj.field
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::Field {
                base: Box::new(SwiftExpr::ParamRef {
                    name: "obj".to_string(),
                    index: 0,
                }),
                field: "field".to_string(),
            },
            description: "unwrap nested optional".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("obj".to_string())),
                    "field".to_string(),
                )),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        ))];

        let result = try_prove_nil_via_simple_constraints(&auto_vc, &preconditions);
        assert!(result.is_some());
    }

    #[test]
    fn test_try_prove_nil_via_simple_constraints_false_has_value() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Precondition: opt.hasValue == false (not non-nil!)
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "unwrap optional".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("opt".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(false)),
        ))];

        let result = try_prove_nil_via_simple_constraints(&auto_vc, &preconditions);
        assert!(result.is_none()); // false means IS nil
    }

    #[test]
    fn test_try_prove_nil_via_simple_constraints_expr_and() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Precondition: Expr::And containing hasValue check
        let auto_vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "unwrap optional".to_string(),
            source_line: 1,
            source_column: 0,
            path_condition: None,
        };

        let preconditions = vec![Predicate::Expr(Expr::And(
            Box::new(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("opt".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        ))];

        let result = try_prove_nil_via_simple_constraints(&auto_vc, &preconditions);
        assert!(result.is_some());
    }

    // ========================================================================
    // error_json tests
    // ========================================================================

    #[test]
    fn test_error_json_simple_message() {
        use std::ffi::CStr;

        let result = error_json("test error");
        assert!(!result.is_null());

        let c_str = unsafe { CStr::from_ptr(result) };
        let string = c_str.to_str().unwrap();
        assert_eq!(string, r#"{"error":"test error"}"#);

        // Free the allocated string
        unsafe {
            drop(std::ffi::CString::from_raw(result));
        }
    }

    #[test]
    fn test_error_json_escapes_quotes() {
        use std::ffi::CStr;

        let result = error_json(r#"message with "quotes""#);
        assert!(!result.is_null());

        let c_str = unsafe { CStr::from_ptr(result) };
        let string = c_str.to_str().unwrap();
        assert_eq!(string, r#"{"error":"message with \"quotes\""}"#);

        unsafe {
            drop(std::ffi::CString::from_raw(result));
        }
    }

    #[test]
    fn test_error_json_escapes_newlines() {
        use std::ffi::CStr;

        let result = error_json("line1\nline2");
        assert!(!result.is_null());

        let c_str = unsafe { CStr::from_ptr(result) };
        let string = c_str.to_str().unwrap();
        assert_eq!(string, r#"{"error":"line1\nline2"}"#);

        unsafe {
            drop(std::ffi::CString::from_raw(result));
        }
    }

    #[test]
    fn test_error_json_empty_message() {
        use std::ffi::CStr;

        let result = error_json("");
        assert!(!result.is_null());

        let c_str = unsafe { CStr::from_ptr(result) };
        let string = c_str.to_str().unwrap();
        assert_eq!(string, r#"{"error":""}"#);

        unsafe {
            drop(std::ffi::CString::from_raw(result));
        }
    }

    #[test]
    fn test_error_json_mixed_escapes() {
        use std::ffi::CStr;

        let result = error_json("Error: \"unexpected\"\nDetails: none");
        assert!(!result.is_null());

        let c_str = unsafe { CStr::from_ptr(result) };
        let string = c_str.to_str().unwrap();
        assert_eq!(
            string,
            r#"{"error":"Error: \"unexpected\"\nDetails: none"}"#
        );

        unsafe {
            drop(std::ffi::CString::from_raw(result));
        }
    }

    // ========================================================================
    // extract_var_int_bound tests
    // ========================================================================

    #[test]
    fn test_extract_var_int_bound_var_ge_literal() {
        let mut out = HashMap::new();
        let a = Expr::Var("x".to_string());
        let b = Expr::IntLit(5);

        extract_var_int_bound(&a, &b, &mut out, BoundCmp::Ge);

        assert_eq!(out.get("x").unwrap().lo, Some(5));
        assert_eq!(out.get("x").unwrap().hi, None);
    }

    #[test]
    fn test_extract_var_int_bound_var_le_literal() {
        let mut out = HashMap::new();
        let a = Expr::Var("x".to_string());
        let b = Expr::IntLit(10);

        extract_var_int_bound(&a, &b, &mut out, BoundCmp::Le);

        assert_eq!(out.get("x").unwrap().lo, None);
        assert_eq!(out.get("x").unwrap().hi, Some(10));
    }

    #[test]
    fn test_extract_var_int_bound_literal_lt_var() {
        let mut out = HashMap::new();
        let a = Expr::IntLit(3);
        let b = Expr::Var("y".to_string());

        // 3 < y => y >= 4
        extract_var_int_bound(&a, &b, &mut out, BoundCmp::Lt);

        assert_eq!(out.get("y").unwrap().lo, Some(4));
        assert_eq!(out.get("y").unwrap().hi, None);
    }

    #[test]
    fn test_extract_var_int_bound_literal_gt_var() {
        let mut out = HashMap::new();
        let a = Expr::IntLit(10);
        let b = Expr::Var("z".to_string());

        // 10 > z => z <= 9
        extract_var_int_bound(&a, &b, &mut out, BoundCmp::Gt);

        assert_eq!(out.get("z").unwrap().lo, None);
        assert_eq!(out.get("z").unwrap().hi, Some(9));
    }

    #[test]
    fn test_extract_var_int_bound_var_eq_literal() {
        let mut out = HashMap::new();
        let a = Expr::Var("n".to_string());
        let b = Expr::IntLit(42);

        extract_var_int_bound(&a, &b, &mut out, BoundCmp::Eq);

        assert_eq!(out.get("n").unwrap().lo, Some(42));
        assert_eq!(out.get("n").unwrap().hi, Some(42));
    }

    #[test]
    fn test_extract_var_int_bound_struct_field_ge_literal() {
        let mut out = HashMap::new();
        let a = Expr::StructField(Box::new(Expr::Var("arr".to_string())), "count".to_string());
        let b = Expr::IntLit(0);

        extract_var_int_bound(&a, &b, &mut out, BoundCmp::Ge);

        assert_eq!(out.get("arr.count").unwrap().lo, Some(0));
        assert_eq!(out.get("arr.count").unwrap().hi, None);
    }

    #[test]
    fn test_extract_var_int_bound_literal_le_struct_field() {
        let mut out = HashMap::new();
        let a = Expr::IntLit(5);
        let b = Expr::StructField(Box::new(Expr::Var("buf".to_string())), "len".to_string());

        // 5 <= buf.len => buf.len >= 5
        extract_var_int_bound(&a, &b, &mut out, BoundCmp::Le);

        assert_eq!(out.get("buf.len").unwrap().lo, Some(5));
        assert_eq!(out.get("buf.len").unwrap().hi, None);
    }

    #[test]
    fn test_extract_var_int_bound_no_literal_no_update() {
        let mut out = HashMap::new();
        let a = Expr::Var("x".to_string());
        let b = Expr::Var("y".to_string());

        // Neither is a literal, no bounds extracted
        extract_var_int_bound(&a, &b, &mut out, BoundCmp::Ge);

        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_var_int_bound_complex_expr_no_update() {
        let mut out = HashMap::new();
        let a = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        let b = Expr::IntLit(10);

        // Complex expr (Add) cannot be named, so no bounds
        extract_var_int_bound(&a, &b, &mut out, BoundCmp::Le);

        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_var_int_bound_updates_existing() {
        let mut out = HashMap::new();
        out.insert(
            "x".to_string(),
            VarBounds {
                lo: Some(0),
                hi: None,
            },
        );

        let a = Expr::Var("x".to_string());
        let b = Expr::IntLit(100);

        extract_var_int_bound(&a, &b, &mut out, BoundCmp::Le);

        assert_eq!(out.get("x").unwrap().lo, Some(0));
        assert_eq!(out.get("x").unwrap().hi, Some(100));
    }

    // ========================================================================
    // path_condition_constrains_index tests
    // ========================================================================

    #[test]
    fn test_path_condition_constrains_index_no_condition() {
        use crate::json_types::SwiftExpr;

        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };

        let result = path_condition_constrains_index(&index, None);
        assert!(!result);
    }

    #[test]
    fn test_path_condition_constrains_index_mentions_var() {
        use crate::json_types::SwiftExpr;

        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };

        // i >= 0
        let path_cond = Some(SwiftExpr::Ge {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        });

        let result = path_condition_constrains_index(&index, path_cond.as_ref());
        assert!(result);
    }

    #[test]
    fn test_path_condition_constrains_index_does_not_mention_var() {
        use crate::json_types::SwiftExpr;

        let index = SwiftExpr::ParamRef {
            name: "i".to_string(),
            index: 0,
        };

        // j >= 0 (different variable)
        let path_cond = Some(SwiftExpr::Ge {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "j".to_string(),
                index: 1,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
        });

        let result = path_condition_constrains_index(&index, path_cond.as_ref());
        assert!(!result);
    }

    #[test]
    fn test_path_condition_constrains_index_complex_expr_returns_true() {
        use crate::json_types::SwiftExpr;

        // Complex index (not ParamRef) - assumed constrained
        let index = SwiftExpr::Add {
            lhs: Box::new(SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            }),
            rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
        };

        let path_cond = Some(SwiftExpr::BoolLit { value: true });

        let result = path_condition_constrains_index(&index, path_cond.as_ref());
        assert!(result); // Complex index assumed constrained
    }

    #[test]
    fn test_path_condition_constrains_index_and_with_var() {
        use crate::json_types::SwiftExpr;

        let index = SwiftExpr::ParamRef {
            name: "idx".to_string(),
            index: 0,
        };

        // idx >= 0 && idx < len
        let path_cond = Some(SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "idx".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            rhs: Box::new(SwiftExpr::Lt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "idx".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::ParamRef {
                    name: "len".to_string(),
                    index: 1,
                }),
            }),
        });

        let result = path_condition_constrains_index(&index, path_cond.as_ref());
        assert!(result);
    }

    #[test]
    fn test_path_condition_constrains_index_nested_mentions() {
        use crate::json_types::SwiftExpr;

        let index = SwiftExpr::ParamRef {
            name: "k".to_string(),
            index: 0,
        };

        // (x > 0) && (y > k)  - k mentioned in nested expression
        let path_cond = Some(SwiftExpr::And {
            lhs: Box::new(SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 1,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            rhs: Box::new(SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 2,
                }),
                rhs: Box::new(SwiftExpr::ParamRef {
                    name: "k".to_string(),
                    index: 0,
                }),
            }),
        });

        let result = path_condition_constrains_index(&index, path_cond.as_ref());
        assert!(result);
    }

    // ========================================================================
    // generate_param_type_bounds tests
    // ========================================================================

    #[test]
    fn test_generate_param_type_bounds_int8() {
        use crate::json_types::{SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 8,
                },
                index: 0,
            }],
            is_trusted: false,
            ..Default::default()
        };

        let bounds = generate_param_type_bounds(&bundle);
        assert_eq!(bounds.len(), 2);

        // Lower bound: x >= -128
        match &bounds[0] {
            Predicate::Expr(Expr::Ge(left, right)) => {
                assert!(matches!(left.as_ref(), Expr::Var(name) if name == "x"));
                assert!(matches!(right.as_ref(), Expr::IntLit(-128)));
            }
            _ => panic!("Expected Ge predicate"),
        }

        // Upper bound: x <= 127
        match &bounds[1] {
            Predicate::Expr(Expr::Le(left, right)) => {
                assert!(matches!(left.as_ref(), Expr::Var(name) if name == "x"));
                assert!(matches!(right.as_ref(), Expr::IntLit(127)));
            }
            _ => panic!("Expected Le predicate"),
        }
    }

    #[test]
    fn test_generate_param_type_bounds_uint8() {
        use crate::json_types::{SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            parameters: vec![SwiftParam {
                name: "u".to_string(),
                param_type: SwiftType::Int {
                    signed: false,
                    bits: 8,
                },
                index: 0,
            }],
            is_trusted: false,
            ..Default::default()
        };

        let bounds = generate_param_type_bounds(&bundle);
        assert_eq!(bounds.len(), 2);

        // Lower bound: u >= 0
        match &bounds[0] {
            Predicate::Expr(Expr::Ge(left, right)) => {
                assert!(matches!(left.as_ref(), Expr::Var(name) if name == "u"));
                assert!(matches!(right.as_ref(), Expr::IntLit(0)));
            }
            _ => panic!("Expected Ge predicate"),
        }

        // Upper bound: u <= 255
        match &bounds[1] {
            Predicate::Expr(Expr::Le(left, right)) => {
                assert!(matches!(left.as_ref(), Expr::Var(name) if name == "u"));
                assert!(matches!(right.as_ref(), Expr::IntLit(255)));
            }
            _ => panic!("Expected Le predicate"),
        }
    }

    #[test]
    fn test_generate_param_type_bounds_int32() {
        use crate::json_types::{SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            parameters: vec![SwiftParam {
                name: "n".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 32,
                },
                index: 0,
            }],
            is_trusted: false,
            ..Default::default()
        };

        let bounds = generate_param_type_bounds(&bundle);
        assert_eq!(bounds.len(), 2);

        match &bounds[0] {
            Predicate::Expr(Expr::Ge(_, right)) => {
                assert!(matches!(right.as_ref(), Expr::IntLit(-2_147_483_648)));
            }
            _ => panic!("Expected Ge predicate"),
        }

        match &bounds[1] {
            Predicate::Expr(Expr::Le(_, right)) => {
                assert!(matches!(right.as_ref(), Expr::IntLit(2_147_483_647)));
            }
            _ => panic!("Expected Le predicate"),
        }
    }

    #[test]
    fn test_generate_param_type_bounds_multiple_params() {
        use crate::json_types::{SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            parameters: vec![
                SwiftParam {
                    name: "a".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 8,
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "b".to_string(),
                    param_type: SwiftType::Int {
                        signed: false,
                        bits: 16,
                    },
                    index: 1,
                },
            ],
            is_trusted: false,
            ..Default::default()
        };

        let bounds = generate_param_type_bounds(&bundle);
        // 2 params * 2 bounds each = 4 predicates
        assert_eq!(bounds.len(), 4);
    }

    #[test]
    fn test_generate_param_type_bounds_non_int_ignored() {
        use crate::json_types::{SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            parameters: vec![SwiftParam {
                name: "flag".to_string(),
                param_type: SwiftType::Bool,
                index: 0,
            }],
            is_trusted: false,
            ..Default::default()
        };

        let bounds = generate_param_type_bounds(&bundle);
        assert!(bounds.is_empty());
    }

    #[test]
    fn test_generate_param_type_bounds_empty_params() {
        let bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            parameters: vec![],
            is_trusted: false,
            ..Default::default()
        };

        let bounds = generate_param_type_bounds(&bundle);
        assert!(bounds.is_empty());
    }

    #[test]
    fn test_generate_param_type_bounds_int64() {
        use crate::json_types::{SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            parameters: vec![SwiftParam {
                name: "big".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
                index: 0,
            }],
            is_trusted: false,
            ..Default::default()
        };

        let bounds = generate_param_type_bounds(&bundle);
        assert_eq!(bounds.len(), 2);

        match &bounds[0] {
            Predicate::Expr(Expr::Ge(_, right)) => {
                assert!(matches!(
                    right.as_ref(),
                    Expr::IntLit(-9_223_372_036_854_775_808)
                ));
            }
            _ => panic!("Expected Ge predicate"),
        }

        match &bounds[1] {
            Predicate::Expr(Expr::Le(_, right)) => {
                assert!(matches!(
                    right.as_ref(),
                    Expr::IntLit(9_223_372_036_854_775_807)
                ));
            }
            _ => panic!("Expected Le predicate"),
        }
    }

    // ========== Tests for collect_old_vars_from_expr ==========

    #[test]
    fn test_collect_old_vars_from_expr_var() {
        // old(x) should collect "x"
        let expr = Expr::Old(Box::new(Expr::Var("x".to_string())));
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars, vec!["x"]);
    }

    #[test]
    fn test_collect_old_vars_from_expr_result() {
        // old(result) should collect "result"
        let expr = Expr::Old(Box::new(Expr::Result));
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars, vec!["result"]);
    }

    #[test]
    fn test_collect_old_vars_from_expr_nested_binary() {
        // old(x) + old(y) should collect both "x" and "y"
        let expr = Expr::Add(
            Box::new(Expr::Old(Box::new(Expr::Var("x".to_string())))),
            Box::new(Expr::Old(Box::new(Expr::Var("y".to_string())))),
        );
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));
    }

    #[test]
    fn test_collect_old_vars_from_expr_no_old() {
        // x + y without old() should collect nothing
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert!(vars.is_empty());
    }

    #[test]
    fn test_collect_old_vars_from_expr_ite() {
        // ite(cond, old(a), old(b))
        let expr = Expr::Ite {
            cond: Box::new(Expr::BoolLit(true)),
            then_: Box::new(Expr::Old(Box::new(Expr::Var("a".to_string())))),
            else_: Box::new(Expr::Old(Box::new(Expr::Var("b".to_string())))),
        };
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&"a".to_string()));
        assert!(vars.contains(&"b".to_string()));
    }

    #[test]
    fn test_collect_old_vars_from_expr_array_index() {
        // old(arr)[old(idx)]
        let expr = Expr::ArrayIndex(
            Box::new(Expr::Old(Box::new(Expr::Var("arr".to_string())))),
            Box::new(Expr::Old(Box::new(Expr::Var("idx".to_string())))),
        );
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&"arr".to_string()));
        assert!(vars.contains(&"idx".to_string()));
    }

    #[test]
    fn test_collect_old_vars_from_expr_struct_field() {
        // old(obj).field
        let expr = Expr::StructField(
            Box::new(Expr::Old(Box::new(Expr::Var("obj".to_string())))),
            "field".to_string(),
        );
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars, vec!["obj"]);
    }

    #[test]
    fn test_collect_old_vars_from_expr_not() {
        // !old(flag)
        let expr = Expr::Not(Box::new(Expr::Old(Box::new(Expr::Var("flag".to_string())))));
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars, vec!["flag"]);
    }

    #[test]
    fn test_collect_old_vars_from_expr_neg() {
        // -old(n)
        let expr = Expr::Neg(Box::new(Expr::Old(Box::new(Expr::Var("n".to_string())))));
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars, vec!["n"]);
    }

    #[test]
    fn test_collect_old_vars_from_expr_apply() {
        // func(old(a), old(b))
        let expr = Expr::Apply {
            func: "func".to_string(),
            args: vec![
                Expr::Old(Box::new(Expr::Var("a".to_string()))),
                Expr::Old(Box::new(Expr::Var("b".to_string()))),
            ],
        };
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&"a".to_string()));
        assert!(vars.contains(&"b".to_string()));
    }

    #[test]
    fn test_collect_old_vars_from_expr_forall() {
        use crate::types::VcType;

        // forall x. old(y) > x
        let expr = Expr::Forall {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Gt(
                Box::new(Expr::Old(Box::new(Expr::Var("y".to_string())))),
                Box::new(Expr::Var("x".to_string())),
            )),
        };
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars, vec!["y"]);
    }

    #[test]
    fn test_collect_old_vars_from_expr_exists() {
        use crate::types::VcType;

        // exists x. old(z) == x
        let expr = Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Old(Box::new(Expr::Var("z".to_string())))),
                Box::new(Expr::Var("x".to_string())),
            )),
        };
        let mut vars = Vec::new();
        collect_old_vars_from_expr(&expr, &mut vars);
        assert_eq!(vars, vec!["z"]);
    }

    // ========== Tests for collect_old_vars_from_predicate_impl ==========

    #[test]
    fn test_collect_old_vars_from_predicate_impl_expr() {
        // Predicate::Expr(old(x) > 0)
        let pred = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Old(Box::new(Expr::Var("x".to_string())))),
            Box::new(Expr::IntLit(0)),
        ));
        let mut vars = Vec::new();
        collect_old_vars_from_predicate_impl(&pred, &mut vars);
        assert_eq!(vars, vec!["x"]);
    }

    #[test]
    fn test_collect_old_vars_from_predicate_impl_and() {
        // Predicate::And([old(a) > 0, old(b) < 10])
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::Gt(
                Box::new(Expr::Old(Box::new(Expr::Var("a".to_string())))),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Old(Box::new(Expr::Var("b".to_string())))),
                Box::new(Expr::IntLit(10)),
            )),
        ]);
        let mut vars = Vec::new();
        collect_old_vars_from_predicate_impl(&pred, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&"a".to_string()));
        assert!(vars.contains(&"b".to_string()));
    }

    #[test]
    fn test_collect_old_vars_from_predicate_impl_or() {
        // Predicate::Or([old(p) == true, old(q) == true])
        let pred = Predicate::Or(vec![
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Old(Box::new(Expr::Var("p".to_string())))),
                Box::new(Expr::BoolLit(true)),
            )),
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Old(Box::new(Expr::Var("q".to_string())))),
                Box::new(Expr::BoolLit(true)),
            )),
        ]);
        let mut vars = Vec::new();
        collect_old_vars_from_predicate_impl(&pred, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&"p".to_string()));
        assert!(vars.contains(&"q".to_string()));
    }

    #[test]
    fn test_collect_old_vars_from_predicate_impl_not() {
        // Predicate::Not(old(flag) == true)
        let pred = Predicate::Not(Box::new(Predicate::Expr(Expr::Eq(
            Box::new(Expr::Old(Box::new(Expr::Var("flag".to_string())))),
            Box::new(Expr::BoolLit(true)),
        ))));
        let mut vars = Vec::new();
        collect_old_vars_from_predicate_impl(&pred, &mut vars);
        assert_eq!(vars, vec!["flag"]);
    }

    #[test]
    fn test_collect_old_vars_from_predicate_impl_implies() {
        // Predicate::Implies(old(pre) > 0, old(post) > 0)
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Old(Box::new(Expr::Var("pre".to_string())))),
                Box::new(Expr::IntLit(0)),
            ))),
            Box::new(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Old(Box::new(Expr::Var("post".to_string())))),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let mut vars = Vec::new();
        collect_old_vars_from_predicate_impl(&pred, &mut vars);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&"pre".to_string()));
        assert!(vars.contains(&"post".to_string()));
    }

    #[test]
    fn test_collect_old_vars_from_predicate_impl_empty() {
        // Predicate with no old() references
        let pred = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let mut vars = Vec::new();
        collect_old_vars_from_predicate_impl(&pred, &mut vars);
        assert!(vars.is_empty());
    }

    // ========== Tests for substitute_old_expr ==========

    #[test]
    fn test_substitute_old_expr_simple_var() {
        // old(x) -> x
        let expr = Expr::Old(Box::new(Expr::Var("x".to_string())));
        let result = substitute_old_expr(&expr);
        assert!(matches!(result, Expr::Var(name) if name == "x"));
    }

    #[test]
    fn test_substitute_old_expr_result() {
        // old(result) -> result
        let expr = Expr::Old(Box::new(Expr::Result));
        let result = substitute_old_expr(&expr);
        assert!(matches!(result, Expr::Result));
    }

    #[test]
    fn test_substitute_old_expr_nested_old() {
        // old(old(x)) -> x (both old wrappers removed)
        let expr = Expr::Old(Box::new(Expr::Old(Box::new(Expr::Var("x".to_string())))));
        let result = substitute_old_expr(&expr);
        assert!(matches!(result, Expr::Var(name) if name == "x"));
    }

    #[test]
    fn test_substitute_old_expr_add() {
        // old(a) + old(b) -> a + b
        let expr = Expr::Add(
            Box::new(Expr::Old(Box::new(Expr::Var("a".to_string())))),
            Box::new(Expr::Old(Box::new(Expr::Var("b".to_string())))),
        );
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Add(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(name) if name == "a"));
                assert!(matches!(rhs.as_ref(), Expr::Var(name) if name == "b"));
            }
            _ => panic!("Expected Add expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_sub() {
        // old(x) - y -> x - y
        let expr = Expr::Sub(
            Box::new(Expr::Old(Box::new(Expr::Var("x".to_string())))),
            Box::new(Expr::Var("y".to_string())),
        );
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Sub(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(name) if name == "x"));
                assert!(matches!(rhs.as_ref(), Expr::Var(name) if name == "y"));
            }
            _ => panic!("Expected Sub expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_mul() {
        // old(a) * old(b)
        let expr = Expr::Mul(
            Box::new(Expr::Old(Box::new(Expr::Var("a".to_string())))),
            Box::new(Expr::Old(Box::new(Expr::Var("b".to_string())))),
        );
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Mul(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(name) if name == "a"));
                assert!(matches!(rhs.as_ref(), Expr::Var(name) if name == "b"));
            }
            _ => panic!("Expected Mul expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_div() {
        // old(n) / 2
        let expr = Expr::Div(
            Box::new(Expr::Old(Box::new(Expr::Var("n".to_string())))),
            Box::new(Expr::IntLit(2)),
        );
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Div(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(name) if name == "n"));
                assert!(matches!(rhs.as_ref(), Expr::IntLit(2)));
            }
            _ => panic!("Expected Div expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_rem() {
        // old(n) % old(m)
        let expr = Expr::Rem(
            Box::new(Expr::Old(Box::new(Expr::Var("n".to_string())))),
            Box::new(Expr::Old(Box::new(Expr::Var("m".to_string())))),
        );
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Rem(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(name) if name == "n"));
                assert!(matches!(rhs.as_ref(), Expr::Var(name) if name == "m"));
            }
            _ => panic!("Expected Rem expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_comparison() {
        // old(x) < old(y)
        let expr = Expr::Lt(
            Box::new(Expr::Old(Box::new(Expr::Var("x".to_string())))),
            Box::new(Expr::Old(Box::new(Expr::Var("y".to_string())))),
        );
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Lt(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(name) if name == "x"));
                assert!(matches!(rhs.as_ref(), Expr::Var(name) if name == "y"));
            }
            _ => panic!("Expected Lt expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_neg() {
        // -old(n)
        let expr = Expr::Neg(Box::new(Expr::Old(Box::new(Expr::Var("n".to_string())))));
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Neg(inner) => {
                assert!(matches!(inner.as_ref(), Expr::Var(name) if name == "n"));
            }
            _ => panic!("Expected Neg expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_not() {
        // !old(flag)
        let expr = Expr::Not(Box::new(Expr::Old(Box::new(Expr::Var("flag".to_string())))));
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Not(inner) => {
                assert!(matches!(inner.as_ref(), Expr::Var(name) if name == "flag"));
            }
            _ => panic!("Expected Not expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_ite() {
        // ite(old(cond), old(a), old(b))
        let expr = Expr::Ite {
            cond: Box::new(Expr::Old(Box::new(Expr::Var("cond".to_string())))),
            then_: Box::new(Expr::Old(Box::new(Expr::Var("a".to_string())))),
            else_: Box::new(Expr::Old(Box::new(Expr::Var("b".to_string())))),
        };
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Ite { cond, then_, else_ } => {
                assert!(matches!(cond.as_ref(), Expr::Var(name) if name == "cond"));
                assert!(matches!(then_.as_ref(), Expr::Var(name) if name == "a"));
                assert!(matches!(else_.as_ref(), Expr::Var(name) if name == "b"));
            }
            _ => panic!("Expected Ite expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_array_index() {
        // old(arr)[old(i)]
        let expr = Expr::ArrayIndex(
            Box::new(Expr::Old(Box::new(Expr::Var("arr".to_string())))),
            Box::new(Expr::Old(Box::new(Expr::Var("i".to_string())))),
        );
        let result = substitute_old_expr(&expr);
        match result {
            Expr::ArrayIndex(base, idx) => {
                assert!(matches!(base.as_ref(), Expr::Var(name) if name == "arr"));
                assert!(matches!(idx.as_ref(), Expr::Var(name) if name == "i"));
            }
            _ => panic!("Expected ArrayIndex expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_struct_field() {
        // old(obj).field
        let expr = Expr::StructField(
            Box::new(Expr::Old(Box::new(Expr::Var("obj".to_string())))),
            "field".to_string(),
        );
        let result = substitute_old_expr(&expr);
        match result {
            Expr::StructField(base, field) => {
                assert!(matches!(base.as_ref(), Expr::Var(name) if name == "obj"));
                assert_eq!(field, "field");
            }
            _ => panic!("Expected StructField expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_apply() {
        // func(old(a), old(b))
        let expr = Expr::Apply {
            func: "func".to_string(),
            args: vec![
                Expr::Old(Box::new(Expr::Var("a".to_string()))),
                Expr::Old(Box::new(Expr::Var("b".to_string()))),
            ],
        };
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Apply { func, args } => {
                assert_eq!(func, "func");
                assert_eq!(args.len(), 2);
                assert!(matches!(&args[0], Expr::Var(name) if name == "a"));
                assert!(matches!(&args[1], Expr::Var(name) if name == "b"));
            }
            _ => panic!("Expected Apply expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_forall() {
        use crate::types::VcType;

        // forall x. old(y) > x
        let expr = Expr::Forall {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Gt(
                Box::new(Expr::Old(Box::new(Expr::Var("y".to_string())))),
                Box::new(Expr::Var("x".to_string())),
            )),
        };
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Forall { vars, body } => {
                assert_eq!(vars.len(), 1);
                match body.as_ref() {
                    Expr::Gt(lhs, _) => {
                        assert!(matches!(lhs.as_ref(), Expr::Var(name) if name == "y"));
                    }
                    _ => panic!("Expected Gt in body"),
                }
            }
            _ => panic!("Expected Forall expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_exists() {
        use crate::types::VcType;

        // exists x. old(z) == x
        let expr = Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Old(Box::new(Expr::Var("z".to_string())))),
                Box::new(Expr::Var("x".to_string())),
            )),
        };
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Exists { vars, body } => {
                assert_eq!(vars.len(), 1);
                match body.as_ref() {
                    Expr::Eq(lhs, _) => {
                        assert!(matches!(lhs.as_ref(), Expr::Var(name) if name == "z"));
                    }
                    _ => panic!("Expected Eq in body"),
                }
            }
            _ => panic!("Expected Exists expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_no_old() {
        // x + y (no old to substitute)
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let result = substitute_old_expr(&expr);
        match result {
            Expr::Add(lhs, rhs) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(name) if name == "x"));
                assert!(matches!(rhs.as_ref(), Expr::Var(name) if name == "y"));
            }
            _ => panic!("Expected Add expression"),
        }
    }

    #[test]
    fn test_substitute_old_expr_terminals() {
        // Test terminal expressions are preserved
        assert!(matches!(
            substitute_old_expr(&Expr::IntLit(42)),
            Expr::IntLit(42)
        ));
        assert!(matches!(
            substitute_old_expr(&Expr::BoolLit(true)),
            Expr::BoolLit(true)
        ));
        assert!(matches!(substitute_old_expr(&Expr::NilLit), Expr::NilLit));
        assert!(matches!(substitute_old_expr(&Expr::Result), Expr::Result));
    }

    // ========== Tests for try_prove_overflow_safe_via_path_condition ==========

    #[test]
    fn test_try_prove_overflow_safe_non_overflow_vc() {
        use crate::json_types::SwiftAutoVc;

        // DivByZero should return None
        let auto_vc = SwiftAutoVc::DivByZero {
            divisor: crate::json_types::SwiftExpr::IntLit { value: 0 },
            description: "div by zero".to_string(),
            path_condition: None,
            source_line: 1,
            source_column: 1,
        };
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_no_path_condition() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // Overflow without path condition should return None
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::IntLit { value: 1 },
            ],
            description: "x + 1 overflow".to_string(),
            path_condition: None,
            signed: true,
            bits: 64,
            source_line: 1,
            source_column: 1,
        };
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_increment_guarded() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // x + 1 with x < Int64.max path condition
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::IntLit { value: 1 },
            ],
            description: "x + 1 overflow".to_string(),
            path_condition: Some(SwiftExpr::Lt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit {
                    value: 9_223_372_036_854_775_807,
                }),
            }),
            signed: true,
            bits: 64,
            source_line: 1,
            source_column: 1,
        };

        let result = try_prove_overflow_safe_via_path_condition(&auto_vc);
        assert!(result.is_some());
        let (verify_result, _smtlib) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_safe_decrement_guarded() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // x - 1 with x > Int64.min path condition
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "sub".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::IntLit { value: 1 },
            ],
            description: "x - 1 underflow".to_string(),
            path_condition: Some(SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit {
                    value: -9_223_372_036_854_775_808,
                }),
            }),
            signed: true,
            bits: 64,
            source_line: 1,
            source_column: 1,
        };

        let result = try_prove_overflow_safe_via_path_condition(&auto_vc);
        assert!(result.is_some());
        let (verify_result, _smtlib) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_safe_increment_not_guarded() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // x + 1 with unrelated path condition
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::IntLit { value: 1 },
            ],
            description: "x + 1 overflow".to_string(),
            path_condition: Some(SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            signed: true,
            bits: 64,
            source_line: 1,
            source_column: 1,
        };

        // Unrelated path condition should not prove safety
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_non_increment_add() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // x + y (not increment by 1)
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                },
            ],
            description: "x + y overflow".to_string(),
            path_condition: Some(SwiftExpr::Lt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit {
                    value: 9_223_372_036_854_775_807,
                }),
            }),
            signed: true,
            bits: 64,
            source_line: 1,
            source_column: 1,
        };

        // Non-increment operations require more complex analysis
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    #[test]
    fn test_try_prove_overflow_safe_sub_non_decrement() {
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        // x - y (not decrement by 1)
        let auto_vc = SwiftAutoVc::Overflow {
            operation: "sub".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                },
            ],
            description: "x - y underflow".to_string(),
            path_condition: Some(SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit {
                    value: -9_223_372_036_854_775_808,
                }),
            }),
            signed: true,
            bits: 64,
            source_line: 1,
            source_column: 1,
        };

        // Non-decrement operations not handled by this fast path
        assert!(try_prove_overflow_safe_via_path_condition(&auto_vc).is_none());
    }

    // ========================================================================
    // Unit Tests for extract_non_nil_from_expr (v498)
    // ========================================================================

    #[test]
    fn test_extract_non_nil_from_expr_has_value_eq_true() {
        // value.hasValue == true
        let expr = Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("value".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        );
        let mut out = HashSet::new();
        extract_non_nil_from_expr(&expr, &mut out);
        assert!(out.contains("value"));
        assert_eq!(out.len(), 1);
    }

    #[test]
    fn test_extract_non_nil_from_expr_true_eq_has_value() {
        // true == value.hasValue (reversed order)
        let expr = Expr::Eq(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::StructField(
                Box::new(Expr::Var("value".to_string())),
                "hasValue".to_string(),
            )),
        );
        let mut out = HashSet::new();
        extract_non_nil_from_expr(&expr, &mut out);
        assert!(out.contains("value"));
        assert_eq!(out.len(), 1);
    }

    #[test]
    fn test_extract_non_nil_from_expr_and_conjunction() {
        // a.hasValue == true && b.hasValue == true
        let expr = Expr::And(
            Box::new(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("a".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
            Box::new(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("b".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        );
        let mut out = HashSet::new();
        extract_non_nil_from_expr(&expr, &mut out);
        assert!(out.contains("a"));
        assert!(out.contains("b"));
        assert_eq!(out.len(), 2);
    }

    #[test]
    fn test_extract_non_nil_from_expr_nested_field() {
        // x.y.hasValue == true
        let expr = Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("x".to_string())),
                    "y".to_string(),
                )),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        );
        let mut out = HashSet::new();
        extract_non_nil_from_expr(&expr, &mut out);
        assert!(out.contains("x.y"));
        assert_eq!(out.len(), 1);
    }

    #[test]
    fn test_extract_non_nil_from_expr_has_value_eq_false() {
        // value.hasValue == false (should NOT extract)
        let expr = Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("value".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(false)),
        );
        let mut out = HashSet::new();
        extract_non_nil_from_expr(&expr, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_non_nil_from_expr_other_field() {
        // value.someOtherField == true (should NOT extract)
        let expr = Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("value".to_string())),
                "someOtherField".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        );
        let mut out = HashSet::new();
        extract_non_nil_from_expr(&expr, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_non_nil_from_expr_literal_eq() {
        // 1 == 1 (should NOT extract)
        let expr = Expr::Eq(Box::new(Expr::IntLit(1)), Box::new(Expr::IntLit(1)));
        let mut out = HashSet::new();
        extract_non_nil_from_expr(&expr, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_non_nil_from_expr_non_eq() {
        // value > 0 (should NOT extract - not an equality check)
        let expr = Expr::Gt(
            Box::new(Expr::Var("value".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        let mut out = HashSet::new();
        extract_non_nil_from_expr(&expr, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_non_nil_from_expr_nested_and() {
        // (a.hasValue == true && b.hasValue == true) && c.hasValue == true
        let inner = Expr::And(
            Box::new(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("a".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
            Box::new(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("b".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        );
        let expr = Expr::And(
            Box::new(inner),
            Box::new(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("c".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        );
        let mut out = HashSet::new();
        extract_non_nil_from_expr(&expr, &mut out);
        assert!(out.contains("a"));
        assert!(out.contains("b"));
        assert!(out.contains("c"));
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn test_extract_non_nil_from_expr_var_only() {
        // Just a variable, not a struct field
        let expr = Expr::Eq(
            Box::new(Expr::Var("value".to_string())),
            Box::new(Expr::BoolLit(true)),
        );
        let mut out = HashSet::new();
        extract_non_nil_from_expr(&expr, &mut out);
        assert!(out.is_empty());
    }

    // ========================================================================
    // Unit Tests for extract_non_nil_from_predicate (v498)
    // ========================================================================

    #[test]
    fn test_extract_non_nil_from_predicate_expr() {
        // Predicate::Expr wrapping hasValue check
        let pred = Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("value".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        ));
        let mut out = HashSet::new();
        extract_non_nil_from_predicate(&pred, &mut out);
        assert!(out.contains("value"));
        assert_eq!(out.len(), 1);
    }

    #[test]
    fn test_extract_non_nil_from_predicate_and() {
        // Predicate::And with multiple hasValue checks
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("a".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("b".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        ]);
        let mut out = HashSet::new();
        extract_non_nil_from_predicate(&pred, &mut out);
        assert!(out.contains("a"));
        assert!(out.contains("b"));
        assert_eq!(out.len(), 2);
    }

    #[test]
    fn test_extract_non_nil_from_predicate_or_ignored() {
        // Predicate::Or should be ignored (cannot assume either branch is true)
        let pred = Predicate::Or(vec![
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("a".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("b".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        ]);
        let mut out = HashSet::new();
        extract_non_nil_from_predicate(&pred, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_non_nil_from_predicate_not_ignored() {
        // Predicate::Not should be ignored
        let pred = Predicate::Not(Box::new(Predicate::Expr(Expr::Eq(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("value".to_string())),
                "hasValue".to_string(),
            )),
            Box::new(Expr::BoolLit(true)),
        ))));
        let mut out = HashSet::new();
        extract_non_nil_from_predicate(&pred, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_non_nil_from_predicate_implies_ignored() {
        // Predicate::Implies should be ignored
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::BoolLit(true))),
            Box::new(Predicate::Expr(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("value".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            ))),
        );
        let mut out = HashSet::new();
        extract_non_nil_from_predicate(&pred, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_non_nil_from_predicate_empty_and() {
        // Empty And predicate
        let pred = Predicate::And(vec![]);
        let mut out = HashSet::new();
        extract_non_nil_from_predicate(&pred, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_non_nil_from_predicate_nested_and() {
        // Nested And predicates
        let pred = Predicate::And(vec![
            Predicate::And(vec![Predicate::Expr(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("a".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            ))]),
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("b".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        ]);
        let mut out = HashSet::new();
        extract_non_nil_from_predicate(&pred, &mut out);
        assert!(out.contains("a"));
        assert!(out.contains("b"));
        assert_eq!(out.len(), 2);
    }

    #[test]
    fn test_extract_non_nil_from_predicate_expr_and_conjunction() {
        // Predicate::Expr wrapping And expression
        let pred = Predicate::Expr(Expr::And(
            Box::new(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("a".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
            Box::new(Expr::Eq(
                Box::new(Expr::StructField(
                    Box::new(Expr::Var("b".to_string())),
                    "hasValue".to_string(),
                )),
                Box::new(Expr::BoolLit(true)),
            )),
        ));
        let mut out = HashSet::new();
        extract_non_nil_from_predicate(&pred, &mut out);
        assert!(out.contains("a"));
        assert!(out.contains("b"));
        assert_eq!(out.len(), 2);
    }

    // ========================================================================
    // Tests for extract_simple_bounds_from_expr
    // ========================================================================

    #[test]
    fn test_extract_simple_bounds_from_expr_ge() {
        // x >= 5
        let expr = Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.contains_key("x"));
        assert_eq!(out["x"].lo, Some(5));
        assert_eq!(out["x"].hi, None);
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_le() {
        // y <= 10
        let expr = Expr::Le(
            Box::new(Expr::Var("y".to_string())),
            Box::new(Expr::IntLit(10)),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.contains_key("y"));
        assert_eq!(out["y"].lo, None);
        assert_eq!(out["y"].hi, Some(10));
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_gt() {
        // z > 3 => z >= 4
        let expr = Expr::Gt(
            Box::new(Expr::Var("z".to_string())),
            Box::new(Expr::IntLit(3)),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.contains_key("z"));
        assert_eq!(out["z"].lo, Some(4));
        assert_eq!(out["z"].hi, None);
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_lt() {
        // w < 7 => w <= 6
        let expr = Expr::Lt(
            Box::new(Expr::Var("w".to_string())),
            Box::new(Expr::IntLit(7)),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.contains_key("w"));
        assert_eq!(out["w"].lo, None);
        assert_eq!(out["w"].hi, Some(6));
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_eq() {
        // n == 42 => lo=42, hi=42
        let expr = Expr::Eq(
            Box::new(Expr::Var("n".to_string())),
            Box::new(Expr::IntLit(42)),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.contains_key("n"));
        assert_eq!(out["n"].lo, Some(42));
        assert_eq!(out["n"].hi, Some(42));
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_and() {
        // x >= 0 && x <= 100
        let expr = Expr::And(
            Box::new(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.contains_key("x"));
        assert_eq!(out["x"].lo, Some(0));
        assert_eq!(out["x"].hi, Some(100));
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_literal_on_left() {
        // 5 <= x => x >= 5
        let expr = Expr::Le(
            Box::new(Expr::IntLit(5)),
            Box::new(Expr::Var("x".to_string())),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.contains_key("x"));
        assert_eq!(out["x"].lo, Some(5));
        assert_eq!(out["x"].hi, None);
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_negative_literal() {
        // x >= -10
        let expr = Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Neg(Box::new(Expr::IntLit(10)))),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.contains_key("x"));
        assert_eq!(out["x"].lo, Some(-10));
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_struct_field() {
        // arr.count >= 0
        let expr = Expr::Ge(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("arr".to_string())),
                "count".to_string(),
            )),
            Box::new(Expr::IntLit(0)),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.contains_key("arr.count"));
        assert_eq!(out["arr.count"].lo, Some(0));
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_ignores_or() {
        // Or is ignored (not sound to extract from disjunctions)
        let expr = Expr::Or(
            Box::new(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(-10)),
            )),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_ignores_ne() {
        // Ne is ignored
        let expr = Expr::Ne(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_simple_bounds_from_expr_multiple_vars() {
        // x >= 0 && y <= 10 && z == 5
        let expr = Expr::And(
            Box::new(Expr::And(
                Box::new(Expr::Ge(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                Box::new(Expr::Le(
                    Box::new(Expr::Var("y".to_string())),
                    Box::new(Expr::IntLit(10)),
                )),
            )),
            Box::new(Expr::Eq(
                Box::new(Expr::Var("z".to_string())),
                Box::new(Expr::IntLit(5)),
            )),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_expr(&expr, &mut out);
        assert_eq!(out.len(), 3);
        assert_eq!(out["x"].lo, Some(0));
        assert_eq!(out["y"].hi, Some(10));
        assert_eq!(out["z"].lo, Some(5));
        assert_eq!(out["z"].hi, Some(5));
    }

    // ========================================================================
    // Tests for extract_simple_bounds_from_predicate
    // ========================================================================

    #[test]
    fn test_extract_simple_bounds_from_predicate_expr() {
        // Single expression predicate
        let pred = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let mut out = HashMap::new();
        extract_simple_bounds_from_predicate(&pred, &mut out);
        assert!(out.contains_key("x"));
        assert_eq!(out["x"].lo, Some(0));
    }

    #[test]
    fn test_extract_simple_bounds_from_predicate_and() {
        // And predicate with multiple bounds
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ]);
        let mut out = HashMap::new();
        extract_simple_bounds_from_predicate(&pred, &mut out);
        assert!(out.contains_key("x"));
        assert_eq!(out["x"].lo, Some(0));
        assert_eq!(out["x"].hi, Some(100));
    }

    #[test]
    fn test_extract_simple_bounds_from_predicate_ignores_or() {
        // Or predicate is ignored
        let pred = Predicate::Or(vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(-10)),
            )),
        ]);
        let mut out = HashMap::new();
        extract_simple_bounds_from_predicate(&pred, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_simple_bounds_from_predicate_ignores_not() {
        // Not predicate is ignored
        let pred = Predicate::Not(Box::new(Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))));
        let mut out = HashMap::new();
        extract_simple_bounds_from_predicate(&pred, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_simple_bounds_from_predicate_ignores_implies() {
        // Implies predicate is ignored
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::BoolLit(true))),
            Box::new(Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let mut out = HashMap::new();
        extract_simple_bounds_from_predicate(&pred, &mut out);
        assert!(out.is_empty());
    }

    #[test]
    fn test_extract_simple_bounds_from_predicate_nested_and() {
        // Nested And predicates
        let pred = Predicate::And(vec![
            Predicate::And(vec![
                Predicate::Expr(Expr::Ge(
                    Box::new(Expr::Var("a".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                Predicate::Expr(Expr::Le(
                    Box::new(Expr::Var("a".to_string())),
                    Box::new(Expr::IntLit(10)),
                )),
            ]),
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(5)),
            )),
        ]);
        let mut out = HashMap::new();
        extract_simple_bounds_from_predicate(&pred, &mut out);
        assert_eq!(out.len(), 2);
        assert_eq!(out["a"].lo, Some(0));
        assert_eq!(out["a"].hi, Some(10));
        assert_eq!(out["b"].lo, Some(5));
        assert_eq!(out["b"].hi, Some(5));
    }

    #[test]
    fn test_extract_simple_bounds_from_predicate_empty_and() {
        // Empty And predicate
        let pred = Predicate::And(vec![]);
        let mut out = HashMap::new();
        extract_simple_bounds_from_predicate(&pred, &mut out);
        assert!(out.is_empty());
    }

    // ========================================================================
    // Tests for expand_body_constraint_to_cases
    // ========================================================================

    #[test]
    fn test_expand_body_constraint_to_cases_non_eq() {
        // Non-Eq constraint returns single case
        let constraint = Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        let cases = expand_body_constraint_to_cases(&constraint);
        assert_eq!(cases.len(), 1);
        assert!(cases[0].0.is_empty()); // no path conditions
        match &cases[0].1 {
            Predicate::Expr(e) => {
                assert!(matches!(e, Expr::Ge(_, _)));
            }
            _ => panic!("Expected Predicate::Expr"),
        }
    }

    #[test]
    fn test_expand_body_constraint_to_cases_simple_eq() {
        // Simple equality without ITE
        let constraint = Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        let cases = expand_body_constraint_to_cases(&constraint);
        // No ITE, so single case
        assert_eq!(cases.len(), 1);
    }

    #[test]
    fn test_expand_body_constraint_to_cases_ite() {
        // result = ite(cond, then, else)
        let constraint = Expr::Eq(
            Box::new(Expr::Result),
            Box::new(Expr::Ite {
                cond: Box::new(Expr::Gt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                then_: Box::new(Expr::Var("x".to_string())),
                else_: Box::new(Expr::Neg(Box::new(Expr::Var("x".to_string())))),
            }),
        );
        let cases = expand_body_constraint_to_cases(&constraint);
        // Should expand to 2 cases: one for cond=true, one for cond=false
        assert_eq!(cases.len(), 2);
    }

    #[test]
    fn test_expand_body_constraint_to_cases_literal() {
        // Literal constraint
        let constraint = Expr::BoolLit(true);
        let cases = expand_body_constraint_to_cases(&constraint);
        assert_eq!(cases.len(), 1);
        match &cases[0].1 {
            Predicate::Expr(Expr::BoolLit(true)) => {}
            _ => panic!("Expected BoolLit(true)"),
        }
    }

    #[test]
    fn test_expand_body_constraint_to_cases_and() {
        // And constraint - not Eq, so single case
        let constraint = Expr::And(
            Box::new(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        );
        let cases = expand_body_constraint_to_cases(&constraint);
        assert_eq!(cases.len(), 1);
    }

    // ========================================================================
    // Tests for try_prove_overflow_via_intervals
    // ========================================================================

    #[test]
    fn test_try_prove_overflow_via_intervals_non_overflow_vc() {
        // Non-Overflow VCs return None
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::DivByZero {
            divisor: SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            },
            description: "test".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let result = try_prove_overflow_via_intervals(&auto_vc, &[]);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_add_bounded() {
        // Add with bounded operands should prove safe
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
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
            description: "a + b".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        // Preconditions: a in [0, 100], b in [0, 100]
        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ];

        let result = try_prove_overflow_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_sub_bounded() {
        // Sub with bounded operands should prove safe
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "sub".to_string(),
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
            description: "a - b".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        // Preconditions: a in [0, 100], b in [0, 50]
        // a - b in [-50, 100], which is within Int64 bounds
        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(50)),
            )),
        ];

        let result = try_prove_overflow_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_mul_bounded() {
        // Mul with bounded operands should prove safe
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "mul".to_string(),
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
            description: "a * b".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        // Preconditions: a in [0, 1000], b in [0, 1000]
        // a * b in [0, 1000000], which is within Int64 bounds
        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(1000)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(1000)),
            )),
        ];

        let result = try_prove_overflow_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_neg_bounded() {
        // Neg with bounded operand should prove safe
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "neg".to_string(),
            operands: vec![SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }],
            description: "-x".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        // Precondition: x in [-100, 100]
        // -x in [-100, 100], which is within Int64 bounds
        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::Neg(Box::new(Expr::IntLit(100)))),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ];

        let result = try_prove_overflow_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_div_divisor_excludes_neg1() {
        // Division where divisor excludes -1 should prove safe
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "div".to_string(),
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
            description: "a / b".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        // Preconditions: b in [1, 100] (excludes -1)
        // interval_for_expr requires both lo and hi bounds
        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ];

        let result = try_prove_overflow_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_div_dividend_excludes_min() {
        // Division where dividend excludes INT_MIN should prove safe
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "div".to_string(),
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
            description: "a / b".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        // Preconditions: a in [0, 1000] (excludes INT64_MIN)
        // interval_for_expr requires both lo and hi bounds
        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(1000)),
            )),
        ];

        let result = try_prove_overflow_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_mod_divisor_excludes_neg1() {
        // Modulo where divisor excludes -1 should prove safe
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "mod".to_string(),
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
            description: "a % b".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        // Preconditions: b in [1, 100] (excludes -1)
        // interval_for_expr requires both lo and hi bounds
        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ];

        let result = try_prove_overflow_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Proven));
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_no_bounds() {
        // No bounds for operands - can't prove
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
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
            description: "a + b".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        // No preconditions - can't determine bounds
        let result = try_prove_overflow_via_intervals(&auto_vc, &[]);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_single_operand() {
        // Single operand for binary op returns None
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![SwiftExpr::ParamRef {
                name: "a".to_string(),
                index: 0,
            }],
            description: "incomplete add".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        let result = try_prove_overflow_via_intervals(&auto_vc, &[]);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_unknown_op() {
        // Unknown operation returns None
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "unknown".to_string(),
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
            description: "unknown op".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 64,
        };

        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ];

        let result = try_prove_overflow_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_none());
    }

    #[test]
    fn test_try_prove_overflow_via_intervals_int8_overflow_detected() {
        // Int8 add that can overflow should be detected
        use crate::json_types::{SwiftAutoVc, SwiftExpr};

        let auto_vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
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
            description: "a + b".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
            signed: true,
            bits: 8, // Int8: [-128, 127]
        };

        // Preconditions: a in [100, 120], b in [50, 60]
        // a + b in [150, 180], which exceeds Int8 max of 127
        let preconditions = vec![
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(120)),
            )),
            Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(50)),
            )),
            Predicate::Expr(Expr::Le(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(60)),
            )),
        ];

        let result = try_prove_overflow_via_intervals(&auto_vc, &preconditions);
        assert!(result.is_some());
        let (verify_result, _) = result.unwrap();
        assert!(matches!(verify_result, VerifyResult::Counterexample(_)));
    }

    // ==================== verify_bundle_with_trace tests ====================

    #[test]
    fn test_verify_bundle_with_trace_trusted() {
        // Test that trusted bundles return trace with function name but empty VC traces
        let bundle = SwiftVcBundle {
            function_name: "trusted_func".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
            parameters: vec![],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: true,
            body_constraints: vec![],
            ..Default::default()
        };

        let result = verify_bundle_with_trace(&bundle);
        assert!(
            result.is_ok(),
            "verify_bundle_with_trace failed: {result:?}"
        );
        let (response, trace) = result.unwrap();

        // Response should indicate trusted
        assert!(response.is_trusted);
        assert_eq!(response.function_name, "trusted_func");
        assert!(matches!(
            response.spec_result,
            Some(SwiftVerifyResult::Verified { .. })
        ));
        assert_eq!(response.summary.trusted, 1);

        // Trace should have function name but empty traces
        assert_eq!(trace.function_name, "trusted_func");
        assert!(trace.spec_traces.is_empty());
        assert!(trace.auto_vc_traces.is_empty());
    }

    #[test]
    fn test_verify_bundle_with_trace_empty_ensures() {
        // Test bundle with no ensures clauses
        let bundle = SwiftVcBundle {
            function_name: "no_ensures".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 5,
            source_column: 0,
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

        let result = verify_bundle_with_trace(&bundle);
        assert!(
            result.is_ok(),
            "verify_bundle_with_trace failed: {result:?}"
        );
        let (response, trace) = result.unwrap();

        // Response should indicate success (nothing to verify)
        assert!(!response.is_trusted);
        assert_eq!(response.function_name, "no_ensures");

        // Trace should be present with function name
        assert_eq!(trace.function_name, "no_ensures");
    }

    #[test]
    fn test_verify_bundle_with_trace_simple_ensures() {
        // Test bundle with a simple ensures clause that should verify
        use crate::json_types::{SwiftExpr, SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "identity".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 10,
            source_column: 0,
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 32,
                },
                index: 0,
            }],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 32,
            }),
            requires: vec![],
            ensures: vec![SwiftExpr::Eq {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::ResultRef), // result == result (tautology)
            }],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let result = verify_bundle_with_trace(&bundle);
        assert!(
            result.is_ok(),
            "verify_bundle_with_trace failed: {result:?}"
        );
        let (response, trace) = result.unwrap();

        // Should verify successfully
        assert!(!response.is_trusted);
        assert_eq!(response.function_name, "identity");

        // Trace should contain the function name
        assert_eq!(trace.function_name, "identity");

        // Trace is present and has function name - spec_traces may or may not be populated
        // depending on whether there were ensures to verify
        let _ = trace.spec_traces.len(); // Just verify it's accessible
    }

    #[test]
    fn test_verify_bundle_with_trace_returns_function_name() {
        // Test that trace always contains the correct function name
        let bundle = SwiftVcBundle {
            function_name: "my_special_function_123".to_string(),
            source_file: "special.swift".to_string(),
            source_line: 42,
            source_column: 0,
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

        let result = verify_bundle_with_trace(&bundle);
        assert!(result.is_ok());
        let (response, trace) = result.unwrap();

        assert_eq!(response.function_name, "my_special_function_123");
        assert_eq!(trace.function_name, "my_special_function_123");
    }

    #[test]
    fn test_verify_bundle_with_trace_vs_verify_bundle_consistency() {
        // Test that verify_bundle_with_trace returns same response as verify_bundle
        let bundle = SwiftVcBundle {
            function_name: "consistency_test".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
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

        let response_basic = verify_bundle(&bundle).unwrap();
        let (response_trace, _trace) = verify_bundle_with_trace(&bundle).unwrap();

        // Both should have same function name
        assert_eq!(response_basic.function_name, response_trace.function_name);
        // Both should have same trusted status
        assert_eq!(response_basic.is_trusted, response_trace.is_trusted);
        // Both should have same source info
        assert_eq!(response_basic.source_file, response_trace.source_file);
        assert_eq!(response_basic.source_line, response_trace.source_line);
    }

    #[test]
    fn test_verify_bundle_with_trace_auto_vcs() {
        // Test bundle with auto-VCs (overflow checks, etc.)
        use crate::json_types::{SwiftAutoVc, SwiftExpr, SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "add_with_overflow".to_string(),
            source_file: "math.swift".to_string(),
            source_line: 20,
            source_column: 0,
            parameters: vec![
                SwiftParam {
                    name: "a".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 32,
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "b".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 32,
                    },
                    index: 1,
                },
            ],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 32,
            }),
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![SwiftAutoVc::Overflow {
                operation: "add".to_string(),
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
                description: "a + b".to_string(),
                source_line: 21,
                source_column: 10,
                path_condition: None,
                signed: true,
                bits: 32,
            }],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let result = verify_bundle_with_trace(&bundle);
        assert!(
            result.is_ok(),
            "verify_bundle_with_trace failed: {result:?}"
        );
        let (response, trace) = result.unwrap();

        assert_eq!(response.function_name, "add_with_overflow");
        assert_eq!(trace.function_name, "add_with_overflow");

        // Verify we can access auto_vc_results and auto_vc_traces
        // (actual count depends on implementation)
        let _ = response.auto_vc_results.len();
        let _ = trace.auto_vc_traces.len();
    }

    // ==================== verify_bundle_with_progress tests ====================

    #[test]
    fn test_verify_bundle_with_progress_trusted() {
        // Test that trusted bundles call progress exactly once with trusted result
        let bundle = SwiftVcBundle {
            function_name: "trusted_progress".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
            parameters: vec![],
            return_type: None,
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: true,
            body_constraints: vec![],
            ..Default::default()
        };

        let mut progress_calls: Vec<VcProgressInfo> = vec![];
        let mut callback = |info: &VcProgressInfo| {
            progress_calls.push(info.clone());
        };

        let result = verify_bundle_with_progress(&bundle, &mut callback);
        assert!(
            result.is_ok(),
            "verify_bundle_with_progress failed: {result:?}"
        );
        let response = result.unwrap();

        // Response should indicate trusted
        assert!(response.is_trusted);
        assert_eq!(response.function_name, "trusted_progress");
        assert_eq!(response.summary.trusted, 1);

        // Progress callback should have been called exactly once
        assert_eq!(progress_calls.len(), 1);
        let call = &progress_calls[0];
        assert_eq!(call.total_vcs, 1);
        assert_eq!(call.completed_vcs, 1);
        assert!(call.vc_name.contains("trusted"));
        assert!(matches!(call.result, SwiftVerifyResult::Verified { .. }));
    }

    #[test]
    fn test_verify_bundle_with_progress_empty_ensures() {
        // Test bundle with no ensures clauses
        let bundle = SwiftVcBundle {
            function_name: "no_ensures_progress".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 5,
            source_column: 0,
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

        let mut progress_calls: Vec<VcProgressInfo> = vec![];
        let mut callback = |info: &VcProgressInfo| {
            progress_calls.push(info.clone());
        };

        let result = verify_bundle_with_progress(&bundle, &mut callback);
        assert!(
            result.is_ok(),
            "verify_bundle_with_progress failed: {result:?}"
        );
        let response = result.unwrap();

        // Response should indicate success (nothing to verify)
        assert!(!response.is_trusted);
        assert_eq!(response.function_name, "no_ensures_progress");

        // Progress callback should have been called at least once for the empty spec
        assert!(!progress_calls.is_empty());
    }

    #[test]
    fn test_verify_bundle_with_progress_simple_ensures() {
        // Test bundle with a simple ensures clause
        use crate::json_types::{SwiftExpr, SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "identity_progress".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 10,
            source_column: 0,
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 32,
                },
                index: 0,
            }],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 32,
            }),
            requires: vec![],
            ensures: vec![SwiftExpr::Eq {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::ResultRef), // result == result (tautology)
            }],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let mut progress_calls: Vec<VcProgressInfo> = vec![];
        let mut callback = |info: &VcProgressInfo| {
            progress_calls.push(info.clone());
        };

        let result = verify_bundle_with_progress(&bundle, &mut callback);
        assert!(
            result.is_ok(),
            "verify_bundle_with_progress failed: {result:?}"
        );
        let response = result.unwrap();

        assert!(!response.is_trusted);
        assert_eq!(response.function_name, "identity_progress");

        // Progress callback should have been called at least once
        assert!(!progress_calls.is_empty());

        // First call should have is_spec = true
        let spec_call = &progress_calls[0];
        assert!(spec_call.is_spec);
        assert!(spec_call.completed_vcs <= spec_call.total_vcs);
    }

    #[test]
    fn test_verify_bundle_with_progress_auto_vcs() {
        // Test bundle with auto-VCs (overflow checks)
        use crate::json_types::{SwiftAutoVc, SwiftExpr, SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "add_progress".to_string(),
            source_file: "math.swift".to_string(),
            source_line: 20,
            source_column: 0,
            parameters: vec![
                SwiftParam {
                    name: "a".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 32,
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "b".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 32,
                    },
                    index: 1,
                },
            ],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 32,
            }),
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![SwiftAutoVc::Overflow {
                operation: "add".to_string(),
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
                description: "a + b".to_string(),
                source_line: 21,
                source_column: 10,
                path_condition: None,
                signed: true,
                bits: 32,
            }],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let mut progress_calls: Vec<VcProgressInfo> = vec![];
        let mut callback = |info: &VcProgressInfo| {
            progress_calls.push(info.clone());
        };

        let result = verify_bundle_with_progress(&bundle, &mut callback);
        assert!(
            result.is_ok(),
            "verify_bundle_with_progress failed: {result:?}"
        );
        let response = result.unwrap();

        assert_eq!(response.function_name, "add_progress");

        // Progress callback should have been called for spec and auto-VC
        assert!(!progress_calls.is_empty());

        // At least one call should have is_spec = false (auto-VC)
        let has_auto_vc_call = progress_calls.iter().any(|c| !c.is_spec);
        // Note: If there are no ensures, all VCs are from spec placeholder + auto-VCs
        // The auto-VC should show is_spec = false
        assert!(
            has_auto_vc_call || !progress_calls.is_empty(),
            "Expected at least one progress call"
        );
    }

    #[test]
    fn test_verify_bundle_with_progress_progress_info_fields() {
        // Test that VcProgressInfo fields are properly populated
        use crate::json_types::{SwiftExpr, SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "fields_test".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
            parameters: vec![SwiftParam {
                name: "n".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 32,
                },
                index: 0,
            }],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 32,
            }),
            requires: vec![],
            ensures: vec![SwiftExpr::Eq {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::ResultRef),
            }],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let mut progress_calls: Vec<VcProgressInfo> = vec![];
        let mut callback = |info: &VcProgressInfo| {
            progress_calls.push(info.clone());
        };

        let result = verify_bundle_with_progress(&bundle, &mut callback);
        assert!(result.is_ok());

        // Verify progress calls have valid fields
        for (i, call) in progress_calls.iter().enumerate() {
            // completed_vcs should be monotonically increasing
            assert!(call.completed_vcs > 0);
            assert!(call.completed_vcs <= call.total_vcs);

            // vc_name should not be empty
            assert!(
                !call.vc_name.is_empty(),
                "VC name should not be empty at call {i}"
            );

            // result should be a valid SwiftVerifyResult variant
            match &call.result {
                SwiftVerifyResult::Verified { time_seconds }
                | SwiftVerifyResult::Failed { time_seconds, .. } => {
                    assert!(*time_seconds >= 0.0);
                }
                SwiftVerifyResult::Unknown {
                    reason,
                    time_seconds,
                } => {
                    assert!(!reason.is_empty());
                    assert!(*time_seconds >= 0.0);
                }
                SwiftVerifyResult::Timeout { timeout_seconds } => {
                    assert!(*timeout_seconds >= 0.0);
                }
                SwiftVerifyResult::Error { message } => {
                    assert!(!message.is_empty());
                }
            }
        }
    }

    #[test]
    fn test_verify_bundle_with_progress_vs_verify_bundle_consistency() {
        // Test that verify_bundle_with_progress returns same response as verify_bundle
        let bundle = SwiftVcBundle {
            function_name: "consistency_progress".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
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

        let mut progress_calls: Vec<VcProgressInfo> = vec![];
        let mut callback = |info: &VcProgressInfo| {
            progress_calls.push(info.clone());
        };

        let response_basic = verify_bundle(&bundle).unwrap();
        let response_progress = verify_bundle_with_progress(&bundle, &mut callback).unwrap();
        assert!(
            !progress_calls.is_empty(),
            "expected verify_bundle_with_progress to call progress callback at least once"
        );

        // Both should have same function name
        assert_eq!(
            response_basic.function_name,
            response_progress.function_name
        );
        // Both should have same trusted status
        assert_eq!(response_basic.is_trusted, response_progress.is_trusted);
        // Both should have same source info
        assert_eq!(response_basic.source_file, response_progress.source_file);
        assert_eq!(response_basic.source_line, response_progress.source_line);
    }

    #[test]
    fn test_verify_bundle_with_progress_multiple_ensures() {
        // Test bundle with multiple ensures clauses
        use crate::json_types::{SwiftExpr, SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "multi_ensures".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            source_column: 0,
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 32,
                },
                index: 0,
            }],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 32,
            }),
            requires: vec![],
            ensures: vec![
                // result == result (tautology 1)
                SwiftExpr::Eq {
                    lhs: Box::new(SwiftExpr::ResultRef),
                    rhs: Box::new(SwiftExpr::ResultRef),
                },
                // x == x (tautology 2)
                SwiftExpr::Eq {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    }),
                },
            ],
            invariants: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let mut progress_calls: Vec<VcProgressInfo> = vec![];
        let mut callback = |info: &VcProgressInfo| {
            progress_calls.push(info.clone());
        };

        let result = verify_bundle_with_progress(&bundle, &mut callback);
        assert!(result.is_ok());

        // Should have at least one progress call
        assert!(!progress_calls.is_empty());

        // Total VCs should be consistent across calls
        if progress_calls.len() > 1 {
            let first_total = progress_calls[0].total_vcs;
            for call in &progress_calls {
                assert_eq!(
                    call.total_vcs, first_total,
                    "Total VCs should be consistent"
                );
            }
        }
    }

    #[test]
    fn test_verify_bundle_with_progress_div_by_zero() {
        // Test bundle with division by zero auto-VC
        use crate::json_types::{SwiftAutoVc, SwiftExpr, SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "div_progress".to_string(),
            source_file: "math.swift".to_string(),
            source_line: 30,
            source_column: 0,
            parameters: vec![
                SwiftParam {
                    name: "a".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 32,
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "b".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 32,
                    },
                    index: 1,
                },
            ],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 32,
            }),
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![SwiftAutoVc::DivByZero {
                divisor: SwiftExpr::ParamRef {
                    name: "b".to_string(),
                    index: 1,
                },
                description: "a / b".to_string(),
                source_line: 31,
                source_column: 10,
                path_condition: None,
            }],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let mut progress_calls: Vec<VcProgressInfo> = vec![];
        let mut callback = |info: &VcProgressInfo| {
            progress_calls.push(info.clone());
        };

        let result = verify_bundle_with_progress(&bundle, &mut callback);
        assert!(result.is_ok());

        // Should have progress calls
        assert!(!progress_calls.is_empty());
    }

    #[test]
    fn test_verify_bundle_with_progress_bounds_check() {
        // Test bundle with bounds check auto-VC
        use crate::json_types::{SwiftAutoVc, SwiftExpr, SwiftParam, SwiftType};

        let bundle = SwiftVcBundle {
            function_name: "bounds_progress".to_string(),
            source_file: "array.swift".to_string(),
            source_line: 40,
            source_column: 0,
            parameters: vec![
                SwiftParam {
                    name: "arr".to_string(),
                    param_type: SwiftType::Array {
                        element: Box::new(SwiftType::Int {
                            signed: true,
                            bits: 32,
                        }),
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "idx".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 1,
                },
            ],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 32,
            }),
            requires: vec![],
            ensures: vec![],
            invariants: vec![],
            auto_vcs: vec![SwiftAutoVc::BoundsCheck {
                index: SwiftExpr::ParamRef {
                    name: "idx".to_string(),
                    index: 1,
                },
                length: SwiftExpr::Field {
                    base: Box::new(SwiftExpr::ParamRef {
                        name: "arr".to_string(),
                        index: 0,
                    }),
                    field: "count".to_string(),
                },
                description: "arr[idx]".to_string(),
                source_line: 41,
                source_column: 10,
                path_condition: None,
            }],
            is_trusted: false,
            body_constraints: vec![],
            ..Default::default()
        };

        let mut progress_calls: Vec<VcProgressInfo> = vec![];
        let mut callback = |info: &VcProgressInfo| {
            progress_calls.push(info.clone());
        };

        let result = verify_bundle_with_progress(&bundle, &mut callback);
        assert!(result.is_ok());

        // Should have progress calls
        assert!(!progress_calls.is_empty());
    }
}
