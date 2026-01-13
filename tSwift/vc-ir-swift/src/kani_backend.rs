//! Kani backend support (prototype).
//!
//! This module currently provides a Kani harness exporter for a subset of VC IR.
//! The generated Rust code is intended to be compiled/checked by the `kani` tool.
//!
//! ## Bitvector Mode (v351)
//!
//! By default, integer parameters use `i128` with bounds assumptions. This is
//! sound but doesn't model exact overflow semantics (e.g., wrapping behavior).
//!
//! In **bitvector mode**, integers map to native Rust types (i8, i16, i32, i64,
//! u8, u16, u32, u64) which Kani can verify with exact overflow semantics.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;

use thiserror::Error;

use crate::types::{Expr, FunctionSignature, Predicate, VcKind, VcType, VerificationCondition};

/// Configuration for Kani harness export.
#[derive(Debug, Clone, Default)]
pub struct KaniExportConfig {
    /// When true, use native Rust integer types (i8, i16, i32, i64, etc.) instead
    /// of i128 with bounds assumptions. This enables exact bitvector overflow
    /// semantics in Kani verification.
    pub bitvector_mode: bool,
    /// Optional preconditions from @_requires annotations.
    /// When provided, these are emitted as `kani::assume()` calls to constrain
    /// the symbolic inputs to only values satisfying the function's contract.
    pub preconditions: Vec<Predicate>,
    /// Optional postconditions from @_ensures annotations.
    /// When provided, these are emitted as `kani::assert()` calls to verify
    /// the function result satisfies the output contract.
    pub postconditions: Vec<Predicate>,
}

/// Errors that can occur during Kani harness export.
#[derive(Debug, Error)]
pub enum KaniExportError {
    #[error("unsupported VC IR construct for Kani export: {0}")]
    Unsupported(&'static str),

    #[error("VC references unknown variable `{0}` (not in function parameters)")]
    UnknownVariable(String),

    #[error("unsupported parameter type for Kani export: `{0}`")]
    UnsupportedParamType(String),
}

/// Tracked struct field access: (`base_var_name`, `field_name`).
/// e.g., arr.count -> ("arr", "count")
type StructFieldRef = (String, String);

/// Tracked array access: `base_var_name`
/// e.g., `arr[i]` -> "arr"
type ArrayAccessRef = String;

/// Tracked old value reference: `var_name`
/// e.g., old(x) -> "x"
/// Used for postconditions that reference entry values of parameters.
type OldValueRef = String;

/// Map a `VcType` to its native Rust integer type name.
/// Returns None if the type is not a supported integer type.
const fn vctype_to_rust_native(ty: &VcType) -> Option<&'static str> {
    match ty {
        VcType::Int { signed, bits } => match (*signed, *bits) {
            (true, 8) => Some("i8"),
            (true, 16) => Some("i16"),
            (true, 32) => Some("i32"),
            (true, 64) => Some("i64"),
            (true, 128) => Some("i128"),
            (false, 8) => Some("u8"),
            (false, 16) => Some("u16"),
            (false, 32) => Some("u32"),
            (false, 64) => Some("u64"),
            (false, 128) => Some("u128"),
            // For non-standard bit widths, fall back to next larger type
            (true, b) if b <= 8 => Some("i8"),
            (true, b) if b <= 16 => Some("i16"),
            (true, b) if b <= 32 => Some("i32"),
            (true, b) if b <= 64 => Some("i64"),
            (true, _) => Some("i128"),
            (false, b) if b <= 8 => Some("u8"),
            (false, b) if b <= 16 => Some("u16"),
            (false, b) if b <= 32 => Some("u32"),
            (false, b) if b <= 64 => Some("u64"),
            (false, _) => Some("u128"),
        },
        _ => None,
    }
}

/// Export a single VC as a standalone Kani proof harness.
///
/// Notes:
/// - This is a prototype exporter intended for debugging/experimentation.
/// - Only a subset of VC IR is supported (primarily int/bool arithmetic and predicates).
/// - The returned string is *not* compiled by this crate; it is meant for the `kani` tool.
///
/// # Errors
/// Returns an error if the VC contains unsupported constructs or required information cannot be
/// extracted for harness generation.
pub fn export_vc_to_kani_harness(
    signature: &FunctionSignature,
    vc: &VerificationCondition,
) -> Result<String, KaniExportError> {
    export_vc_to_kani_harness_with_config(signature, vc, &KaniExportConfig::default())
}

/// Export a single VC as a standalone Kani proof harness with configuration.
///
/// With `config.bitvector_mode = true`, integers use native Rust types (i8, i16, i32, i64)
/// instead of i128 with bounds assumptions, enabling exact overflow semantics verification.
///
/// # Errors
/// Returns an error if the VC contains unsupported constructs or required information cannot be
/// extracted for harness generation.
///
/// # Panics
/// Panics if internal variable maps are inconsistent (a collected variable is missing from
/// `var_map` or `param_type_map`). This indicates a bug in variable collection.
#[allow(clippy::too_many_lines)]
pub fn export_vc_to_kani_harness_with_config(
    signature: &FunctionSignature,
    vc: &VerificationCondition,
    config: &KaniExportConfig,
) -> Result<String, KaniExportError> {
    let mut referenced_vars: BTreeSet<String> = BTreeSet::new();
    let mut struct_fields: BTreeSet<StructFieldRef> = BTreeSet::new();
    let mut array_accesses: BTreeSet<ArrayAccessRef> = BTreeSet::new();
    let mut old_refs: BTreeSet<OldValueRef> = BTreeSet::new();
    let mut uses_result = false;
    collect_vars_from_vc(
        &vc.condition,
        &mut referenced_vars,
        &mut struct_fields,
        &mut array_accesses,
        &mut old_refs,
        &mut uses_result,
    )?;

    // Also collect variables from preconditions (v354)
    for precond in &config.preconditions {
        collect_vars_from_predicate(
            precond,
            &mut referenced_vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )?;
    }

    // Also collect variables from postconditions (v355)
    for postcond in &config.postconditions {
        collect_vars_from_predicate(
            postcond,
            &mut referenced_vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )?;
    }

    let param_type_map: HashMap<String, VcType> = signature
        .params
        .iter()
        .map(|(name, ty)| (name.clone(), ty.clone()))
        .collect();

    for var in &referenced_vars {
        if !param_type_map.contains_key(var) {
            return Err(KaniExportError::UnknownVariable(var.clone()));
        }
    }

    let mut var_map: HashMap<String, String> = HashMap::new();
    let mut used_idents: HashSet<String> = HashSet::new();
    for var in &referenced_vars {
        let ident = unique_sanitized_ident(var, &mut used_idents);
        var_map.insert(var.clone(), ident);
    }

    let harness_name = unique_sanitized_ident(&format!("proof_{}", vc.name), &mut used_idents);

    // Create rendering context for expression/predicate rendering
    let render_ctx = RenderContext {
        bitvector_mode: config.bitvector_mode,
    };

    let mut out = String::new();
    out.push_str("// Auto-generated by vc-ir-swift Kani exporter\n");
    out.push_str("// NOTE: This harness is a prototype; review before relying on results.\n");
    if config.bitvector_mode {
        out.push_str(
            "// MODE: Bitvector (native Rust integer types for exact overflow semantics)\n",
        );
    } else {
        out.push_str("// MODE: Unbounded (i128 with bounds assumptions)\n");
    }
    out.push('\n');
    out.push_str("#![allow(unused_imports)]\n");
    out.push_str("#![allow(unused_variables)]\n");
    out.push_str("#![allow(non_snake_case)]\n\n");
    out.push_str("extern crate kani;\n\n");
    let _ = writeln!(
        out,
        "// VC: {}\n// Source: {}:{}\n",
        vc.name,
        vc.span.file.as_ref(),
        vc.span.line_start
    );
    out.push_str("#[kani::proof]\n");
    let _ = writeln!(out, "fn {harness_name}() {{");

    // Declare referenced parameters.
    for var in &referenced_vars {
        let ident = var_map.get(var).expect("var_map must contain var");
        let ty = param_type_map
            .get(var)
            .expect("param_type_map must contain var");
        emit_symbolic_var(&mut out, ident, ty, config.bitvector_mode)?;
    }

    // If the VC references `result`, declare it as unconstrained (typed by return type).
    if uses_result {
        emit_symbolic_var(
            &mut out,
            "result",
            &signature.return_type,
            config.bitvector_mode,
        )?;
    }

    // Declare synthetic variables for struct field accesses (.count, .hasValue).
    for (base_var, field) in &struct_fields {
        let base_ident = var_map
            .get(base_var)
            .cloned()
            .unwrap_or_else(|| sanitize_ident(base_var));
        match field.as_str() {
            "count" => {
                // Array count: non-negative integer
                let synth_ident = format!("{base_ident}_count");
                if config.bitvector_mode {
                    // Use i64 for array count in bitvector mode to match Swift Int semantics.
                    // (Using usize would require extra casts in predicates like idx < arr.count.)
                    let _ = writeln!(out, "    let {synth_ident}: i64 = kani::any();");
                    let _ = writeln!(out, "    kani::assume({synth_ident} >= 0);");
                } else {
                    let _ = writeln!(out, "    let {synth_ident}: i128 = kani::any();");
                    let _ = writeln!(out, "    kani::assume({synth_ident} >= 0i128);");
                }
            }
            "hasValue" => {
                // Optional hasValue: boolean
                let synth_ident = format!("{base_ident}_has_value");
                let _ = writeln!(out, "    let {synth_ident}: bool = kani::any();");
            }
            _ => {
                // Should not reach here; collect_vars_from_expr filters unsupported fields.
            }
        }
    }

    // Declare synthetic variables for array element accesses.
    // The actual element value is unconstrained; bounds check VCs verify the index is in range.
    for arr_var in &array_accesses {
        let arr_ident = var_map
            .get(arr_var)
            .cloned()
            .unwrap_or_else(|| sanitize_ident(arr_var));
        let synth_ident = format!("{arr_ident}_elem");
        if config.bitvector_mode {
            // Use i64 as a reasonable default element type in bitvector mode
            let _ = writeln!(out, "    let {synth_ident}: i64 = kani::any();");
        } else {
            let _ = writeln!(out, "    let {synth_ident}: i128 = kani::any();");
        }
    }

    // Declare old_x variables for old() references in postconditions (v357).
    // These capture the entry value of the parameter at function call time.
    // In the Kani harness, they're just copies of the parameter (before any mutation).
    for old_var in &old_refs {
        let base_ident = var_map
            .get(old_var)
            .cloned()
            .unwrap_or_else(|| sanitize_ident(old_var));
        let old_ident = format!("old_{base_ident}");
        let ty = param_type_map.get(old_var);
        match ty {
            Some(VcType::Int { .. }) => {
                if config.bitvector_mode {
                    let rust_type = vctype_to_rust_native(ty.unwrap()).unwrap_or("i128");
                    let _ = writeln!(
                        out,
                        "    let {old_ident}: {rust_type} = {base_ident}; // entry value"
                    );
                } else {
                    let _ = writeln!(
                        out,
                        "    let {old_ident}: i128 = {base_ident}; // entry value"
                    );
                }
            }
            Some(VcType::Bool) => {
                let _ = writeln!(
                    out,
                    "    let {old_ident}: bool = {base_ident}; // entry value"
                );
            }
            Some(VcType::Float { bits }) => {
                let rust_type = if *bits <= 32 { "f32" } else { "f64" };
                let _ = writeln!(
                    out,
                    "    let {old_ident}: {rust_type} = {base_ident}; // entry value"
                );
            }
            _ => {
                // For unknown types, use generic i128
                let _ = writeln!(
                    out,
                    "    let {old_ident}: i128 = {base_ident}; // entry value"
                );
            }
        }
    }

    out.push('\n');

    // Emit preconditions as kani::assume() calls (v354)
    // This constrains symbolic inputs to satisfy the function's @_requires contract.
    if !config.preconditions.is_empty() {
        out.push_str("    // Preconditions (@_requires)\n");
        for (i, precond) in config.preconditions.iter().enumerate() {
            let precond_rendered = render_predicate(precond, &var_map, render_ctx)?;
            let _ = writeln!(
                out,
                "    kani::assume({precond_rendered}); // precondition {}",
                i + 1
            );
        }
        out.push('\n');
    }

    // Emit assertions using Kani function API (not macros).
    // kani::assert(cond, "message") is the current API as of Kani 0.66+.
    let vc_desc = escape_string_for_rust(&vc.name);
    match &vc.condition {
        VcKind::Predicate(p) => {
            // In bitvector mode, try to detect arithmetic overflow patterns and use
            // checked_add/checked_sub/etc. instead of wrapping operations with range checks.
            // This fixes the bug where wrapping arithmetic always produces in-range results.
            let pred =
                if let Some(overflow_check) = try_render_overflow_check(p, &var_map, render_ctx) {
                    overflow_check?
                } else {
                    render_predicate(p, &var_map, render_ctx)?
                };
            let _ = writeln!(out, "    kani::assert({pred}, \"{vc_desc}\");");
        }
        VcKind::Implies {
            antecedent,
            consequent,
        } => {
            let ant = render_predicate(antecedent, &var_map, render_ctx)?;
            // Try to detect overflow pattern in the consequent
            let cons = if let Some(overflow_check) =
                try_render_overflow_check(consequent, &var_map, render_ctx)
            {
                overflow_check?
            } else {
                render_predicate(consequent, &var_map, render_ctx)?
            };
            let _ = writeln!(
                out,
                "    kani::assert(!({ant}) || ({cons}), \"{vc_desc}\");"
            );
        }
        VcKind::Termination {
            measure,
            initial_measure,
            next_measure,
            ..
        } => {
            if let Some(init) = initial_measure {
                let init_s = render_expr(init, &var_map, render_ctx)?;
                let _ = writeln!(
                    out,
                    "    kani::assert({init_s} >= 0, \"{vc_desc}: initial measure >= 0\");"
                );
            }
            let measure_s = render_expr(measure, &var_map, render_ctx)?;
            let _ = writeln!(
                out,
                "    kani::assert({measure_s} >= 0, \"{vc_desc}: measure >= 0\");"
            );
            let next_s = render_expr(next_measure, &var_map, render_ctx)?;
            let _ = writeln!(
                out,
                "    kani::assert({next_s} < {measure_s}, \"{vc_desc}: measure decreases\");"
            );
        }
    }

    // Emit postconditions as kani::assert() calls (v355)
    // This verifies the function result satisfies the @_ensures contract.
    if !config.postconditions.is_empty() {
        out.push('\n');
        out.push_str("    // Postconditions (@_ensures)\n");
        for (i, postcond) in config.postconditions.iter().enumerate() {
            let postcond_rendered = render_predicate(postcond, &var_map, render_ctx)?;
            let _ = writeln!(
                out,
                "    kani::assert({postcond_rendered}, \"postcondition {}\"); // @_ensures",
                i + 1
            );
        }
    }

    out.push_str("}\n");
    Ok(out)
}

const fn int_bounds(ty: &VcType) -> Result<(i128, i128), KaniExportError> {
    match ty {
        VcType::Int { signed, bits } => {
            let bits_u32 = *bits;
            if bits_u32 == 0 || bits_u32 > 128 {
                return Err(KaniExportError::Unsupported("int bitwidth"));
            }
            if *signed {
                let max = (1_i128 << (bits_u32 - 1)) - 1;
                let min = -(1_i128 << (bits_u32 - 1));
                Ok((min, max))
            } else {
                let max = (1_i128 << bits_u32) - 1;
                Ok((0, max))
            }
        }
        _ => Err(KaniExportError::Unsupported("non-int bounds")),
    }
}

fn collect_vars_from_vc(
    vc: &VcKind,
    vars: &mut BTreeSet<String>,
    struct_fields: &mut BTreeSet<StructFieldRef>,
    array_accesses: &mut BTreeSet<ArrayAccessRef>,
    old_refs: &mut BTreeSet<OldValueRef>,
    uses_result: &mut bool,
) -> Result<(), KaniExportError> {
    match vc {
        VcKind::Predicate(p) => collect_vars_from_predicate(
            p,
            vars,
            struct_fields,
            array_accesses,
            old_refs,
            uses_result,
        ),
        VcKind::Implies {
            antecedent,
            consequent,
        } => {
            collect_vars_from_predicate(
                antecedent,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )?;
            collect_vars_from_predicate(
                consequent,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )
        }
        VcKind::Termination {
            measure,
            initial_measure,
            next_measure,
            ..
        } => {
            collect_vars_from_expr(
                measure,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )?;
            if let Some(init) = initial_measure {
                collect_vars_from_expr(
                    init,
                    vars,
                    struct_fields,
                    array_accesses,
                    old_refs,
                    uses_result,
                )?;
            }
            collect_vars_from_expr(
                next_measure,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )
        }
    }
}

fn collect_vars_from_predicate(
    pred: &Predicate,
    vars: &mut BTreeSet<String>,
    struct_fields: &mut BTreeSet<StructFieldRef>,
    array_accesses: &mut BTreeSet<ArrayAccessRef>,
    old_refs: &mut BTreeSet<OldValueRef>,
    uses_result: &mut bool,
) -> Result<(), KaniExportError> {
    match pred {
        Predicate::Expr(e) => collect_vars_from_expr(
            e,
            vars,
            struct_fields,
            array_accesses,
            old_refs,
            uses_result,
        ),
        Predicate::And(ps) | Predicate::Or(ps) => {
            for p in ps {
                collect_vars_from_predicate(
                    p,
                    vars,
                    struct_fields,
                    array_accesses,
                    old_refs,
                    uses_result,
                )?;
            }
            Ok(())
        }
        Predicate::Not(p) => collect_vars_from_predicate(
            p,
            vars,
            struct_fields,
            array_accesses,
            old_refs,
            uses_result,
        ),
        Predicate::Implies(a, b) => {
            collect_vars_from_predicate(
                a,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )?;
            collect_vars_from_predicate(
                b,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )
        }
    }
}

#[allow(clippy::too_many_lines)]
fn collect_vars_from_expr(
    expr: &Expr,
    vars: &mut BTreeSet<String>,
    struct_fields: &mut BTreeSet<StructFieldRef>,
    array_accesses: &mut BTreeSet<ArrayAccessRef>,
    old_refs: &mut BTreeSet<OldValueRef>,
    uses_result: &mut bool,
) -> Result<(), KaniExportError> {
    match expr {
        Expr::IntLit(_) | Expr::BoolLit(_) => Ok(()),
        Expr::NilLit => Err(KaniExportError::Unsupported("NilLit")),
        Expr::Var(name) => {
            vars.insert(name.clone());
            Ok(())
        }
        Expr::Result => {
            *uses_result = true;
            Ok(())
        }
        Expr::Old(inner) => collect_vars_from_expr_in_old_context(
            inner,
            vars,
            struct_fields,
            array_accesses,
            old_refs,
            uses_result,
        ),

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
            collect_vars_from_expr(
                a,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )?;
            collect_vars_from_expr(
                b,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )
        }
        Expr::Neg(a) | Expr::Not(a) => collect_vars_from_expr(
            a,
            vars,
            struct_fields,
            array_accesses,
            old_refs,
            uses_result,
        ),
        Expr::Ite { cond, then_, else_ } => {
            collect_vars_from_expr(
                cond,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )?;
            collect_vars_from_expr(
                then_,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )?;
            collect_vars_from_expr(
                else_,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )
        }
        Expr::ArrayIndex(arr, idx) => {
            // Track array access for synthetic element variable declaration
            if let Expr::Var(arr_name) = arr.as_ref() {
                array_accesses.insert(arr_name.clone());
            }
            collect_vars_from_expr(
                arr,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )?;
            collect_vars_from_expr(
                idx,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )
        }
        Expr::StructField(base, field) => {
            // For supported fields (.count, .hasValue), record the field access and collect vars from base.
            // This allows BoundsCheck and NilCheck VCs to be exported.
            match field.as_str() {
                "count" | "hasValue" => {
                    // Extract base variable name for struct field tracking
                    if let Expr::Var(base_name) = base.as_ref() {
                        struct_fields.insert((base_name.clone(), field.clone()));
                    }
                    collect_vars_from_expr(
                        base,
                        vars,
                        struct_fields,
                        array_accesses,
                        old_refs,
                        uses_result,
                    )
                }
                _ => Err(KaniExportError::Unsupported(
                    "StructField (unsupported field)",
                )),
            }
        }
        Expr::Apply { .. } => Err(KaniExportError::Unsupported("Apply")),
        Expr::Forall { .. } => Err(KaniExportError::Unsupported("Forall")),
        Expr::Exists { .. } => Err(KaniExportError::Unsupported("Exists")),
    }
}

fn collect_vars_from_expr_in_old_context(
    expr: &Expr,
    vars: &mut BTreeSet<String>,
    struct_fields: &mut BTreeSet<StructFieldRef>,
    array_accesses: &mut BTreeSet<ArrayAccessRef>,
    old_refs: &mut BTreeSet<OldValueRef>,
    uses_result: &mut bool,
) -> Result<(), KaniExportError> {
    match expr {
        Expr::IntLit(_) | Expr::BoolLit(_) => Ok(()),
        Expr::NilLit => Err(KaniExportError::Unsupported("NilLit")),
        Expr::Var(name) => {
            vars.insert(name.clone());
            old_refs.insert(name.clone());
            Ok(())
        }
        Expr::Result => Err(KaniExportError::Unsupported("Old(Result)")),
        Expr::Old(inner) => collect_vars_from_expr_in_old_context(
            inner,
            vars,
            struct_fields,
            array_accesses,
            old_refs,
            uses_result,
        ),

        // We model struct fields/array access as synthetic immutable variables, so they already
        // behave like "entry values" in the Kani harness; no need for old_ copies.
        Expr::ArrayIndex(_, _) | Expr::StructField(_, _) => collect_vars_from_expr(
            expr,
            vars,
            struct_fields,
            array_accesses,
            old_refs,
            uses_result,
        ),

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
            collect_vars_from_expr_in_old_context(
                a,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )?;
            collect_vars_from_expr_in_old_context(
                b,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )
        }
        Expr::Neg(a) | Expr::Not(a) => collect_vars_from_expr_in_old_context(
            a,
            vars,
            struct_fields,
            array_accesses,
            old_refs,
            uses_result,
        ),
        Expr::Ite { cond, then_, else_ } => {
            collect_vars_from_expr_in_old_context(
                cond,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )?;
            collect_vars_from_expr_in_old_context(
                then_,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )?;
            collect_vars_from_expr_in_old_context(
                else_,
                vars,
                struct_fields,
                array_accesses,
                old_refs,
                uses_result,
            )
        }
        Expr::Apply { .. } => Err(KaniExportError::Unsupported("Apply")),
        Expr::Forall { .. } => Err(KaniExportError::Unsupported("Forall")),
        Expr::Exists { .. } => Err(KaniExportError::Unsupported("Exists")),
    }
}

/// Context for rendering expressions, controls arithmetic mode.
/// Emit a symbolic variable declaration (`let var: Type = kani::any();`) with optional bounds.
///
/// This helper centralizes the repeated pattern of emitting variable declarations for
/// different `VcType` variants in both bitvector and default modes.
fn emit_symbolic_var(
    out: &mut String,
    var_name: &str,
    ty: &VcType,
    bitvector_mode: bool,
) -> Result<(), KaniExportError> {
    match ty {
        VcType::Int { .. } => {
            if bitvector_mode {
                let rust_type = vctype_to_rust_native(ty).unwrap_or("i128");
                let _ = writeln!(out, "    let {var_name}: {rust_type} = kani::any();");
            } else {
                let _ = writeln!(out, "    let {var_name}: i128 = kani::any();");
                let (min, max) = int_bounds(ty)?;
                let _ = writeln!(
                    out,
                    "    kani::assume({var_name} >= {min} && {var_name} <= {max});"
                );
            }
        }
        VcType::Bool => {
            let _ = writeln!(out, "    let {var_name}: bool = kani::any();");
        }
        VcType::Float { bits } => {
            let rust_type = if *bits <= 32 { "f32" } else { "f64" };
            let _ = writeln!(out, "    let {var_name}: {rust_type} = kani::any();");
            let _ = writeln!(
                out,
                "    // Note: {var_name} is symbolic; float arithmetic not verified"
            );
        }
        other => {
            return Err(KaniExportError::UnsupportedParamType(format!("{other:?}")));
        }
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
struct RenderContext {
    /// When true, use wrapping arithmetic methods to avoid Rust overflow panics.
    /// This allows Kani to explore the full state space including overflow scenarios.
    bitvector_mode: bool,
}

/// Arithmetic operation type for overflow detection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Neg,
}

impl ArithOp {
    /// Return the checked method name for this operation.
    const fn checked_method(self) -> &'static str {
        match self {
            Self::Add => "checked_add",
            Self::Sub => "checked_sub",
            Self::Mul => "checked_mul",
            Self::Div => "checked_div",
            Self::Rem => "checked_rem",
            Self::Neg => "checked_neg",
        }
    }
}

/// Try to detect an arithmetic overflow VC pattern in a predicate.
///
/// Overflow VCs have the structure: `arith_result >= MIN && arith_result <= MAX`
/// where `arith_result` is an arithmetic operation (Add, Sub, Mul, Div, Rem, Neg).
///
/// In bitvector mode, we convert this to `a.checked_op(b).is_some()` which correctly
/// detects overflow using Rust's checked arithmetic, rather than using wrapping
/// arithmetic which always produces in-range results.
///
/// Returns `Some(rust_code)` if the pattern is detected, None otherwise.
fn try_render_overflow_check(
    pred: &Predicate,
    var_map: &HashMap<String, String>,
    ctx: RenderContext,
) -> Option<Result<String, KaniExportError>> {
    if !ctx.bitvector_mode {
        return None;
    }

    // Pattern: And([Ge(arith_expr, IntLit(MIN)), Le(arith_expr, IntLit(MAX))])
    // Or:      Expr(And(Ge(arith_expr, IntLit(MIN)), Le(arith_expr, IntLit(MAX))))

    let and_expr = match pred {
        Predicate::Expr(e) => e,
        Predicate::And(ps) if ps.len() == 2 => {
            // Try to match And([Predicate::Expr(ge), Predicate::Expr(le)])
            if let (Predicate::Expr(e1), Predicate::Expr(e2)) = (&ps[0], &ps[1]) {
                return try_render_overflow_check_from_exprs(e1, e2, var_map);
            }
            return None;
        }
        _ => return None,
    };

    // The and_expr should be: And(ge_expr, le_expr)
    if let Expr::And(ge_expr, le_expr) = and_expr {
        return try_render_overflow_check_from_exprs(ge_expr, le_expr, var_map);
    }

    None
}

/// Helper to detect overflow pattern from two expressions (ge and le bounds).
fn try_render_overflow_check_from_exprs(
    ge_expr: &Expr,
    le_expr: &Expr,
    var_map: &HashMap<String, String>,
) -> Option<Result<String, KaniExportError>> {
    // ge_expr should be: Ge(arith_expr, IntLit(MIN))
    // le_expr should be: Le(arith_expr, IntLit(MAX))

    let arith_expr1 = match ge_expr {
        Expr::Ge(left, right) => {
            if matches!(right.as_ref(), Expr::IntLit(_)) {
                left.as_ref()
            } else {
                return None;
            }
        }
        _ => return None,
    };

    let arith_expr2 = match le_expr {
        Expr::Le(left, right) => {
            if matches!(right.as_ref(), Expr::IntLit(_)) {
                left.as_ref()
            } else {
                return None;
            }
        }
        _ => return None,
    };

    // Both should reference the same arithmetic expression
    // For simplicity, we check structural equality
    if !exprs_structurally_equal(arith_expr1, arith_expr2) {
        return None;
    }

    // Extract the operation and operands
    let (op, operands) = extract_arith_op(arith_expr1)?;

    Some(render_checked_overflow(op, &operands, var_map))
}

/// Check if two expressions are structurally equal.
fn exprs_structurally_equal(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::IntLit(x), Expr::IntLit(y)) => x == y,
        (Expr::BoolLit(x), Expr::BoolLit(y)) => x == y,
        (Expr::NilLit, Expr::NilLit) | (Expr::Result, Expr::Result) => true,
        (Expr::Var(x), Expr::Var(y)) => x == y,
        (Expr::Old(x), Expr::Old(y)) | (Expr::Neg(x), Expr::Neg(y)) => {
            exprs_structurally_equal(x, y)
        }
        (Expr::Add(a1, a2), Expr::Add(b1, b2))
        | (Expr::Sub(a1, a2), Expr::Sub(b1, b2))
        | (Expr::Mul(a1, a2), Expr::Mul(b1, b2))
        | (Expr::Div(a1, a2), Expr::Div(b1, b2))
        | (Expr::Rem(a1, a2), Expr::Rem(b1, b2)) => {
            exprs_structurally_equal(a1, b1) && exprs_structurally_equal(a2, b2)
        }
        _ => false, // For other cases, assume not equal (conservative)
    }
}

/// Extract arithmetic operation and operands from an expression.
fn extract_arith_op(expr: &Expr) -> Option<(ArithOp, Vec<&Expr>)> {
    match expr {
        Expr::Add(a, b) => Some((ArithOp::Add, vec![a.as_ref(), b.as_ref()])),
        Expr::Sub(a, b) => Some((ArithOp::Sub, vec![a.as_ref(), b.as_ref()])),
        Expr::Mul(a, b) => Some((ArithOp::Mul, vec![a.as_ref(), b.as_ref()])),
        Expr::Div(a, b) => Some((ArithOp::Div, vec![a.as_ref(), b.as_ref()])),
        Expr::Rem(a, b) => Some((ArithOp::Rem, vec![a.as_ref(), b.as_ref()])),
        Expr::Neg(a) => Some((ArithOp::Neg, vec![a.as_ref()])),
        _ => None,
    }
}

/// Render a checked overflow assertion for bitvector mode.
/// Instead of `(a + b) >= MIN && (a + b) <= MAX` (always true with wrapping),
/// we generate `a.checked_add(b).is_some()` which correctly detects overflow.
fn render_checked_overflow(
    op: ArithOp,
    operands: &[&Expr],
    var_map: &HashMap<String, String>,
) -> Result<String, KaniExportError> {
    // Use non-bitvector context for rendering operands (we want direct values)
    let ctx = RenderContext {
        bitvector_mode: false,
    };

    // First operand is used in both branches
    let a = render_expr(operands[0], var_map, ctx)?;

    if op == ArithOp::Neg {
        // Unary: a.checked_neg().is_some()
        Ok(format!("({a}).checked_neg().is_some()"))
    } else {
        // Binary: a.checked_op(b).is_some()
        let b = render_expr(operands[1], var_map, ctx)?;
        let method = op.checked_method();
        Ok(format!("({a}).{method}({b}).is_some()"))
    }
}

fn render_predicate(
    pred: &Predicate,
    var_map: &HashMap<String, String>,
    ctx: RenderContext,
) -> Result<String, KaniExportError> {
    match pred {
        Predicate::Expr(e) => render_expr(e, var_map, ctx),
        Predicate::And(ps) => {
            let mut rendered = Vec::with_capacity(ps.len());
            for p in ps {
                rendered.push(render_predicate(p, var_map, ctx)?);
            }
            Ok(join_bool("&&", rendered))
        }
        Predicate::Or(ps) => {
            let mut rendered = Vec::with_capacity(ps.len());
            for p in ps {
                rendered.push(render_predicate(p, var_map, ctx)?);
            }
            Ok(join_bool("||", rendered))
        }
        Predicate::Not(p) => Ok(format!("!({})", render_predicate(p, var_map, ctx)?)),
        Predicate::Implies(a, b) => {
            let a_s = render_predicate(a, var_map, ctx)?;
            let b_s = render_predicate(b, var_map, ctx)?;
            Ok(format!("(!({a_s})) || ({b_s})"))
        }
    }
}

fn join_bool(op: &str, parts: Vec<String>) -> String {
    if parts.is_empty() {
        "true".to_string()
    } else if parts.len() == 1 {
        parts.into_iter().next().unwrap()
    } else {
        format!("({})", parts.join(&format!(" {op} ")))
    }
}

#[allow(clippy::too_many_lines)]
fn render_expr(
    expr: &Expr,
    var_map: &HashMap<String, String>,
    ctx: RenderContext,
) -> Result<String, KaniExportError> {
    match expr {
        // Keep integer literals unsuffixed so they can be inferred to the surrounding Rust integer
        // type (i128 in default mode, native types in bitvector mode).
        Expr::IntLit(v) => Ok(format!("{v}")),
        Expr::BoolLit(v) => Ok(v.to_string()),
        Expr::NilLit => Err(KaniExportError::Unsupported("NilLit")),
        Expr::Var(name) => Ok(var_map.get(name).cloned().unwrap_or_else(|| name.clone())),
        Expr::Result => Ok("result".to_string()),
        Expr::Old(inner) => render_expr_in_old_context(inner, var_map, ctx),

        // Arithmetic operators: use wrapping methods in bitvector mode to avoid Rust overflow panics.
        // This allows Kani to explore the full state space including overflow scenarios.
        Expr::Add(a, b) => {
            let a_s = render_expr(a, var_map, ctx)?;
            let b_s = render_expr(b, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_add({b_s})"))
            } else {
                Ok(format!("({a_s} + {b_s})"))
            }
        }
        Expr::Sub(a, b) => {
            let a_s = render_expr(a, var_map, ctx)?;
            let b_s = render_expr(b, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_sub({b_s})"))
            } else {
                Ok(format!("({a_s} - {b_s})"))
            }
        }
        Expr::Mul(a, b) => {
            let a_s = render_expr(a, var_map, ctx)?;
            let b_s = render_expr(b, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_mul({b_s})"))
            } else {
                Ok(format!("({a_s} * {b_s})"))
            }
        }
        Expr::Div(a, b) => {
            // Division: use wrapping_div in bitvector mode to handle MIN / -1 overflow.
            // Division by zero is still caught by Kani/Rust.
            let a_s = render_expr(a, var_map, ctx)?;
            let b_s = render_expr(b, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_div({b_s})"))
            } else {
                Ok(format!("({a_s} / {b_s})"))
            }
        }
        Expr::Rem(a, b) => {
            // Remainder: use wrapping_rem in bitvector mode to handle MIN % -1 overflow.
            let a_s = render_expr(a, var_map, ctx)?;
            let b_s = render_expr(b, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_rem({b_s})"))
            } else {
                Ok(format!("({a_s} % {b_s})"))
            }
        }
        Expr::Neg(a) => {
            // Negation: use wrapping_neg in bitvector mode to handle MIN.wrapping_neg() -> MIN.
            let a_s = render_expr(a, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_neg()"))
            } else {
                Ok(format!("-({a_s})"))
            }
        }

        Expr::Eq(a, b) => Ok(format!(
            "({} == {})",
            render_expr(a, var_map, ctx)?,
            render_expr(b, var_map, ctx)?
        )),
        Expr::Ne(a, b) => Ok(format!(
            "({} != {})",
            render_expr(a, var_map, ctx)?,
            render_expr(b, var_map, ctx)?
        )),
        Expr::Lt(a, b) => Ok(format!(
            "({} < {})",
            render_expr(a, var_map, ctx)?,
            render_expr(b, var_map, ctx)?
        )),
        Expr::Le(a, b) => Ok(format!(
            "({} <= {})",
            render_expr(a, var_map, ctx)?,
            render_expr(b, var_map, ctx)?
        )),
        Expr::Gt(a, b) => Ok(format!(
            "({} > {})",
            render_expr(a, var_map, ctx)?,
            render_expr(b, var_map, ctx)?
        )),
        Expr::Ge(a, b) => Ok(format!(
            "({} >= {})",
            render_expr(a, var_map, ctx)?,
            render_expr(b, var_map, ctx)?
        )),

        Expr::And(a, b) => Ok(format!(
            "({} && {})",
            render_expr(a, var_map, ctx)?,
            render_expr(b, var_map, ctx)?
        )),
        Expr::Or(a, b) => Ok(format!(
            "({} || {})",
            render_expr(a, var_map, ctx)?,
            render_expr(b, var_map, ctx)?
        )),
        Expr::Not(a) => Ok(format!("!({})", render_expr(a, var_map, ctx)?)),

        Expr::Ite { cond, then_, else_ } => {
            // Render as Rust conditional expression: if cond { then_ } else { else_ }
            let cond_s = render_expr(cond, var_map, ctx)?;
            let then_s = render_expr(then_, var_map, ctx)?;
            let else_s = render_expr(else_, var_map, ctx)?;
            Ok(format!("(if {cond_s} {{ {then_s} }} else {{ {else_s} }})"))
        }
        Expr::ArrayIndex(arr, idx) => {
            // Model array indexing as a pure function call to kani::any() with the index as a comment.
            // This allows bounds check VCs to be exported - the actual value returned is unconstrained,
            // but the verification focuses on the index being within bounds.
            let arr_s = render_expr(arr, var_map, ctx)?;
            let idx_s = render_expr(idx, var_map, ctx)?;
            // Use a synthetic variable pattern: {arr}_elem_{idx}
            // For most bounds checks, this expression doesn't actually matter since the VC
            // checks that idx is in bounds, not what the array element value is.
            Ok(format!("{arr_s}_elem /* [{idx_s}] */"))
        }
        Expr::StructField(base, field) => {
            // Support .count and .hasValue for BoundsCheck and NilCheck VCs.
            // These are rendered as synthetic helper variables since Kani doesn't know Swift types.
            let base_s = render_expr(base, var_map, ctx)?;
            match field.as_str() {
                "count" => {
                    // Array count: render as {base}_count variable (non-negative integer)
                    Ok(format!("{base_s}_count"))
                }
                "hasValue" => {
                    // Optional hasValue: render as {base}_has_value variable (boolean)
                    Ok(format!("{base_s}_has_value"))
                }
                _ => Err(KaniExportError::Unsupported(
                    "StructField (unsupported field)",
                )),
            }
        }
        Expr::Apply { .. } => Err(KaniExportError::Unsupported("Apply")),
        Expr::Forall { .. } => Err(KaniExportError::Unsupported("Forall")),
        Expr::Exists { .. } => Err(KaniExportError::Unsupported("Exists")),
    }
}

#[allow(clippy::too_many_lines)]
fn render_expr_in_old_context(
    expr: &Expr,
    var_map: &HashMap<String, String>,
    ctx: RenderContext,
) -> Result<String, KaniExportError> {
    match expr {
        Expr::IntLit(v) => Ok(format!("{v}")),
        Expr::BoolLit(v) => Ok(v.to_string()),
        Expr::NilLit => Err(KaniExportError::Unsupported("NilLit")),
        Expr::Var(var_name) => {
            let ident = var_map
                .get(var_name)
                .cloned()
                .unwrap_or_else(|| var_name.clone());
            Ok(format!("old_{ident}"))
        }
        Expr::Result => Err(KaniExportError::Unsupported("Old(Result)")),
        Expr::Old(inner) => render_expr_in_old_context(inner, var_map, ctx),

        // We model struct fields/array access as synthetic immutable variables, so they already
        // behave like "entry values" in the Kani harness; no need for old_ copies.
        Expr::ArrayIndex(_, _) | Expr::StructField(_, _) => render_expr(expr, var_map, ctx),

        Expr::Add(a, b) => {
            let a_s = render_expr_in_old_context(a, var_map, ctx)?;
            let b_s = render_expr_in_old_context(b, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_add({b_s})"))
            } else {
                Ok(format!("({a_s} + {b_s})"))
            }
        }
        Expr::Sub(a, b) => {
            let a_s = render_expr_in_old_context(a, var_map, ctx)?;
            let b_s = render_expr_in_old_context(b, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_sub({b_s})"))
            } else {
                Ok(format!("({a_s} - {b_s})"))
            }
        }
        Expr::Mul(a, b) => {
            let a_s = render_expr_in_old_context(a, var_map, ctx)?;
            let b_s = render_expr_in_old_context(b, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_mul({b_s})"))
            } else {
                Ok(format!("({a_s} * {b_s})"))
            }
        }
        Expr::Div(a, b) => {
            let a_s = render_expr_in_old_context(a, var_map, ctx)?;
            let b_s = render_expr_in_old_context(b, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_div({b_s})"))
            } else {
                Ok(format!("({a_s} / {b_s})"))
            }
        }
        Expr::Rem(a, b) => {
            let a_s = render_expr_in_old_context(a, var_map, ctx)?;
            let b_s = render_expr_in_old_context(b, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_rem({b_s})"))
            } else {
                Ok(format!("({a_s} % {b_s})"))
            }
        }
        Expr::Eq(a, b) => Ok(format!(
            "({} == {})",
            render_expr_in_old_context(a, var_map, ctx)?,
            render_expr_in_old_context(b, var_map, ctx)?
        )),
        Expr::Ne(a, b) => Ok(format!(
            "({} != {})",
            render_expr_in_old_context(a, var_map, ctx)?,
            render_expr_in_old_context(b, var_map, ctx)?
        )),
        Expr::Lt(a, b) => Ok(format!(
            "({} < {})",
            render_expr_in_old_context(a, var_map, ctx)?,
            render_expr_in_old_context(b, var_map, ctx)?
        )),
        Expr::Le(a, b) => Ok(format!(
            "({} <= {})",
            render_expr_in_old_context(a, var_map, ctx)?,
            render_expr_in_old_context(b, var_map, ctx)?
        )),
        Expr::Gt(a, b) => Ok(format!(
            "({} > {})",
            render_expr_in_old_context(a, var_map, ctx)?,
            render_expr_in_old_context(b, var_map, ctx)?
        )),
        Expr::Ge(a, b) => Ok(format!(
            "({} >= {})",
            render_expr_in_old_context(a, var_map, ctx)?,
            render_expr_in_old_context(b, var_map, ctx)?
        )),

        Expr::And(a, b) => Ok(format!(
            "({} && {})",
            render_expr_in_old_context(a, var_map, ctx)?,
            render_expr_in_old_context(b, var_map, ctx)?
        )),
        Expr::Or(a, b) => Ok(format!(
            "({} || {})",
            render_expr_in_old_context(a, var_map, ctx)?,
            render_expr_in_old_context(b, var_map, ctx)?
        )),
        Expr::Neg(a) => {
            let a_s = render_expr_in_old_context(a, var_map, ctx)?;
            if ctx.bitvector_mode {
                Ok(format!("({a_s}).wrapping_neg()"))
            } else {
                Ok(format!("-({a_s})"))
            }
        }
        Expr::Not(a) => Ok(format!(
            "!({})",
            render_expr_in_old_context(a, var_map, ctx)?
        )),

        Expr::Ite { cond, then_, else_ } => {
            let cond_s = render_expr_in_old_context(cond, var_map, ctx)?;
            let then_s = render_expr_in_old_context(then_, var_map, ctx)?;
            let else_s = render_expr_in_old_context(else_, var_map, ctx)?;
            Ok(format!("(if {cond_s} {{ {then_s} }} else {{ {else_s} }})"))
        }
        Expr::Apply { .. } => Err(KaniExportError::Unsupported("Apply")),
        Expr::Forall { .. } => Err(KaniExportError::Unsupported("Forall")),
        Expr::Exists { .. } => Err(KaniExportError::Unsupported("Exists")),
    }
}

const fn is_rust_ident_start(c: char) -> bool {
    c == '_' || c.is_ascii_alphabetic()
}

const fn is_rust_ident_continue(c: char) -> bool {
    c == '_' || c.is_ascii_alphanumeric()
}

fn sanitize_ident(name: &str) -> String {
    let mut out = String::new();
    for (i, ch) in name.chars().enumerate() {
        if i == 0 {
            out.push(if is_rust_ident_start(ch) { ch } else { '_' });
        } else {
            out.push(if is_rust_ident_continue(ch) { ch } else { '_' });
        }
    }
    if out.is_empty() {
        out.push('_');
    }
    match out.as_str() {
        "fn" | "let" | "mod" | "crate" | "super" | "self" | "type" | "match" | "impl" | "trait"
        | "struct" | "enum" | "use" | "pub" | "where" | "return" | "true" | "false" | "const"
        | "static" | "mut" | "ref" | "move" | "async" | "await" | "loop" | "while" | "for"
        | "if" | "else" | "break" | "continue" => format!("_{out}"),
        _ => out,
    }
}

fn unique_sanitized_ident(name: &str, used: &mut HashSet<String>) -> String {
    let base = sanitize_ident(name);
    if used.insert(base.clone()) {
        return base;
    }
    for i in 1.. {
        let candidate = format!("{base}_{i}");
        if used.insert(candidate.clone()) {
            return candidate;
        }
    }
    unreachable!("loop returns on first unused candidate")
}

/// Escape a string for use as a Rust string literal.
fn escape_string_for_rust(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========== vctype_to_rust_native tests ==========

    #[test]
    fn vctype_to_rust_native_signed_standard_widths() {
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: true,
                bits: 8
            }),
            Some("i8")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: true,
                bits: 16
            }),
            Some("i16")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: true,
                bits: 32
            }),
            Some("i32")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: true,
                bits: 64
            }),
            Some("i64")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: true,
                bits: 128
            }),
            Some("i128")
        );
    }

    #[test]
    fn vctype_to_rust_native_unsigned_standard_widths() {
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: false,
                bits: 8
            }),
            Some("u8")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: false,
                bits: 16
            }),
            Some("u16")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: false,
                bits: 32
            }),
            Some("u32")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: false,
                bits: 64
            }),
            Some("u64")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: false,
                bits: 128
            }),
            Some("u128")
        );
    }

    #[test]
    fn vctype_to_rust_native_nonstandard_widths_round_up() {
        // Non-standard widths should round up to next larger type
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: true,
                bits: 4
            }),
            Some("i8")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: true,
                bits: 12
            }),
            Some("i16")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: true,
                bits: 24
            }),
            Some("i32")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: true,
                bits: 48
            }),
            Some("i64")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: true,
                bits: 100
            }),
            Some("i128")
        );

        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: false,
                bits: 4
            }),
            Some("u8")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: false,
                bits: 12
            }),
            Some("u16")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: false,
                bits: 24
            }),
            Some("u32")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: false,
                bits: 48
            }),
            Some("u64")
        );
        assert_eq!(
            vctype_to_rust_native(&VcType::Int {
                signed: false,
                bits: 100
            }),
            Some("u128")
        );
    }

    #[test]
    fn vctype_to_rust_native_non_int_returns_none() {
        assert_eq!(vctype_to_rust_native(&VcType::Bool), None);
        assert_eq!(vctype_to_rust_native(&VcType::Float { bits: 32 }), None);
        assert_eq!(
            vctype_to_rust_native(&VcType::Abstract("String".to_string())),
            None
        );
    }

    // ========== int_bounds tests ==========

    #[test]
    fn int_bounds_i8() {
        let result = int_bounds(&VcType::Int {
            signed: true,
            bits: 8,
        })
        .unwrap();
        assert_eq!(result, (-128, 127));
    }

    #[test]
    fn int_bounds_u8() {
        let result = int_bounds(&VcType::Int {
            signed: false,
            bits: 8,
        })
        .unwrap();
        assert_eq!(result, (0, 255));
    }

    #[test]
    fn int_bounds_i16() {
        let result = int_bounds(&VcType::Int {
            signed: true,
            bits: 16,
        })
        .unwrap();
        assert_eq!(result, (-32768, 32767));
    }

    #[test]
    fn int_bounds_u16() {
        let result = int_bounds(&VcType::Int {
            signed: false,
            bits: 16,
        })
        .unwrap();
        assert_eq!(result, (0, 65535));
    }

    #[test]
    fn int_bounds_i32() {
        let result = int_bounds(&VcType::Int {
            signed: true,
            bits: 32,
        })
        .unwrap();
        assert_eq!(result, (-2_147_483_648, 2_147_483_647));
    }

    #[test]
    fn int_bounds_u32() {
        let result = int_bounds(&VcType::Int {
            signed: false,
            bits: 32,
        })
        .unwrap();
        assert_eq!(result, (0, 4_294_967_295));
    }

    #[test]
    fn int_bounds_i64() {
        let result = int_bounds(&VcType::Int {
            signed: true,
            bits: 64,
        })
        .unwrap();
        assert_eq!(
            result,
            (-9_223_372_036_854_775_808, 9_223_372_036_854_775_807)
        );
    }

    #[test]
    fn int_bounds_u64() {
        let result = int_bounds(&VcType::Int {
            signed: false,
            bits: 64,
        })
        .unwrap();
        assert_eq!(result, (0, 18_446_744_073_709_551_615));
    }

    #[test]
    fn int_bounds_zero_bits_error() {
        let result = int_bounds(&VcType::Int {
            signed: true,
            bits: 0,
        });
        assert!(result.is_err());
    }

    #[test]
    fn int_bounds_non_int_error() {
        let result = int_bounds(&VcType::Bool);
        assert!(result.is_err());
    }

    // ========== sanitize_ident tests ==========

    #[test]
    fn sanitize_ident_valid_identifier() {
        assert_eq!(sanitize_ident("foo"), "foo");
        assert_eq!(sanitize_ident("_bar"), "_bar");
        assert_eq!(sanitize_ident("foo_bar"), "foo_bar");
        assert_eq!(sanitize_ident("foo123"), "foo123");
    }

    #[test]
    fn sanitize_ident_starts_with_digit() {
        assert_eq!(sanitize_ident("123foo"), "_23foo");
    }

    #[test]
    fn sanitize_ident_invalid_characters() {
        assert_eq!(sanitize_ident("foo-bar"), "foo_bar");
        assert_eq!(sanitize_ident("foo.bar"), "foo_bar");
        assert_eq!(sanitize_ident("foo bar"), "foo_bar");
        assert_eq!(sanitize_ident("foo@bar"), "foo_bar");
    }

    #[test]
    fn sanitize_ident_empty_string() {
        assert_eq!(sanitize_ident(""), "_");
    }

    #[test]
    fn sanitize_ident_reserved_keywords() {
        let cases = [
            ("fn", "_fn"),
            ("let", "_let"),
            ("mod", "_mod"),
            ("crate", "_crate"),
            ("self", "_self"),
            ("type", "_type"),
            ("match", "_match"),
            ("impl", "_impl"),
            ("trait", "_trait"),
            ("struct", "_struct"),
            ("enum", "_enum"),
            ("use", "_use"),
            ("pub", "_pub"),
            ("where", "_where"),
            ("return", "_return"),
            ("true", "_true"),
            ("false", "_false"),
            ("const", "_const"),
            ("static", "_static"),
            ("mut", "_mut"),
            ("ref", "_ref"),
            ("move", "_move"),
            ("async", "_async"),
            ("await", "_await"),
            ("loop", "_loop"),
            ("while", "_while"),
            ("for", "_for"),
            ("if", "_if"),
            ("else", "_else"),
            ("break", "_break"),
            ("continue", "_continue"),
        ];

        for (input, expected) in cases {
            assert_eq!(sanitize_ident(input), expected);
        }
    }

    #[test]
    fn sanitize_ident_not_reserved() {
        // Non-reserved words shouldn't be prefixed
        assert_eq!(sanitize_ident("function"), "function");
        assert_eq!(sanitize_ident("letter"), "letter");
        assert_eq!(sanitize_ident("module"), "module");
    }

    // ========== unique_sanitized_ident tests ==========

    #[test]
    fn unique_sanitized_ident_first_use() {
        let mut used = HashSet::new();
        let result = unique_sanitized_ident("foo", &mut used);
        assert_eq!(result, "foo");
        assert!(used.contains("foo"));
    }

    #[test]
    fn unique_sanitized_ident_collision() {
        let mut used = HashSet::new();
        used.insert("foo".to_string());
        let result = unique_sanitized_ident("foo", &mut used);
        assert_eq!(result, "foo_1");
        assert!(used.contains("foo_1"));
    }

    #[test]
    fn unique_sanitized_ident_multiple_collisions() {
        let mut used = HashSet::new();
        used.insert("foo".to_string());
        used.insert("foo_1".to_string());
        used.insert("foo_2".to_string());
        let result = unique_sanitized_ident("foo", &mut used);
        assert_eq!(result, "foo_3");
    }

    #[test]
    fn unique_sanitized_ident_sanitizes_first() {
        let mut used = HashSet::new();
        let result = unique_sanitized_ident("foo-bar", &mut used);
        assert_eq!(result, "foo_bar");
    }

    // ========== escape_string_for_rust tests ==========

    #[test]
    fn escape_string_plain_text() {
        assert_eq!(escape_string_for_rust("hello world"), "hello world");
    }

    #[test]
    fn escape_string_backslash() {
        assert_eq!(escape_string_for_rust("foo\\bar"), "foo\\\\bar");
    }

    #[test]
    fn escape_string_quotes() {
        assert_eq!(escape_string_for_rust("foo\"bar"), "foo\\\"bar");
    }

    #[test]
    fn escape_string_newline() {
        assert_eq!(escape_string_for_rust("foo\nbar"), "foo\\nbar");
    }

    #[test]
    fn escape_string_carriage_return() {
        assert_eq!(escape_string_for_rust("foo\rbar"), "foo\\rbar");
    }

    #[test]
    fn escape_string_tab() {
        assert_eq!(escape_string_for_rust("foo\tbar"), "foo\\tbar");
    }

    #[test]
    fn escape_string_combined() {
        assert_eq!(
            escape_string_for_rust("a\\b\"c\nd\re\tf"),
            "a\\\\b\\\"c\\nd\\re\\tf"
        );
    }

    // ========== is_rust_ident_start/continue tests ==========

    #[test]
    fn is_rust_ident_start_underscore() {
        assert!(is_rust_ident_start('_'));
    }

    #[test]
    fn is_rust_ident_start_letter() {
        assert!(is_rust_ident_start('a'));
        assert!(is_rust_ident_start('Z'));
    }

    #[test]
    fn is_rust_ident_start_digit_false() {
        assert!(!is_rust_ident_start('0'));
        assert!(!is_rust_ident_start('9'));
    }

    #[test]
    fn is_rust_ident_continue_underscore() {
        assert!(is_rust_ident_continue('_'));
    }

    #[test]
    fn is_rust_ident_continue_letter() {
        assert!(is_rust_ident_continue('a'));
        assert!(is_rust_ident_continue('Z'));
    }

    #[test]
    fn is_rust_ident_continue_digit() {
        assert!(is_rust_ident_continue('0'));
        assert!(is_rust_ident_continue('9'));
    }

    #[test]
    fn is_rust_ident_continue_special_false() {
        assert!(!is_rust_ident_continue('-'));
        assert!(!is_rust_ident_continue('.'));
        assert!(!is_rust_ident_continue('@'));
    }

    // ========== exprs_structurally_equal tests ==========

    #[test]
    fn exprs_structurally_equal_int_literals() {
        assert!(exprs_structurally_equal(
            &Expr::IntLit(42),
            &Expr::IntLit(42)
        ));
        assert!(!exprs_structurally_equal(
            &Expr::IntLit(42),
            &Expr::IntLit(43)
        ));
    }

    #[test]
    fn exprs_structurally_equal_bool_literals() {
        assert!(exprs_structurally_equal(
            &Expr::BoolLit(true),
            &Expr::BoolLit(true)
        ));
        assert!(!exprs_structurally_equal(
            &Expr::BoolLit(true),
            &Expr::BoolLit(false)
        ));
    }

    #[test]
    fn exprs_structurally_equal_nil() {
        assert!(exprs_structurally_equal(&Expr::NilLit, &Expr::NilLit));
    }

    #[test]
    fn exprs_structurally_equal_vars() {
        assert!(exprs_structurally_equal(
            &Expr::Var("x".to_string()),
            &Expr::Var("x".to_string())
        ));
        assert!(!exprs_structurally_equal(
            &Expr::Var("x".to_string()),
            &Expr::Var("y".to_string())
        ));
    }

    #[test]
    fn exprs_structurally_equal_result() {
        assert!(exprs_structurally_equal(&Expr::Result, &Expr::Result));
    }

    #[test]
    fn exprs_structurally_equal_add() {
        let a = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        let b = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        let c = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert!(exprs_structurally_equal(&a, &b));
        assert!(!exprs_structurally_equal(&a, &c));
    }

    #[test]
    fn exprs_structurally_equal_sub() {
        let a = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        let b = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        assert!(exprs_structurally_equal(&a, &b));
    }

    #[test]
    fn exprs_structurally_equal_mul() {
        let a = Expr::Mul(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        let b = Expr::Mul(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert!(exprs_structurally_equal(&a, &b));
    }

    #[test]
    fn exprs_structurally_equal_div() {
        let a = Expr::Div(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        let b = Expr::Div(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert!(exprs_structurally_equal(&a, &b));
    }

    #[test]
    fn exprs_structurally_equal_rem() {
        let a = Expr::Rem(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        let b = Expr::Rem(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert!(exprs_structurally_equal(&a, &b));
    }

    #[test]
    fn exprs_structurally_equal_neg() {
        let a = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        let b = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        let c = Expr::Neg(Box::new(Expr::Var("y".to_string())));
        assert!(exprs_structurally_equal(&a, &b));
        assert!(!exprs_structurally_equal(&a, &c));
    }

    #[test]
    fn exprs_structurally_equal_old() {
        let a = Expr::Old(Box::new(Expr::Var("x".to_string())));
        let b = Expr::Old(Box::new(Expr::Var("x".to_string())));
        let c = Expr::Old(Box::new(Expr::Var("y".to_string())));
        assert!(exprs_structurally_equal(&a, &b));
        assert!(!exprs_structurally_equal(&a, &c));
    }

    #[test]
    fn exprs_structurally_equal_different_types() {
        // Different expression types should not be equal
        assert!(!exprs_structurally_equal(
            &Expr::IntLit(1),
            &Expr::BoolLit(true)
        ));
        assert!(!exprs_structurally_equal(
            &Expr::Var("x".to_string()),
            &Expr::IntLit(1)
        ));
        assert!(!exprs_structurally_equal(&Expr::Result, &Expr::NilLit));
    }

    // ========== extract_arith_op tests ==========

    #[test]
    fn extract_arith_op_add() {
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        let result = extract_arith_op(&expr);
        assert!(matches!(result, Some((ArithOp::Add, _))));
        let (_, operands) = result.unwrap();
        assert_eq!(operands.len(), 2);
    }

    #[test]
    fn extract_arith_op_sub() {
        let expr = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        let result = extract_arith_op(&expr);
        assert!(matches!(result, Some((ArithOp::Sub, _))));
    }

    #[test]
    fn extract_arith_op_mul() {
        let expr = Expr::Mul(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        let result = extract_arith_op(&expr);
        assert!(matches!(result, Some((ArithOp::Mul, _))));
    }

    #[test]
    fn extract_arith_op_div() {
        let expr = Expr::Div(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        let result = extract_arith_op(&expr);
        assert!(matches!(result, Some((ArithOp::Div, _))));
    }

    #[test]
    fn extract_arith_op_rem() {
        let expr = Expr::Rem(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        let result = extract_arith_op(&expr);
        assert!(matches!(result, Some((ArithOp::Rem, _))));
    }

    #[test]
    fn extract_arith_op_neg() {
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        let result = extract_arith_op(&expr);
        assert!(matches!(result, Some((ArithOp::Neg, _))));
        let (_, operands) = result.unwrap();
        assert_eq!(operands.len(), 1);
    }

    #[test]
    fn extract_arith_op_non_arith_returns_none() {
        assert!(extract_arith_op(&Expr::IntLit(42)).is_none());
        assert!(extract_arith_op(&Expr::BoolLit(true)).is_none());
        assert!(extract_arith_op(&Expr::Var("x".to_string())).is_none());
        assert!(extract_arith_op(&Expr::Result).is_none());
    }

    // ========== ArithOp::checked_method tests ==========

    #[test]
    fn arith_op_checked_method_add() {
        assert_eq!(ArithOp::Add.checked_method(), "checked_add");
    }

    #[test]
    fn arith_op_checked_method_sub() {
        assert_eq!(ArithOp::Sub.checked_method(), "checked_sub");
    }

    #[test]
    fn arith_op_checked_method_mul() {
        assert_eq!(ArithOp::Mul.checked_method(), "checked_mul");
    }

    #[test]
    fn arith_op_checked_method_div() {
        assert_eq!(ArithOp::Div.checked_method(), "checked_div");
    }

    #[test]
    fn arith_op_checked_method_rem() {
        assert_eq!(ArithOp::Rem.checked_method(), "checked_rem");
    }

    #[test]
    fn arith_op_checked_method_neg() {
        assert_eq!(ArithOp::Neg.checked_method(), "checked_neg");
    }

    // ========== join_bool tests ==========

    #[test]
    fn join_bool_empty() {
        assert_eq!(join_bool("&&", vec![]), "true");
    }

    #[test]
    fn join_bool_single() {
        assert_eq!(join_bool("&&", vec!["x".to_string()]), "x");
    }

    #[test]
    fn join_bool_two() {
        assert_eq!(
            join_bool("&&", vec!["x".to_string(), "y".to_string()]),
            "(x && y)"
        );
    }

    #[test]
    fn join_bool_three() {
        assert_eq!(
            join_bool(
                "||",
                vec!["a".to_string(), "b".to_string(), "c".to_string()]
            ),
            "(a || b || c)"
        );
    }

    // ========== render_expr tests ==========

    #[test]
    fn render_expr_int_lit() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        assert_eq!(render_expr(&Expr::IntLit(42), &var_map, ctx).unwrap(), "42");
        assert_eq!(
            render_expr(&Expr::IntLit(-123), &var_map, ctx).unwrap(),
            "-123"
        );
    }

    #[test]
    fn render_expr_bool_lit() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        assert_eq!(
            render_expr(&Expr::BoolLit(true), &var_map, ctx).unwrap(),
            "true"
        );
        assert_eq!(
            render_expr(&Expr::BoolLit(false), &var_map, ctx).unwrap(),
            "false"
        );
    }

    #[test]
    fn render_expr_var() {
        let mut var_map = HashMap::new();
        var_map.insert("x".to_string(), "x_var".to_string());
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        assert_eq!(
            render_expr(&Expr::Var("x".to_string()), &var_map, ctx).unwrap(),
            "x_var"
        );
    }

    #[test]
    fn render_expr_var_unmapped() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        // Unmapped variables use their original name
        assert_eq!(
            render_expr(&Expr::Var("foo".to_string()), &var_map, ctx).unwrap(),
            "foo"
        );
    }

    #[test]
    fn render_expr_result() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        assert_eq!(render_expr(&Expr::Result, &var_map, ctx).unwrap(), "result");
    }

    #[test]
    fn render_expr_old() {
        let mut var_map = HashMap::new();
        var_map.insert("x".to_string(), "x_var".to_string());
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Old(Box::new(Expr::Var("x".to_string())));
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "old_x_var");
    }

    #[test]
    fn render_expr_add_default_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x + 1)");
    }

    #[test]
    fn render_expr_add_bitvector_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        assert_eq!(
            render_expr(&expr, &var_map, ctx).unwrap(),
            "(x).wrapping_add(1)"
        );
    }

    #[test]
    fn render_expr_sub_default_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x - 1)");
    }

    #[test]
    fn render_expr_sub_bitvector_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let expr = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        assert_eq!(
            render_expr(&expr, &var_map, ctx).unwrap(),
            "(x).wrapping_sub(1)"
        );
    }

    #[test]
    fn render_expr_mul_default_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Mul(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x * 2)");
    }

    #[test]
    fn render_expr_mul_bitvector_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let expr = Expr::Mul(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert_eq!(
            render_expr(&expr, &var_map, ctx).unwrap(),
            "(x).wrapping_mul(2)"
        );
    }

    #[test]
    fn render_expr_div_default_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Div(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x / 2)");
    }

    #[test]
    fn render_expr_div_bitvector_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let expr = Expr::Div(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert_eq!(
            render_expr(&expr, &var_map, ctx).unwrap(),
            "(x).wrapping_div(2)"
        );
    }

    #[test]
    fn render_expr_rem_default_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Rem(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(3)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x % 3)");
    }

    #[test]
    fn render_expr_rem_bitvector_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let expr = Expr::Rem(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(3)),
        );
        assert_eq!(
            render_expr(&expr, &var_map, ctx).unwrap(),
            "(x).wrapping_rem(3)"
        );
    }

    #[test]
    fn render_expr_neg_default_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "-(x)");
    }

    #[test]
    fn render_expr_neg_bitvector_mode() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        assert_eq!(
            render_expr(&expr, &var_map, ctx).unwrap(),
            "(x).wrapping_neg()"
        );
    }

    #[test]
    fn render_expr_eq() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x == 1)");
    }

    #[test]
    fn render_expr_ne() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Ne(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x != 1)");
    }

    #[test]
    fn render_expr_lt() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Lt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(10)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x < 10)");
    }

    #[test]
    fn render_expr_le() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Le(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(10)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x <= 10)");
    }

    #[test]
    fn render_expr_gt() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x > 0)");
    }

    #[test]
    fn render_expr_ge() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(x >= 0)");
    }

    #[test]
    fn render_expr_and() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::And(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(true && b)");
    }

    #[test]
    fn render_expr_or() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Or(
            Box::new(Expr::BoolLit(false)),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "(false || b)");
    }

    #[test]
    fn render_expr_not() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Not(Box::new(Expr::Var("b".to_string())));
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "!(b)");
    }

    #[test]
    fn render_expr_ite() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Ite {
            cond: Box::new(Expr::Var("c".to_string())),
            then_: Box::new(Expr::IntLit(1)),
            else_: Box::new(Expr::IntLit(0)),
        };
        assert_eq!(
            render_expr(&expr, &var_map, ctx).unwrap(),
            "(if c { 1 } else { 0 })"
        );
    }

    #[test]
    fn render_expr_array_index() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::ArrayIndex(
            Box::new(Expr::Var("arr".to_string())),
            Box::new(Expr::Var("i".to_string())),
        );
        assert_eq!(
            render_expr(&expr, &var_map, ctx).unwrap(),
            "arr_elem /* [i] */"
        );
    }

    #[test]
    fn render_expr_struct_field_count() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::StructField(Box::new(Expr::Var("arr".to_string())), "count".to_string());
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "arr_count");
    }

    #[test]
    fn render_expr_struct_field_has_value() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::StructField(
            Box::new(Expr::Var("opt".to_string())),
            "hasValue".to_string(),
        );
        assert_eq!(render_expr(&expr, &var_map, ctx).unwrap(), "opt_has_value");
    }

    #[test]
    fn render_expr_struct_field_unsupported() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::StructField(
            Box::new(Expr::Var("obj".to_string())),
            "unknown".to_string(),
        );
        assert!(render_expr(&expr, &var_map, ctx).is_err());
    }

    #[test]
    fn render_expr_nil_lit_unsupported() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        assert!(render_expr(&Expr::NilLit, &var_map, ctx).is_err());
    }

    #[test]
    fn render_expr_apply_unsupported() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Apply {
            func: "foo".to_string(),
            args: vec![],
        };
        assert!(render_expr(&expr, &var_map, ctx).is_err());
    }

    #[test]
    fn render_expr_forall_unsupported() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Forall {
            vars: vec![],
            body: Box::new(Expr::BoolLit(true)),
        };
        assert!(render_expr(&expr, &var_map, ctx).is_err());
    }

    #[test]
    fn render_expr_exists_unsupported() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Exists {
            vars: vec![],
            body: Box::new(Expr::BoolLit(true)),
        };
        assert!(render_expr(&expr, &var_map, ctx).is_err());
    }

    // ========== render_predicate tests ==========

    #[test]
    fn render_predicate_expr() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let pred = Predicate::Expr(Expr::BoolLit(true));
        assert_eq!(render_predicate(&pred, &var_map, ctx).unwrap(), "true");
    }

    #[test]
    fn render_predicate_and_empty() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let pred = Predicate::And(vec![]);
        assert_eq!(render_predicate(&pred, &var_map, ctx).unwrap(), "true");
    }

    #[test]
    fn render_predicate_and_single() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let pred = Predicate::And(vec![Predicate::Expr(Expr::Var("a".to_string()))]);
        assert_eq!(render_predicate(&pred, &var_map, ctx).unwrap(), "a");
    }

    #[test]
    fn render_predicate_and_multiple() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::Var("a".to_string())),
            Predicate::Expr(Expr::Var("b".to_string())),
        ]);
        assert_eq!(render_predicate(&pred, &var_map, ctx).unwrap(), "(a && b)");
    }

    #[test]
    fn render_predicate_or_empty() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let pred = Predicate::Or(vec![]);
        assert_eq!(render_predicate(&pred, &var_map, ctx).unwrap(), "true");
    }

    #[test]
    fn render_predicate_or_multiple() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let pred = Predicate::Or(vec![
            Predicate::Expr(Expr::Var("a".to_string())),
            Predicate::Expr(Expr::Var("b".to_string())),
        ]);
        assert_eq!(render_predicate(&pred, &var_map, ctx).unwrap(), "(a || b)");
    }

    #[test]
    fn render_predicate_not() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let pred = Predicate::Not(Box::new(Predicate::Expr(Expr::Var("a".to_string()))));
        assert_eq!(render_predicate(&pred, &var_map, ctx).unwrap(), "!(a)");
    }

    #[test]
    fn render_predicate_implies() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::Var("a".to_string()))),
            Box::new(Predicate::Expr(Expr::Var("b".to_string()))),
        );
        assert_eq!(
            render_predicate(&pred, &var_map, ctx).unwrap(),
            "(!(a)) || (b)"
        );
    }

    // ========== collect_vars_from_expr tests ==========

    #[test]
    fn collect_vars_from_expr_int_lit() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        collect_vars_from_expr(
            &Expr::IntLit(42),
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.is_empty());
        assert!(!uses_result);
    }

    #[test]
    fn collect_vars_from_expr_bool_lit() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        collect_vars_from_expr(
            &Expr::BoolLit(true),
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.is_empty());
    }

    #[test]
    fn collect_vars_from_expr_var() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        collect_vars_from_expr(
            &Expr::Var("x".to_string()),
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("x"));
    }

    #[test]
    fn collect_vars_from_expr_result() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        collect_vars_from_expr(
            &Expr::Result,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(uses_result);
    }

    #[test]
    fn collect_vars_from_expr_old() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let expr = Expr::Old(Box::new(Expr::Var("x".to_string())));
        collect_vars_from_expr(
            &expr,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("x"));
        assert!(old_refs.contains("x"));
    }

    #[test]
    fn collect_vars_from_expr_binary_ops() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        collect_vars_from_expr(
            &expr,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("x"));
        assert!(vars.contains("y"));
    }

    #[test]
    fn collect_vars_from_expr_ite() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let expr = Expr::Ite {
            cond: Box::new(Expr::Var("c".to_string())),
            then_: Box::new(Expr::Var("t".to_string())),
            else_: Box::new(Expr::Var("e".to_string())),
        };
        collect_vars_from_expr(
            &expr,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("c"));
        assert!(vars.contains("t"));
        assert!(vars.contains("e"));
    }

    #[test]
    fn collect_vars_from_expr_array_index() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let expr = Expr::ArrayIndex(
            Box::new(Expr::Var("arr".to_string())),
            Box::new(Expr::Var("i".to_string())),
        );
        collect_vars_from_expr(
            &expr,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("arr"));
        assert!(vars.contains("i"));
        assert!(array_accesses.contains("arr"));
    }

    #[test]
    fn collect_vars_from_expr_struct_field_count() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let expr = Expr::StructField(Box::new(Expr::Var("arr".to_string())), "count".to_string());
        collect_vars_from_expr(
            &expr,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("arr"));
        assert!(struct_fields.contains(&("arr".to_string(), "count".to_string())));
    }

    #[test]
    fn collect_vars_from_expr_struct_field_has_value() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let expr = Expr::StructField(
            Box::new(Expr::Var("opt".to_string())),
            "hasValue".to_string(),
        );
        collect_vars_from_expr(
            &expr,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("opt"));
        assert!(struct_fields.contains(&("opt".to_string(), "hasValue".to_string())));
    }

    #[test]
    fn collect_vars_from_expr_nil_lit_error() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let result = collect_vars_from_expr(
            &Expr::NilLit,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        );
        assert!(result.is_err());
    }

    // ========== collect_vars_from_predicate tests ==========

    #[test]
    fn collect_vars_from_predicate_expr() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let pred = Predicate::Expr(Expr::Var("x".to_string()));
        collect_vars_from_predicate(
            &pred,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("x"));
    }

    #[test]
    fn collect_vars_from_predicate_and() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::Var("a".to_string())),
            Predicate::Expr(Expr::Var("b".to_string())),
        ]);
        collect_vars_from_predicate(
            &pred,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("a"));
        assert!(vars.contains("b"));
    }

    #[test]
    fn collect_vars_from_predicate_or() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let pred = Predicate::Or(vec![
            Predicate::Expr(Expr::Var("a".to_string())),
            Predicate::Expr(Expr::Var("b".to_string())),
        ]);
        collect_vars_from_predicate(
            &pred,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("a"));
        assert!(vars.contains("b"));
    }

    #[test]
    fn collect_vars_from_predicate_not() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let pred = Predicate::Not(Box::new(Predicate::Expr(Expr::Var("a".to_string()))));
        collect_vars_from_predicate(
            &pred,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("a"));
    }

    #[test]
    fn collect_vars_from_predicate_implies() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::Var("a".to_string()))),
            Box::new(Predicate::Expr(Expr::Var("b".to_string()))),
        );
        collect_vars_from_predicate(
            &pred,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("a"));
        assert!(vars.contains("b"));
    }

    // ========== collect_vars_from_vc tests ==========

    #[test]
    fn collect_vars_from_vc_predicate() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let vc = VcKind::Predicate(Predicate::Expr(Expr::Var("x".to_string())));
        collect_vars_from_vc(
            &vc,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("x"));
    }

    #[test]
    fn collect_vars_from_vc_implies() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let vc = VcKind::Implies {
            antecedent: Predicate::Expr(Expr::Var("a".to_string())),
            consequent: Predicate::Expr(Expr::Var("b".to_string())),
        };
        collect_vars_from_vc(
            &vc,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("a"));
        assert!(vars.contains("b"));
    }

    #[test]
    fn collect_vars_from_vc_termination() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let vc = VcKind::Termination {
            measure: Expr::Var("m".to_string()),
            initial_measure: Some(Expr::Var("i".to_string())),
            next_measure: Expr::Var("n".to_string()),
            loop_label: "bb1".to_string(),
        };
        collect_vars_from_vc(
            &vc,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("m"));
        assert!(vars.contains("i"));
        assert!(vars.contains("n"));
    }

    #[test]
    fn collect_vars_from_vc_termination_no_initial() {
        let mut vars = BTreeSet::new();
        let mut struct_fields = BTreeSet::new();
        let mut array_accesses = BTreeSet::new();
        let mut old_refs = BTreeSet::new();
        let mut uses_result = false;
        let vc = VcKind::Termination {
            measure: Expr::Var("m".to_string()),
            initial_measure: None,
            next_measure: Expr::Var("n".to_string()),
            loop_label: "bb2".to_string(),
        };
        collect_vars_from_vc(
            &vc,
            &mut vars,
            &mut struct_fields,
            &mut array_accesses,
            &mut old_refs,
            &mut uses_result,
        )
        .unwrap();
        assert!(vars.contains("m"));
        assert!(!vars.contains("i"));
        assert!(vars.contains("n"));
    }

    // ========== render_checked_overflow tests ==========

    #[test]
    fn render_checked_overflow_add() {
        let var_map = HashMap::new();
        let a = Expr::Var("x".to_string());
        let b = Expr::IntLit(1);
        let result = render_checked_overflow(ArithOp::Add, &[&a, &b], &var_map).unwrap();
        assert_eq!(result, "(x).checked_add(1).is_some()");
    }

    #[test]
    fn render_checked_overflow_sub() {
        let var_map = HashMap::new();
        let a = Expr::Var("x".to_string());
        let b = Expr::IntLit(1);
        let result = render_checked_overflow(ArithOp::Sub, &[&a, &b], &var_map).unwrap();
        assert_eq!(result, "(x).checked_sub(1).is_some()");
    }

    #[test]
    fn render_checked_overflow_mul() {
        let var_map = HashMap::new();
        let a = Expr::Var("x".to_string());
        let b = Expr::IntLit(2);
        let result = render_checked_overflow(ArithOp::Mul, &[&a, &b], &var_map).unwrap();
        assert_eq!(result, "(x).checked_mul(2).is_some()");
    }

    #[test]
    fn render_checked_overflow_div() {
        let var_map = HashMap::new();
        let a = Expr::Var("x".to_string());
        let b = Expr::IntLit(2);
        let result = render_checked_overflow(ArithOp::Div, &[&a, &b], &var_map).unwrap();
        assert_eq!(result, "(x).checked_div(2).is_some()");
    }

    #[test]
    fn render_checked_overflow_rem() {
        let var_map = HashMap::new();
        let a = Expr::Var("x".to_string());
        let b = Expr::IntLit(3);
        let result = render_checked_overflow(ArithOp::Rem, &[&a, &b], &var_map).unwrap();
        assert_eq!(result, "(x).checked_rem(3).is_some()");
    }

    #[test]
    fn render_checked_overflow_neg() {
        let var_map = HashMap::new();
        let a = Expr::Var("x".to_string());
        let result = render_checked_overflow(ArithOp::Neg, &[&a], &var_map).unwrap();
        assert_eq!(result, "(x).checked_neg().is_some()");
    }

    // ========== try_render_overflow_check tests ==========

    #[test]
    fn try_render_overflow_check_non_bitvector_mode_returns_none() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        // Any predicate in non-bitvector mode should return None
        let pred = Predicate::Expr(Expr::BoolLit(true));
        assert!(try_render_overflow_check(&pred, &var_map, ctx).is_none());
    }

    #[test]
    fn try_render_overflow_check_non_matching_pattern_returns_none() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        // A simple expression that doesn't match the overflow pattern
        let pred = Predicate::Expr(Expr::BoolLit(true));
        assert!(try_render_overflow_check(&pred, &var_map, ctx).is_none());
    }

    #[test]
    fn try_render_overflow_check_from_exprs_mismatched_arith_returns_none() {
        // Two different arithmetic expressions should not match
        let ge_expr = Expr::Ge(
            Box::new(Expr::Add(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
            Box::new(Expr::IntLit(-128)),
        );
        let le_expr = Expr::Le(
            Box::new(Expr::Sub(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(1)),
            )), // Different op
            Box::new(Expr::IntLit(127)),
        );
        let var_map = HashMap::new();
        assert!(try_render_overflow_check_from_exprs(&ge_expr, &le_expr, &var_map).is_none());
    }

    #[test]
    fn try_render_overflow_check_from_exprs_valid_add_overflow() {
        // Pattern: (x + 1) >= MIN && (x + 1) <= MAX -> x.checked_add(1).is_some()
        let add_expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        let ge_expr = Expr::Ge(Box::new(add_expr.clone()), Box::new(Expr::IntLit(-128)));
        let le_expr = Expr::Le(Box::new(add_expr), Box::new(Expr::IntLit(127)));
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&ge_expr, &le_expr, &var_map);
        assert!(result.is_some());
        let code = result.unwrap().unwrap();
        assert_eq!(code, "(x).checked_add(1).is_some()");
    }

    #[test]
    fn try_render_overflow_check_from_exprs_valid_neg_overflow() {
        // Pattern: (-x) >= MIN && (-x) <= MAX -> x.checked_neg().is_some()
        let neg_expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        let ge_expr = Expr::Ge(Box::new(neg_expr.clone()), Box::new(Expr::IntLit(-128)));
        let le_expr = Expr::Le(Box::new(neg_expr), Box::new(Expr::IntLit(127)));
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&ge_expr, &le_expr, &var_map);
        assert!(result.is_some());
        let code = result.unwrap().unwrap();
        assert_eq!(code, "(x).checked_neg().is_some()");
    }

    // ========== KaniExportConfig tests ==========

    #[test]
    fn kani_export_config_default() {
        let config = KaniExportConfig::default();
        assert!(!config.bitvector_mode);
        assert!(config.preconditions.is_empty());
        assert!(config.postconditions.is_empty());
    }

    #[test]
    fn kani_export_config_clone() {
        let config = KaniExportConfig {
            bitvector_mode: true,
            preconditions: vec![Predicate::Expr(Expr::BoolLit(true))],
            postconditions: vec![],
        };
        let cloned = config;
        assert!(cloned.bitvector_mode);
        assert_eq!(cloned.preconditions.len(), 1);
    }

    #[test]
    fn kani_export_config_debug() {
        let config = KaniExportConfig::default();
        let debug_str = format!("{config:?}");
        assert!(debug_str.contains("KaniExportConfig"));
    }

    // ========== KaniExportError tests ==========

    #[test]
    fn kani_export_error_unsupported_display() {
        let err = KaniExportError::Unsupported("test feature");
        let msg = format!("{err}");
        assert!(msg.contains("unsupported"));
        assert!(msg.contains("test feature"));
    }

    #[test]
    fn kani_export_error_unknown_variable_display() {
        let err = KaniExportError::UnknownVariable("x".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("unknown variable"));
        assert!(msg.contains('x'));
    }

    #[test]
    fn kani_export_error_unsupported_param_type_display() {
        let err = KaniExportError::UnsupportedParamType("String".to_string());
        let msg = format!("{err}");
        assert!(msg.contains("unsupported parameter type"));
        assert!(msg.contains("String"));
    }

    // ========== RenderContext tests ==========

    #[test]
    fn render_context_default() {
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        assert!(!ctx.bitvector_mode);
    }

    #[test]
    fn render_context_bitvector() {
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        assert!(ctx.bitvector_mode);
    }

    #[test]
    fn render_context_clone() {
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let cloned = ctx;
        assert!(cloned.bitvector_mode);
    }

    #[test]
    fn render_context_debug() {
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let debug_str = format!("{ctx:?}");
        assert!(debug_str.contains("RenderContext"));
    }

    // ========== Additional render_expr literal tests ==========

    #[test]
    fn render_expr_int_literal_positive() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::IntLit(42);
        let result = render_expr(&expr, &var_map, ctx).unwrap();
        assert_eq!(result, "42");
    }

    #[test]
    fn render_expr_int_literal_negative() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::IntLit(-100);
        let result = render_expr(&expr, &var_map, ctx).unwrap();
        assert_eq!(result, "-100");
    }

    #[test]
    fn render_expr_bool_literal_true_value() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::BoolLit(true);
        let result = render_expr(&expr, &var_map, ctx).unwrap();
        assert_eq!(result, "true");
    }

    #[test]
    fn render_expr_bool_literal_false_value() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::BoolLit(false);
        let result = render_expr(&expr, &var_map, ctx).unwrap();
        assert_eq!(result, "false");
    }

    #[test]
    fn render_expr_var_with_mapping() {
        let mut var_map = HashMap::new();
        var_map.insert("x".to_string(), "x_mapped".to_string());
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Var("x".to_string());
        let result = render_expr(&expr, &var_map, ctx).unwrap();
        assert_eq!(result, "x_mapped");
    }

    #[test]
    fn render_expr_old_literal_renders_literal() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        // Old of a literal is just the literal value.
        let expr = Expr::Old(Box::new(Expr::IntLit(5)));
        let result = render_expr(&expr, &var_map, ctx).unwrap();
        assert_eq!(result, "5");
    }

    #[test]
    fn render_expr_old_complex_expr_renders_with_old_vars() {
        let mut var_map = HashMap::new();
        var_map.insert("x".to_string(), "x_var".to_string());
        var_map.insert("y".to_string(), "y_var".to_string());
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let expr = Expr::Old(Box::new(Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        )));
        let result = render_expr(&expr, &var_map, ctx).unwrap();
        assert_eq!(result, "(old_x_var + old_y_var)");
    }

    // ========== Additional render_predicate tests ==========

    #[test]
    fn render_predicate_or_single_element() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let pred = Predicate::Or(vec![Predicate::Expr(Expr::BoolLit(false))]);
        let result = render_predicate(&pred, &var_map, ctx).unwrap();
        assert_eq!(result, "false");
    }

    #[test]
    fn render_predicate_nested_complex() {
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: false,
        };
        let pred = Predicate::And(vec![
            Predicate::Not(Box::new(Predicate::Expr(Expr::BoolLit(false)))),
            Predicate::Or(vec![
                Predicate::Expr(Expr::BoolLit(true)),
                Predicate::Expr(Expr::BoolLit(false)),
            ]),
        ]);
        let result = render_predicate(&pred, &var_map, ctx).unwrap();
        assert_eq!(result, "(!(false) && (true || false))");
    }

    // ========== Additional render_checked_overflow tests ==========

    #[test]
    fn render_checked_overflow_with_var_mapping() {
        let mut var_map = HashMap::new();
        var_map.insert("x".to_string(), "x_arg".to_string());
        var_map.insert("y".to_string(), "y_arg".to_string());
        let a = Expr::Var("x".to_string());
        let b = Expr::Var("y".to_string());
        let result = render_checked_overflow(ArithOp::Add, &[&a, &b], &var_map).unwrap();
        assert_eq!(result, "(x_arg).checked_add(y_arg).is_some()");
    }

    // ========== Additional join_bool tests ==========

    #[test]
    fn join_bool_multiple_or() {
        let result = join_bool(
            "||",
            vec!["a".to_string(), "b".to_string(), "c".to_string()],
        );
        assert_eq!(result, "(a || b || c)");
    }

    // ========== Additional exprs_structurally_equal tests (v472) ==========

    #[test]
    fn exprs_structurally_equal_comparison_ops_return_false() {
        // Comparison operators are not handled by exprs_structurally_equal (catch-all returns false)
        let ge1 = Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        let ge2 = Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        // Even structurally identical Ge expressions return false (conservative)
        assert!(!exprs_structurally_equal(&ge1, &ge2));

        let le1 = Expr::Le(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(100)),
        );
        let le2 = Expr::Le(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(100)),
        );
        assert!(!exprs_structurally_equal(&le1, &le2));

        let lt1 = Expr::Lt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        let lt2 = Expr::Lt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        );
        assert!(!exprs_structurally_equal(&lt1, &lt2));

        let gt1 = Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(-1)),
        );
        let gt2 = Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(-1)),
        );
        assert!(!exprs_structurally_equal(&gt1, &gt2));
    }

    #[test]
    fn exprs_structurally_equal_eq_ne_return_false() {
        // Eq and Ne are comparison expressions, not arithmetic - also return false
        let eq1 = Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        let eq2 = Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert!(!exprs_structurally_equal(&eq1, &eq2));

        let ne1 = Expr::Ne(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        let ne2 = Expr::Ne(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert!(!exprs_structurally_equal(&ne1, &ne2));
    }

    #[test]
    fn exprs_structurally_equal_logical_ops_return_false() {
        // Logical operators are not handled by exprs_structurally_equal
        let and1 = Expr::And(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::BoolLit(false)),
        );
        let and2 = Expr::And(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::BoolLit(false)),
        );
        assert!(!exprs_structurally_equal(&and1, &and2));

        let or1 = Expr::Or(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::BoolLit(false)),
        );
        let or2 = Expr::Or(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::BoolLit(false)),
        );
        assert!(!exprs_structurally_equal(&or1, &or2));

        let not1 = Expr::Not(Box::new(Expr::BoolLit(true)));
        let not2 = Expr::Not(Box::new(Expr::BoolLit(true)));
        assert!(!exprs_structurally_equal(&not1, &not2));
    }

    #[test]
    fn exprs_structurally_equal_deeply_nested() {
        // Deeply nested arithmetic expressions
        let a = Expr::Add(
            Box::new(Expr::Mul(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(2)),
            )),
            Box::new(Expr::Sub(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
        );
        let b = Expr::Add(
            Box::new(Expr::Mul(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(2)),
            )),
            Box::new(Expr::Sub(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
        );
        let c = Expr::Add(
            Box::new(Expr::Mul(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(3)), // Different value
            )),
            Box::new(Expr::Sub(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
        );
        assert!(exprs_structurally_equal(&a, &b));
        assert!(!exprs_structurally_equal(&a, &c));
    }

    #[test]
    fn exprs_structurally_equal_old_nested_arithmetic() {
        // Old expressions containing arithmetic
        let a = Expr::Old(Box::new(Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        )));
        let b = Expr::Old(Box::new(Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        )));
        let c = Expr::Old(Box::new(Expr::Add(
            Box::new(Expr::Var("y".to_string())), // Different var
            Box::new(Expr::IntLit(1)),
        )));
        assert!(exprs_structurally_equal(&a, &b));
        assert!(!exprs_structurally_equal(&a, &c));
    }

    #[test]
    fn exprs_structurally_equal_mixed_operations_order_matters() {
        // Different operations at same position should not be equal
        let add_then_sub = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        let sub_then_add = Expr::Sub(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        assert!(!exprs_structurally_equal(&add_then_sub, &sub_then_add));
    }

    // ========== Additional extract_arith_op tests (v472) ==========

    #[test]
    fn extract_arith_op_nested_arithmetic() {
        // Outer operation is what gets extracted, not inner
        let expr = Expr::Add(
            Box::new(Expr::Mul(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(2)),
            )),
            Box::new(Expr::Var("y".to_string())),
        );
        let result = extract_arith_op(&expr);
        assert!(result.is_some());
        let (op, operands) = result.unwrap();
        assert!(matches!(op, ArithOp::Add));
        assert_eq!(operands.len(), 2);
    }

    #[test]
    fn extract_arith_op_comparison_ops_return_none() {
        // Comparison expressions are not arithmetic ops
        assert!(
            extract_arith_op(&Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0))
            ))
            .is_none()
        );
        assert!(
            extract_arith_op(&Expr::Le(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100))
            ))
            .is_none()
        );
        assert!(
            extract_arith_op(&Expr::Lt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(5))
            ))
            .is_none()
        );
        assert!(
            extract_arith_op(&Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(-1))
            ))
            .is_none()
        );
        assert!(
            extract_arith_op(&Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0))
            ))
            .is_none()
        );
        assert!(
            extract_arith_op(&Expr::Ne(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0))
            ))
            .is_none()
        );
    }

    #[test]
    fn extract_arith_op_logical_ops_return_none() {
        // Logical expressions are not arithmetic ops
        assert!(
            extract_arith_op(&Expr::And(
                Box::new(Expr::BoolLit(true)),
                Box::new(Expr::BoolLit(false))
            ))
            .is_none()
        );
        assert!(
            extract_arith_op(&Expr::Or(
                Box::new(Expr::BoolLit(true)),
                Box::new(Expr::BoolLit(false))
            ))
            .is_none()
        );
        assert!(extract_arith_op(&Expr::Not(Box::new(Expr::BoolLit(true)))).is_none());
    }

    #[test]
    fn extract_arith_op_old_and_struct_field_return_none() {
        // Old and StructField are not arithmetic ops
        assert!(extract_arith_op(&Expr::Old(Box::new(Expr::Var("x".to_string())))).is_none());
        assert!(
            extract_arith_op(&Expr::StructField(
                Box::new(Expr::Var("s".to_string())),
                "field".to_string()
            ))
            .is_none()
        );
    }

    // ========== Additional join_bool tests (v472) ==========

    #[test]
    fn join_bool_empty_list() {
        // Empty list returns "true" (identity for conjunction/disjunction base case)
        let result = join_bool("&&", vec![]);
        assert_eq!(result, "true");
    }

    #[test]
    fn join_bool_single_element() {
        // Single element is returned unwrapped
        let result = join_bool("&&", vec!["a".to_string()]);
        assert_eq!(result, "a");
    }

    #[test]
    fn join_bool_two_elements_and() {
        let result = join_bool("&&", vec!["a".to_string(), "b".to_string()]);
        assert_eq!(result, "(a && b)");
    }

    #[test]
    fn join_bool_two_elements_or() {
        let result = join_bool("||", vec!["x".to_string(), "y".to_string()]);
        assert_eq!(result, "(x || y)");
    }

    #[test]
    fn join_bool_complex_expressions() {
        let result = join_bool(
            "&&",
            vec![
                "(a > 0)".to_string(),
                "(b < 100)".to_string(),
                "(c != 0)".to_string(),
            ],
        );
        assert_eq!(result, "((a > 0) && (b < 100) && (c != 0))");
    }

    // ========== export_vc_to_kani_harness tests (v478) ==========

    use crate::{SourceSpan, VcId};
    use std::sync::Arc;

    // Helper to create a test SourceSpan
    fn test_span() -> SourceSpan {
        SourceSpan {
            file: Arc::<str>::from("test.swift"),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 10,
        }
    }

    // Helper to create a simple FunctionSignature
    fn test_sig(params: Vec<(&str, VcType)>, return_type: VcType) -> FunctionSignature {
        FunctionSignature {
            name: "test_func".to_string(),
            params: params
                .into_iter()
                .map(|(n, t)| (n.to_string(), t))
                .collect(),
            return_type,
        }
    }

    // Helper to create a VerificationCondition
    fn test_vc(name: &str, condition: VcKind) -> VerificationCondition {
        VerificationCondition {
            id: VcId(0),
            name: name.to_string(),
            span: test_span(),
            condition,
            preferred_backend: None,
        }
    }

    #[test]
    fn export_vc_unknown_variable_error() {
        // VC references a variable not in the function signature
        let sig = test_sig(
            vec![(
                "x",
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "test_vc",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("unknown_var".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(
            matches!(result, Err(KaniExportError::UnknownVariable(ref v)) if v == "unknown_var")
        );
    }

    #[test]
    fn export_vc_unsupported_param_type_abstract() {
        // Parameter with Abstract type (e.g., Optional) should fail
        let sig = test_sig(
            vec![("x", VcType::Abstract("Optional<Int>".to_string()))],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "test_vc",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(matches!(
            result,
            Err(KaniExportError::UnsupportedParamType(_))
        ));
    }

    #[test]
    fn export_vc_unsupported_param_type_array() {
        // Parameter with Array type should fail
        let sig = test_sig(
            vec![(
                "arr",
                VcType::Array {
                    elem: Box::new(VcType::Int {
                        signed: true,
                        bits: 64,
                    }),
                    len: None,
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "test_vc",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("arr".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(matches!(
            result,
            Err(KaniExportError::UnsupportedParamType(_))
        ));
    }

    #[test]
    fn export_vc_unsupported_result_type() {
        // Result type with Abstract should fail when result is referenced
        let sig = test_sig(
            vec![(
                "x",
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            VcType::Abstract("Optional<Int>".to_string()),
        );
        let vc = test_vc(
            "test_vc",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Result),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(matches!(
            result,
            Err(KaniExportError::UnsupportedParamType(_))
        ));
    }

    #[test]
    fn export_vc_simple_predicate_success() {
        // Basic successful export
        let sig = test_sig(
            vec![(
                "x",
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = VerificationCondition {
            id: VcId(1),
            name: "positive_check".to_string(),
            span: SourceSpan {
                file: Arc::<str>::from("test.swift"),
                line_start: 10,
                col_start: 5,
                line_end: 10,
                col_end: 15,
            },
            condition: VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
            preferred_backend: None,
        };
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(result.is_ok());
        let harness = result.unwrap();
        assert!(harness.contains("#[kani::proof]"));
        assert!(harness.contains("fn proof_positive_check()"));
        assert!(harness.contains("let x: i128 = kani::any()"));
    }

    #[test]
    fn export_vc_with_result_reference() {
        // VC that references result value
        let sig = test_sig(
            vec![(
                "x",
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "result_check",
            VcKind::Predicate(Predicate::Expr(Expr::Ge(
                Box::new(Expr::Result),
                Box::new(Expr::Var("x".to_string())),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(result.is_ok());
        let harness = result.unwrap();
        assert!(harness.contains("let result: i128 = kani::any()"));
    }

    #[test]
    fn export_vc_with_bool_param() {
        // VC with bool parameter
        let sig = test_sig(vec![("flag", VcType::Bool)], VcType::Bool);
        let vc = test_vc(
            "bool_check",
            VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("flag".to_string())),
                Box::new(Expr::BoolLit(true)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(result.is_ok());
        let harness = result.unwrap();
        assert!(harness.contains("let flag: bool = kani::any()"));
    }

    #[test]
    fn export_vc_bitvector_mode() {
        // Export with bitvector mode enabled
        let sig = test_sig(
            vec![(
                "x",
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            VcType::Int {
                signed: true,
                bits: 32,
            },
        );
        let vc = test_vc(
            "bitvector_check",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let config = KaniExportConfig {
            bitvector_mode: true,
            ..Default::default()
        };
        let result = export_vc_to_kani_harness_with_config(&sig, &vc, &config);
        assert!(result.is_ok());
        let harness = result.unwrap();
        assert!(harness.contains("let x: i32 = kani::any()"));
        assert!(harness.contains("MODE: Bitvector"));
    }

    #[test]
    fn export_vc_with_preconditions() {
        // Export with preconditions
        let sig = test_sig(
            vec![(
                "x",
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "precond_check",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let config = KaniExportConfig {
            preconditions: vec![Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))],
            ..Default::default()
        };
        let result = export_vc_to_kani_harness_with_config(&sig, &vc, &config);
        assert!(result.is_ok());
        let harness = result.unwrap();
        assert!(harness.contains("kani::assume"));
    }

    #[test]
    fn export_vc_implies_condition() {
        // Export a VC with Implies condition
        let sig = test_sig(
            vec![(
                "x",
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "implies_check",
            VcKind::Implies {
                antecedent: Predicate::Expr(Expr::Gt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                consequent: Predicate::Expr(Expr::Ge(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(1)),
                )),
            },
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(result.is_ok());
        let harness = result.unwrap();
        assert!(harness.contains("kani::assume"));
        assert!(harness.contains("kani::assert"));
    }

    #[test]
    fn export_vc_termination_condition() {
        // Export a VC with Termination condition
        let sig = test_sig(
            vec![(
                "n",
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "termination_check",
            VcKind::Termination {
                measure: Expr::Var("n".to_string()),
                next_measure: Expr::Sub(
                    Box::new(Expr::Var("n".to_string())),
                    Box::new(Expr::IntLit(1)),
                ),
                initial_measure: Some(Expr::IntLit(10)),
                loop_label: "bb1".to_string(),
            },
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(result.is_ok());
        let harness = result.unwrap();
        // Should check measure >= 0 and decreased < measure
        assert!(harness.contains("kani::assert"));
    }

    #[test]
    fn export_vc_with_float_param() {
        // VC with float parameter (symbolic, not verified)
        let sig = test_sig(
            vec![("f", VcType::Float { bits: 64 })],
            VcType::Float { bits: 64 },
        );
        let vc = test_vc(
            "float_check",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("f".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(result.is_ok());
        let harness = result.unwrap();
        assert!(harness.contains("let f: f64 = kani::any()"));
        assert!(harness.contains("symbolic"));
    }

    #[test]
    fn export_vc_collect_vars_from_old_in_vc() {
        // Ensure old() references in VCs are collected and result in old_x variable
        let sig = test_sig(
            vec![(
                "x",
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "old_check",
            VcKind::Predicate(Predicate::Expr(Expr::Ge(
                Box::new(Expr::Result),
                Box::new(Expr::Old(Box::new(Expr::Var("x".to_string())))),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(result.is_ok());
        let harness = result.unwrap();
        assert!(harness.contains("let old_x"));
    }

    #[test]
    fn export_vc_collect_vars_from_complex_old_in_vc() {
        // Ensure old(x + y) references are collected and result in old_x/old_y variables.
        let sig = test_sig(
            vec![
                (
                    "x",
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
                (
                    "y",
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
            ],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "old_complex_check",
            VcKind::Predicate(Predicate::Expr(Expr::Ge(
                Box::new(Expr::Result),
                Box::new(Expr::Old(Box::new(Expr::Add(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::Var("y".to_string())),
                )))),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(result.is_ok());
        let harness = result.unwrap();
        assert!(harness.contains("let old_x"));
        assert!(harness.contains("let old_y"));
        assert!(harness.contains("old_x"));
        assert!(harness.contains("old_y"));
    }

    #[test]
    fn export_vc_sanitizes_special_chars_in_name() {
        // VC with special characters in name should be sanitized
        let sig = test_sig(
            vec![(
                "x",
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "check-with-dashes.and.dots",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(result.is_ok());
        let harness = result.unwrap();
        // Should sanitize to valid Rust identifier in the function name
        assert!(harness.contains("fn proof_check_with_dashes_and_dots()"));
        // The function name should not contain special characters (sanitize replaces them with underscores)
        assert!(!harness.contains("fn proof_check-"));
    }

    #[test]
    fn export_vc_unsupported_param_type_ref() {
        // Parameter with Ref type should fail
        let sig = test_sig(
            vec![(
                "ptr",
                VcType::Ref {
                    mutable: true,
                    inner: Box::new(VcType::Int {
                        signed: true,
                        bits: 64,
                    }),
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "test_vc",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("ptr".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(matches!(
            result,
            Err(KaniExportError::UnsupportedParamType(_))
        ));
    }

    #[test]
    fn export_vc_unsupported_param_type_tuple() {
        // Parameter with Tuple type should fail
        let sig = test_sig(
            vec![(
                "tup",
                VcType::Tuple(vec![
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                    VcType::Bool,
                ]),
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "test_vc",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("tup".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(matches!(
            result,
            Err(KaniExportError::UnsupportedParamType(_))
        ));
    }

    #[test]
    fn export_vc_unsupported_param_type_struct() {
        // Parameter with Struct type should fail
        let sig = test_sig(
            vec![(
                "s",
                VcType::Struct {
                    name: "Point".to_string(),
                    fields: vec![(
                        "x".to_string(),
                        VcType::Int {
                            signed: true,
                            bits: 64,
                        },
                    )],
                },
            )],
            VcType::Int {
                signed: true,
                bits: 64,
            },
        );
        let vc = test_vc(
            "test_vc",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("s".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(matches!(
            result,
            Err(KaniExportError::UnsupportedParamType(_))
        ));
    }

    #[test]
    fn export_vc_with_float32_param() {
        // VC with f32 float parameter
        let sig = test_sig(
            vec![("f", VcType::Float { bits: 32 })],
            VcType::Float { bits: 32 },
        );
        let vc = test_vc(
            "float32_check",
            VcKind::Predicate(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("f".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let result = export_vc_to_kani_harness(&sig, &vc);
        assert!(result.is_ok());
        let harness = result.unwrap();
        assert!(harness.contains("let f: f32 = kani::any()"));
    }

    // ========== extract_arith_op tests (v479) ==========

    #[test]
    fn extract_arith_op_add_returns_correct_op_and_operands() {
        let expr = Expr::Add(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        let result = extract_arith_op(&expr);
        assert!(result.is_some());
        let (op, operands) = result.unwrap();
        assert!(matches!(op, ArithOp::Add));
        assert_eq!(operands.len(), 2);
    }

    #[test]
    fn extract_arith_op_sub_returns_correct_op() {
        let expr = Expr::Sub(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        let result = extract_arith_op(&expr);
        assert!(result.is_some());
        let (op, _) = result.unwrap();
        assert!(matches!(op, ArithOp::Sub));
    }

    #[test]
    fn extract_arith_op_mul_returns_correct_op() {
        let expr = Expr::Mul(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        let result = extract_arith_op(&expr);
        assert!(result.is_some());
        let (op, operands) = result.unwrap();
        assert!(matches!(op, ArithOp::Mul));
        assert_eq!(operands.len(), 2);
    }

    #[test]
    fn extract_arith_op_div_returns_correct_op() {
        let expr = Expr::Div(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let result = extract_arith_op(&expr);
        assert!(result.is_some());
        let (op, _) = result.unwrap();
        assert!(matches!(op, ArithOp::Div));
    }

    #[test]
    fn extract_arith_op_rem_returns_correct_op() {
        let expr = Expr::Rem(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(10)),
        );
        let result = extract_arith_op(&expr);
        assert!(result.is_some());
        let (op, _) = result.unwrap();
        assert!(matches!(op, ArithOp::Rem));
    }

    #[test]
    fn extract_arith_op_neg_returns_single_operand() {
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        let result = extract_arith_op(&expr);
        assert!(result.is_some());
        let (op, operands) = result.unwrap();
        assert!(matches!(op, ArithOp::Neg));
        assert_eq!(operands.len(), 1);
    }

    #[test]
    fn extract_arith_op_comparison_returns_none() {
        // Comparison operators should return None
        let expr = Expr::Gt(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert!(extract_arith_op(&expr).is_none());
    }

    #[test]
    fn extract_arith_op_var_expr_returns_none() {
        let expr = Expr::Var("x".to_string());
        assert!(extract_arith_op(&expr).is_none());
    }

    #[test]
    fn extract_arith_op_literal_returns_none() {
        let expr = Expr::IntLit(42);
        assert!(extract_arith_op(&expr).is_none());
    }

    #[test]
    fn extract_arith_op_bool_returns_none() {
        let expr = Expr::BoolLit(true);
        assert!(extract_arith_op(&expr).is_none());
    }

    #[test]
    fn extract_arith_op_eq_returns_none() {
        let expr = Expr::Eq(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert!(extract_arith_op(&expr).is_none());
    }

    #[test]
    fn extract_arith_op_and_returns_none() {
        let expr = Expr::And(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::BoolLit(false)),
        );
        assert!(extract_arith_op(&expr).is_none());
    }

    // ========== ArithOp::checked_method tests (v479) ==========

    #[test]
    fn arith_op_add_checked_method() {
        assert_eq!(ArithOp::Add.checked_method(), "checked_add");
    }

    #[test]
    fn arith_op_sub_checked_method() {
        assert_eq!(ArithOp::Sub.checked_method(), "checked_sub");
    }

    #[test]
    fn arith_op_mul_checked_method() {
        assert_eq!(ArithOp::Mul.checked_method(), "checked_mul");
    }

    #[test]
    fn arith_op_div_checked_method() {
        assert_eq!(ArithOp::Div.checked_method(), "checked_div");
    }

    #[test]
    fn arith_op_rem_checked_method() {
        assert_eq!(ArithOp::Rem.checked_method(), "checked_rem");
    }

    #[test]
    fn arith_op_neg_checked_method() {
        assert_eq!(ArithOp::Neg.checked_method(), "checked_neg");
    }

    // ========== render_checked_overflow additional tests (v479) ==========

    #[test]
    fn render_checked_overflow_with_variable_mapping() {
        let a = Expr::Var("input".to_string());
        let b = Expr::IntLit(5);
        let operands = vec![&a, &b];
        let mut var_map = HashMap::new();
        var_map.insert("input".to_string(), "mapped_input".to_string());
        let result = render_checked_overflow(ArithOp::Add, &operands, &var_map);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "(mapped_input).checked_add(5).is_some()");
    }

    #[test]
    fn render_checked_overflow_nested_arithmetic() {
        // (a + b) * c -> should render operands without wrapping
        let a_plus_b = Expr::Add(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        let c = Expr::Var("c".to_string());
        let operands = vec![&a_plus_b, &c];
        let var_map = HashMap::new();
        let result = render_checked_overflow(ArithOp::Mul, &operands, &var_map);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "((a + b)).checked_mul(c).is_some()");
    }

    #[test]
    fn render_checked_overflow_sub_with_two_vars() {
        let a = Expr::Var("x".to_string());
        let b = Expr::Var("y".to_string());
        let operands = vec![&a, &b];
        let var_map = HashMap::new();
        let result = render_checked_overflow(ArithOp::Sub, &operands, &var_map);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "(x).checked_sub(y).is_some()");
    }

    #[test]
    fn render_checked_overflow_div_with_mapped_vars() {
        let a = Expr::Var("num".to_string());
        let b = Expr::Var("den".to_string());
        let operands = vec![&a, &b];
        let mut var_map = HashMap::new();
        var_map.insert("num".to_string(), "numerator".to_string());
        var_map.insert("den".to_string(), "denominator".to_string());
        let result = render_checked_overflow(ArithOp::Div, &operands, &var_map);
        assert!(result.is_ok());
        assert_eq!(
            result.unwrap(),
            "(numerator).checked_div(denominator).is_some()"
        );
    }

    // ========== try_render_overflow_check additional tests (v479) ==========

    #[test]
    fn try_render_overflow_check_not_predicate() {
        let pred = Predicate::Not(Box::new(Predicate::Expr(Expr::BoolLit(false))));
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let result = try_render_overflow_check(&pred, &var_map, ctx);
        assert!(result.is_none());
    }

    #[test]
    fn try_render_overflow_check_implies_predicate() {
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::BoolLit(true))),
            Box::new(Predicate::Expr(Expr::BoolLit(true))),
        );
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let result = try_render_overflow_check(&pred, &var_map, ctx);
        assert!(result.is_none());
    }

    #[test]
    fn try_render_overflow_check_or_predicate() {
        let pred = Predicate::Or(vec![
            Predicate::Expr(Expr::BoolLit(true)),
            Predicate::Expr(Expr::BoolLit(false)),
        ]);
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let result = try_render_overflow_check(&pred, &var_map, ctx);
        assert!(result.is_none());
    }

    #[test]
    fn try_render_overflow_check_and_three_elements() {
        // And with 3 elements should return None (expects exactly 2)
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::BoolLit(true)),
            Predicate::Expr(Expr::BoolLit(true)),
            Predicate::Expr(Expr::BoolLit(true)),
        ]);
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let result = try_render_overflow_check(&pred, &var_map, ctx);
        assert!(result.is_none());
    }

    #[test]
    fn try_render_overflow_check_and_one_element() {
        let pred = Predicate::And(vec![Predicate::Expr(Expr::BoolLit(true))]);
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let result = try_render_overflow_check(&pred, &var_map, ctx);
        assert!(result.is_none());
    }

    #[test]
    fn try_render_overflow_check_simple_gt_expr() {
        // A simple Gt that doesn't match the overflow pattern
        let pred = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let var_map = HashMap::new();
        let ctx = RenderContext {
            bitvector_mode: true,
        };
        let result = try_render_overflow_check(&pred, &var_map, ctx);
        assert!(result.is_none());
    }

    // ========== try_render_overflow_check_from_exprs additional tests (v479) ==========

    #[test]
    fn try_render_overflow_check_from_exprs_mul_pattern_i64_bounds() {
        let mul_expr = Expr::Mul(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let ge_expr = Expr::Ge(
            Box::new(mul_expr.clone()),
            Box::new(Expr::IntLit(i128::from(i64::MIN))),
        );
        let le_expr = Expr::Le(
            Box::new(mul_expr),
            Box::new(Expr::IntLit(i128::from(i64::MAX))),
        );
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&ge_expr, &le_expr, &var_map);
        assert!(result.is_some());
        let rendered = result.unwrap();
        assert!(rendered.is_ok());
        assert_eq!(rendered.unwrap(), "(x).checked_mul(y).is_some()");
    }

    #[test]
    fn try_render_overflow_check_from_exprs_ge_non_int_bound() {
        let add_expr = Expr::Add(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        let ge_expr = Expr::Ge(
            Box::new(add_expr.clone()),
            Box::new(Expr::Var("min".to_string())), // Variable instead of IntLit
        );
        let le_expr = Expr::Le(Box::new(add_expr), Box::new(Expr::IntLit(100)));
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&ge_expr, &le_expr, &var_map);
        assert!(result.is_none());
    }

    #[test]
    fn try_render_overflow_check_from_exprs_le_non_int_bound() {
        let add_expr = Expr::Add(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        let ge_expr = Expr::Ge(Box::new(add_expr.clone()), Box::new(Expr::IntLit(-100)));
        let le_expr = Expr::Le(
            Box::new(add_expr),
            Box::new(Expr::Var("max".to_string())), // Variable instead of IntLit
        );
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&ge_expr, &le_expr, &var_map);
        assert!(result.is_none());
    }

    #[test]
    fn try_render_overflow_check_from_exprs_gt_instead_of_ge() {
        // First expr is Gt instead of Ge
        let add_expr = Expr::Add(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        let gt_expr = Expr::Gt(Box::new(add_expr.clone()), Box::new(Expr::IntLit(-100)));
        let le_expr = Expr::Le(Box::new(add_expr), Box::new(Expr::IntLit(100)));
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&gt_expr, &le_expr, &var_map);
        assert!(result.is_none());
    }

    #[test]
    fn try_render_overflow_check_from_exprs_lt_instead_of_le() {
        // Second expr is Lt instead of Le
        let add_expr = Expr::Add(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        let ge_expr = Expr::Ge(Box::new(add_expr.clone()), Box::new(Expr::IntLit(-100)));
        let lt_expr = Expr::Lt(Box::new(add_expr), Box::new(Expr::IntLit(100)));
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&ge_expr, &lt_expr, &var_map);
        assert!(result.is_none());
    }

    #[test]
    fn try_render_overflow_check_from_exprs_plain_var_not_arith() {
        // Expression is not an arithmetic operation
        let var_expr = Expr::Var("x".to_string());
        let ge_expr = Expr::Ge(Box::new(var_expr.clone()), Box::new(Expr::IntLit(-100)));
        let le_expr = Expr::Le(Box::new(var_expr), Box::new(Expr::IntLit(100)));
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&ge_expr, &le_expr, &var_map);
        assert!(result.is_none());
    }

    #[test]
    fn try_render_overflow_check_from_exprs_sub_pattern() {
        let sub_expr = Expr::Sub(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        let ge_expr = Expr::Ge(
            Box::new(sub_expr.clone()),
            Box::new(Expr::IntLit(i128::from(i32::MIN))),
        );
        let le_expr = Expr::Le(
            Box::new(sub_expr),
            Box::new(Expr::IntLit(i128::from(i32::MAX))),
        );
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&ge_expr, &le_expr, &var_map);
        assert!(result.is_some());
        let rendered = result.unwrap();
        assert!(rendered.is_ok());
        assert_eq!(rendered.unwrap(), "(a).checked_sub(b).is_some()");
    }

    #[test]
    fn try_render_overflow_check_from_exprs_div_pattern() {
        let div_expr = Expr::Div(
            Box::new(Expr::Var("num".to_string())),
            Box::new(Expr::Var("den".to_string())),
        );
        let ge_expr = Expr::Ge(
            Box::new(div_expr.clone()),
            Box::new(Expr::IntLit(i128::from(i64::MIN))),
        );
        let le_expr = Expr::Le(
            Box::new(div_expr),
            Box::new(Expr::IntLit(i128::from(i64::MAX))),
        );
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&ge_expr, &le_expr, &var_map);
        assert!(result.is_some());
        let rendered = result.unwrap();
        assert!(rendered.is_ok());
        assert_eq!(rendered.unwrap(), "(num).checked_div(den).is_some()");
    }

    #[test]
    fn try_render_overflow_check_from_exprs_rem_pattern() {
        let rem_expr = Expr::Rem(
            Box::new(Expr::Var("n".to_string())),
            Box::new(Expr::IntLit(7)),
        );
        let ge_expr = Expr::Ge(Box::new(rem_expr.clone()), Box::new(Expr::IntLit(-100)));
        let le_expr = Expr::Le(Box::new(rem_expr), Box::new(Expr::IntLit(100)));
        let var_map = HashMap::new();
        let result = try_render_overflow_check_from_exprs(&ge_expr, &le_expr, &var_map);
        assert!(result.is_some());
        let rendered = result.unwrap();
        assert!(rendered.is_ok());
        assert_eq!(rendered.unwrap(), "(n).checked_rem(7).is_some()");
    }
}
