//! Condition string parser for verification conditions.
//!
//! This module parses condition strings like "x > 0", "result >= x",
//! "a && b || c" into `SwiftExpr` AST nodes for verification.
//!
//! # Supported Syntax
//!
//! - **Literals**: `true`, `false`, integers (`42`, `-5`), `nil`, `result`
//! - **References**: parameter names (`x`, `y`), `result` (return value)
//! - **Comparisons**: `==`, `!=`, `<`, `<=`, `>`, `>=`
//! - **Arithmetic**: `+`, `-`, `*`, `/`, `%`
//! - **Logical**: `&&`, `||`, `!`
//! - **Field access**: `x.count`, `self.value`
//! - **Parentheses**: `(a + b) * c`
//!
//! # Example
//!
//! ```
//! use vc_ir_swift::condition_parser::parse_condition;
//! use vc_ir_swift::SwiftExpr;
//! use std::collections::HashMap;
//!
//! let params: HashMap<String, usize> = [("x".to_string(), 0)].into_iter().collect();
//! let expr = parse_condition("x > 0", &params);
//!
//! // Result is: Gt { lhs: ParamRef { name: "x", index: 0 }, rhs: IntLit { value: 0 } }
//! assert!(matches!(expr, SwiftExpr::Gt { .. }));
//! ```

use crate::json_types::SwiftExpr;
use std::collections::HashMap;

/// Parse a condition string into a `SwiftExpr`.
///
/// # Arguments
/// * `condition` - The condition string to parse (e.g., "x > 0")
/// * `params` - Map from parameter names to their indices
///
/// # Returns
/// A `SwiftExpr` representing the parsed condition
#[must_use]
#[allow(clippy::implicit_hasher)] // Generic hasher not needed for internal API
pub fn parse_condition(condition: &str, params: &HashMap<String, usize>) -> SwiftExpr {
    parse_condition_impl(condition.trim(), params)
}

/// Parse a condition string with an empty parameter map.
///
/// Useful when parameter indices aren't known or relevant.
#[must_use]
pub fn parse_condition_simple(condition: &str) -> SwiftExpr {
    let empty: HashMap<String, usize> = HashMap::new();
    parse_condition_impl(condition.trim(), &empty)
}

/// Internal parsing implementation.
#[allow(clippy::too_many_lines)]
fn parse_condition_impl(cond: &str, params: &HashMap<String, usize>) -> SwiftExpr {
    let cond = cond.trim();

    // Handle boolean literals
    if cond == "true" {
        return SwiftExpr::BoolLit { value: true };
    }
    if cond == "false" {
        return SwiftExpr::BoolLit { value: false };
    }

    // Handle parenthesized expressions
    if is_wrapped_in_parens(cond) {
        return parse_condition_impl(&cond[1..cond.len() - 1], params);
    }

    // Handle logical operators (lowest precedence, left to right)
    if let Some(idx) = find_operator_outside_parens(cond, "||") {
        let lhs = parse_condition_impl(&cond[..idx], params);
        let rhs = parse_condition_impl(&cond[idx + 2..], params);
        return SwiftExpr::Or {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };
    }

    if let Some(idx) = find_operator_outside_parens(cond, "&&") {
        let lhs = parse_condition_impl(&cond[..idx], params);
        let rhs = parse_condition_impl(&cond[idx + 2..], params);
        return SwiftExpr::And {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };
    }

    // Handle comparison operators (check multi-char ops first)
    for (op_str, make_expr) in [
        (
            ">=",
            make_ge as fn(Box<SwiftExpr>, Box<SwiftExpr>) -> SwiftExpr,
        ),
        ("<=", make_le),
        ("==", make_eq),
        ("!=", make_ne),
        (">", make_gt),
        ("<", make_lt),
    ] {
        if let Some(idx) = find_operator_outside_parens(cond, op_str) {
            let lhs = parse_condition_impl(&cond[..idx], params);
            let rhs = parse_condition_impl(&cond[idx + op_str.len()..], params);
            return make_expr(Box::new(lhs), Box::new(rhs));
        }
    }

    // Handle arithmetic operators (+ and - first, then * / %)
    if let Some(idx) = find_additive_operator_outside_parens(cond) {
        // idx is a byte offset from find_additive_operator_outside_parens,
        // so use byte access instead of chars().nth() which uses char offset
        let op = cond.as_bytes()[idx] as char;
        let lhs = parse_condition_impl(&cond[..idx], params);
        let rhs = parse_condition_impl(&cond[idx + 1..], params);
        return if op == '+' {
            SwiftExpr::Add {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            }
        } else {
            SwiftExpr::Sub {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            }
        };
    }

    if let Some(idx) = find_operator_outside_parens(cond, "*") {
        let lhs = parse_condition_impl(&cond[..idx], params);
        let rhs = parse_condition_impl(&cond[idx + 1..], params);
        return SwiftExpr::Mul {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };
    }

    if let Some(idx) = find_operator_outside_parens(cond, "/") {
        let lhs = parse_condition_impl(&cond[..idx], params);
        let rhs = parse_condition_impl(&cond[idx + 1..], params);
        return SwiftExpr::Div {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };
    }

    if let Some(idx) = find_operator_outside_parens(cond, "%") {
        let lhs = parse_condition_impl(&cond[..idx], params);
        let rhs = parse_condition_impl(&cond[idx + 1..], params);
        return SwiftExpr::Mod {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        };
    }

    // Handle unary NOT
    if let Some(rest) = cond.strip_prefix('!') {
        let operand = parse_condition_impl(rest, params);
        return SwiftExpr::Not {
            operand: Box::new(operand),
        };
    }

    // Handle unary minus for negative numbers
    if let Some(rest) = cond.strip_prefix('-') {
        if !rest.is_empty() {
            // Check if it's just a negative integer literal
            if let Ok(value) = cond.parse::<i64>() {
                return SwiftExpr::IntLit { value };
            }
            let operand = parse_condition_impl(rest, params);
            return SwiftExpr::Neg {
                operand: Box::new(operand),
            };
        }
    }

    // Handle result reference
    if cond == "result" {
        return SwiftExpr::ResultRef;
    }

    // Handle nil literal
    if cond == "nil" {
        return SwiftExpr::NilLit;
    }

    // Handle integer literals
    if let Ok(value) = cond.parse::<i64>() {
        return SwiftExpr::IntLit { value };
    }

    // Handle field access: base.field
    if let Some(dot_idx) = find_last_dot_outside_parens(cond) {
        let base_str = &cond[..dot_idx];
        let field_str = &cond[dot_idx + 1..];

        if is_valid_field_ident(field_str) && !base_str.is_empty() {
            let base_expr = parse_condition_impl(base_str, params);
            return SwiftExpr::Field {
                base: Box::new(base_expr),
                field: field_str.trim().to_string(),
            };
        }
    }

    // Handle array indexing: base[index]
    if cond.ends_with(']') {
        if let Some(bracket_start) = find_matching_open_bracket(cond) {
            let base_str = &cond[..bracket_start];
            let index_str = &cond[bracket_start + 1..cond.len() - 1];

            if !base_str.is_empty() {
                let base_expr = parse_condition_impl(base_str, params);
                let index_expr = parse_condition_impl(index_str, params);
                return SwiftExpr::Index {
                    base: Box::new(base_expr),
                    index: Box::new(index_expr),
                };
            }
        }
    }

    // Handle function call: func(args)
    if cond.ends_with(')') {
        if let Some(paren_start) = find_matching_open_paren_for_call(cond) {
            let func_name = &cond[..paren_start];
            let args_str = &cond[paren_start + 1..cond.len() - 1];

            if is_valid_field_ident(func_name) {
                // Special case: old(expr) for postconditions
                if func_name == "old" {
                    let inner = parse_condition_impl(args_str, params);
                    return SwiftExpr::Old {
                        expr: Box::new(inner),
                    };
                }

                // Regular function call
                let args = if args_str.trim().is_empty() {
                    vec![]
                } else {
                    split_args(args_str)
                        .iter()
                        .map(|arg| parse_condition_impl(arg, params))
                        .collect()
                };
                return SwiftExpr::Call {
                    func: func_name.to_string(),
                    args,
                };
            }
        }
    }

    // Handle parameter reference
    let name = cond.to_string();
    // Parameter indices are small non-negative integers (0, 1, 2, ...) or -1 for unresolved.
    // Safe because they will never exceed i32::MAX.
    #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
    let index = params.get(&name).map_or(-1, |&i| i as i32);
    SwiftExpr::ParamRef { name, index }
}

// Helper functions

fn is_wrapped_in_parens(s: &str) -> bool {
    let s = s.trim();
    if !s.starts_with('(') || !s.ends_with(')') {
        return false;
    }

    let mut depth: i32 = 0;
    let last_idx = s.len().saturating_sub(1);
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 && i != last_idx {
                    return false;
                }
            }
            _ => {}
        }
        if depth < 0 {
            return false;
        }
    }
    depth == 0
}

fn find_operator_outside_parens(s: &str, op: &str) -> Option<usize> {
    let mut depth = 0_i32;
    let bytes = s.as_bytes();
    let op_bytes = op.as_bytes();

    for i in 0..s.len() {
        match bytes[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            _ => {}
        }

        if depth == 0 && i + op.len() <= s.len() {
            if &bytes[i..i + op.len()] == op_bytes {
                // For single-char ops like '<', make sure it's not part of '<=' or '<<'
                if op.len() == 1 {
                    let next = bytes.get(i + 1).copied();
                    if op == "<" && (next == Some(b'=') || next == Some(b'<')) {
                        continue;
                    }
                    if op == ">" && (next == Some(b'=') || next == Some(b'>')) {
                        continue;
                    }
                    if op == "=" && next == Some(b'=') {
                        continue;
                    }
                    if op == "!" && next == Some(b'=') {
                        continue;
                    }
                }
                return Some(i);
            }
        }
    }
    None
}

/// Find additive operator (+ or -) outside parentheses, handling negative numbers.
fn find_additive_operator_outside_parens(s: &str) -> Option<usize> {
    let mut depth = 0_i32;
    let bytes = s.as_bytes();

    for i in 0..s.len() {
        match bytes[i] {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth -= 1,
            _ => {}
        }

        if depth == 0 && (bytes[i] == b'+' || bytes[i] == b'-') {
            // Skip if at start (unary)
            if i == 0 {
                continue;
            }
            // Look backward past whitespace to find the actual previous token
            let mut j = i - 1;
            while j > 0 && bytes[j] == b' ' {
                j -= 1;
            }
            let prev = bytes[j];
            // Check if this is binary (previous non-space char is identifier, number, or closing paren/bracket)
            // Also check for multi-byte UTF-8 continuation bytes (high bit set) to support Unicode identifiers
            if prev.is_ascii_alphanumeric()
                || prev == b')'
                || prev == b']'
                || prev == b'_'
                || prev >= 0x80
            {
                return Some(i);
            }
        }
    }
    None
}

fn find_last_dot_outside_parens(s: &str) -> Option<usize> {
    let mut depth = 0_i32;
    let mut last_dot: Option<usize> = None;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            '.' if depth == 0 => last_dot = Some(i),
            _ => {}
        }
    }
    last_dot
}

fn is_valid_field_ident(s: &str) -> bool {
    let s = s.trim();
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    // Swift identifiers can start with a letter (including Unicode) or underscore
    if !(first.is_alphabetic() || first == '_') {
        return false;
    }
    // Rest can be letters, numbers (including Unicode), or underscores
    chars.all(|c| c.is_alphanumeric() || c == '_')
}

fn find_matching_open_bracket(s: &str) -> Option<usize> {
    // Find the '[' that matches the final ']'
    let mut depth = 0_i32;
    for (i, c) in s.char_indices().rev() {
        match c {
            ']' => depth += 1,
            '[' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

fn find_matching_open_paren_for_call(s: &str) -> Option<usize> {
    // Find the '(' that matches the final ')' for a function call
    let mut depth = 0_i32;
    for (i, c) in s.char_indices().rev() {
        match c {
            ')' => depth += 1,
            '(' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

fn split_args(s: &str) -> Vec<&str> {
    let mut args = Vec::new();
    let mut depth = 0_i32;
    let mut start = 0;

    for (i, c) in s.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                args.push(s[start..i].trim());
                start = i + 1;
            }
            _ => {}
        }
    }

    // Don't forget the last argument
    let last = s[start..].trim();
    if !last.is_empty() {
        args.push(last);
    }

    args
}

// Expression constructors for operator parsing
const fn make_ge(lhs: Box<SwiftExpr>, rhs: Box<SwiftExpr>) -> SwiftExpr {
    SwiftExpr::Ge { lhs, rhs }
}

const fn make_le(lhs: Box<SwiftExpr>, rhs: Box<SwiftExpr>) -> SwiftExpr {
    SwiftExpr::Le { lhs, rhs }
}

const fn make_eq(lhs: Box<SwiftExpr>, rhs: Box<SwiftExpr>) -> SwiftExpr {
    SwiftExpr::Eq { lhs, rhs }
}

const fn make_ne(lhs: Box<SwiftExpr>, rhs: Box<SwiftExpr>) -> SwiftExpr {
    SwiftExpr::Ne { lhs, rhs }
}

const fn make_gt(lhs: Box<SwiftExpr>, rhs: Box<SwiftExpr>) -> SwiftExpr {
    SwiftExpr::Gt { lhs, rhs }
}

const fn make_lt(lhs: Box<SwiftExpr>, rhs: Box<SwiftExpr>) -> SwiftExpr {
    SwiftExpr::Lt { lhs, rhs }
}

/// Warning produced during spec expression validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecWarning {
    /// The warning message.
    pub message: String,
    /// The problematic expression or name.
    pub context: String,
}

/// Validate a parsed spec expression and return any warnings.
///
/// This detects potential issues like:
/// - Undefined variables (`ParamRef` with index -1)
/// - Malformed expressions (names containing spaces or unparsed operators)
///
/// # Arguments
/// * `expr` - The parsed expression to validate
/// * `spec_kind` - The kind of spec ("requires", "ensures", "invariant") for error messages
/// * `original_condition` - The original condition string for context
///
/// # Returns
/// A vector of warnings (empty if no issues found)
#[must_use]
pub fn validate_spec_expression(
    expr: &SwiftExpr,
    spec_kind: &str,
    original_condition: &str,
) -> Vec<SpecWarning> {
    let mut warnings = Vec::new();
    validate_expr_recursive(expr, spec_kind, original_condition, &mut warnings);
    warnings
}

fn validate_expr_recursive(
    expr: &SwiftExpr,
    spec_kind: &str,
    original_condition: &str,
    warnings: &mut Vec<SpecWarning>,
) {
    match expr {
        SwiftExpr::ParamRef { name, index } => {
            // Check for unbound variables (index -1) that aren't special names
            if *index == -1 && !is_special_name(name) {
                // Check if name is empty (malformed expression like "x >> 0")
                if name.is_empty() {
                    warnings.push(SpecWarning {
                        message: format!(
                            "@_{spec_kind} expression could not be fully parsed (may contain unsupported operators)"
                        ),
                        context: original_condition.to_string(),
                    });
                } else if name.contains(' ')
                    || name.contains(">>")
                    || name.contains("<<")
                    || name.contains("=>")
                    || name.contains("::")
                {
                    // Check if name looks like malformed/unparsed expression
                    warnings.push(SpecWarning {
                        message: format!(
                            "@_{spec_kind} expression may be malformed: `{name}` looks like unparsed syntax"
                        ),
                        context: original_condition.to_string(),
                    });
                } else {
                    // Likely an undefined variable
                    warnings.push(SpecWarning {
                        message: format!("@_{spec_kind} references undefined variable `{name}`"),
                        context: original_condition.to_string(),
                    });
                }
            }
        }

        // Recursively check composite expressions
        SwiftExpr::And { lhs, rhs }
        | SwiftExpr::Or { lhs, rhs }
        | SwiftExpr::Eq { lhs, rhs }
        | SwiftExpr::Ne { lhs, rhs }
        | SwiftExpr::Lt { lhs, rhs }
        | SwiftExpr::Le { lhs, rhs }
        | SwiftExpr::Gt { lhs, rhs }
        | SwiftExpr::Ge { lhs, rhs }
        | SwiftExpr::Add { lhs, rhs }
        | SwiftExpr::Sub { lhs, rhs }
        | SwiftExpr::Mul { lhs, rhs }
        | SwiftExpr::Div { lhs, rhs }
        | SwiftExpr::Mod { lhs, rhs } => {
            validate_expr_recursive(lhs, spec_kind, original_condition, warnings);
            validate_expr_recursive(rhs, spec_kind, original_condition, warnings);
        }

        SwiftExpr::Not { operand }
        | SwiftExpr::Neg { operand }
        | SwiftExpr::Old { expr: operand } => {
            validate_expr_recursive(operand, spec_kind, original_condition, warnings);
        }

        SwiftExpr::Field { base, .. } => {
            validate_expr_recursive(base, spec_kind, original_condition, warnings);
        }

        SwiftExpr::Index { base, index } => {
            validate_expr_recursive(base, spec_kind, original_condition, warnings);
            validate_expr_recursive(index, spec_kind, original_condition, warnings);
        }

        SwiftExpr::Call { args, .. } => {
            for arg in args {
                validate_expr_recursive(arg, spec_kind, original_condition, warnings);
            }
        }

        SwiftExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            validate_expr_recursive(cond, spec_kind, original_condition, warnings);
            validate_expr_recursive(then_expr, spec_kind, original_condition, warnings);
            validate_expr_recursive(else_expr, spec_kind, original_condition, warnings);
        }

        SwiftExpr::Forall { body, .. } | SwiftExpr::Exists { body, .. } => {
            validate_expr_recursive(body, spec_kind, original_condition, warnings);
        }

        // Literals and other leaf nodes - no validation needed
        SwiftExpr::IntLit { .. }
        | SwiftExpr::BoolLit { .. }
        | SwiftExpr::StringLit { .. }
        | SwiftExpr::NilLit
        | SwiftExpr::TypeLit { .. }
        | SwiftExpr::ResultRef => {}
    }
}

/// Check if a name is a special/reserved name that's valid without being a parameter.
fn is_special_name(name: &str) -> bool {
    matches!(
        name,
        "result"
            | "self"
            | "Self"
            | "true"
            | "false"
            | "nil"
            | "Int"
            | "Int8"
            | "Int16"
            | "Int32"
            | "Int64"
            | "UInt"
            | "UInt8"
            | "UInt16"
            | "UInt32"
            | "UInt64"
            | "Bool"
            | "String"
            | "Double"
            | "Float"
            | "Array"
            | "Dictionary"
            | "Set"
            | "Optional"
            | "min"
            | "max"
            | "count"
            | "isEmpty"
            | "first"
            | "last"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_params() -> HashMap<String, usize> {
        [
            ("x".to_string(), 0),
            ("y".to_string(), 1),
            ("count".to_string(), 2),
        ]
        .into_iter()
        .collect()
    }

    #[test]
    fn test_parse_bool_literals() {
        assert!(matches!(
            parse_condition_simple("true"),
            SwiftExpr::BoolLit { value: true }
        ));
        assert!(matches!(
            parse_condition_simple("false"),
            SwiftExpr::BoolLit { value: false }
        ));
    }

    #[test]
    fn test_parse_int_literals() {
        assert!(matches!(
            parse_condition_simple("42"),
            SwiftExpr::IntLit { value: 42 }
        ));
        assert!(matches!(
            parse_condition_simple("0"),
            SwiftExpr::IntLit { value: 0 }
        ));
        assert!(matches!(
            parse_condition_simple("-5"),
            SwiftExpr::IntLit { value: -5 }
        ));
    }

    #[test]
    fn test_parse_result_ref() {
        assert!(matches!(
            parse_condition_simple("result"),
            SwiftExpr::ResultRef
        ));
    }

    #[test]
    fn test_parse_nil_lit() {
        assert!(matches!(parse_condition_simple("nil"), SwiftExpr::NilLit));
    }

    #[test]
    fn test_parse_param_ref_with_index() {
        let params = sample_params();
        match parse_condition("x", &params) {
            SwiftExpr::ParamRef { name, index } => {
                assert_eq!(name, "x");
                assert_eq!(index, 0);
            }
            _ => panic!("Expected ParamRef"),
        }
    }

    #[test]
    fn test_parse_param_ref_unknown() {
        match parse_condition_simple("unknown_param") {
            SwiftExpr::ParamRef { name, index } => {
                assert_eq!(name, "unknown_param");
                assert_eq!(index, -1);
            }
            _ => panic!("Expected ParamRef"),
        }
    }

    #[test]
    fn test_parse_comparison_gt() {
        let params = sample_params();
        match parse_condition("x > 0", &params) {
            SwiftExpr::Gt { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, index: 0 } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: 0 }));
            }
            _ => panic!("Expected Gt"),
        }
    }

    #[test]
    fn test_parse_comparison_ge() {
        match parse_condition_simple("result >= x") {
            SwiftExpr::Ge { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ResultRef));
                assert!(matches!(*rhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
            }
            _ => panic!("Expected Ge"),
        }
    }

    #[test]
    fn test_parse_comparison_eq() {
        match parse_condition_simple("x == y") {
            SwiftExpr::Eq { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::ParamRef { ref name, .. } if name == "y"));
            }
            _ => panic!("Expected Eq"),
        }
    }

    #[test]
    fn test_parse_comparison_ne() {
        match parse_condition_simple("x != 0") {
            SwiftExpr::Ne { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: 0 }));
            }
            _ => panic!("Expected Ne"),
        }
    }

    #[test]
    fn test_parse_logical_and() {
        match parse_condition_simple("x > 0 && y > 0") {
            SwiftExpr::And { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Gt { .. }));
                assert!(matches!(*rhs, SwiftExpr::Gt { .. }));
            }
            _ => panic!("Expected And"),
        }
    }

    #[test]
    fn test_parse_logical_or() {
        match parse_condition_simple("x == 0 || y == 0") {
            SwiftExpr::Or { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Eq { .. }));
                assert!(matches!(*rhs, SwiftExpr::Eq { .. }));
            }
            _ => panic!("Expected Or"),
        }
    }

    #[test]
    fn test_parse_logical_not() {
        match parse_condition_simple("!flag") {
            SwiftExpr::Not { operand } => {
                assert!(matches!(*operand, SwiftExpr::ParamRef { ref name, .. } if name == "flag"));
            }
            _ => panic!("Expected Not"),
        }
    }

    #[test]
    fn test_parse_arithmetic_add() {
        match parse_condition_simple("x + 1") {
            SwiftExpr::Add { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: 1 }));
            }
            _ => panic!("Expected Add"),
        }
    }

    #[test]
    fn test_parse_arithmetic_sub() {
        match parse_condition_simple("x - 1") {
            SwiftExpr::Sub { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: 1 }));
            }
            _ => panic!("Expected Sub"),
        }
    }

    #[test]
    fn test_parse_arithmetic_mul() {
        match parse_condition_simple("x * 2") {
            SwiftExpr::Mul { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: 2 }));
            }
            _ => panic!("Expected Mul"),
        }
    }

    #[test]
    fn test_parse_arithmetic_div() {
        match parse_condition_simple("x / 2") {
            SwiftExpr::Div { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: 2 }));
            }
            _ => panic!("Expected Div"),
        }
    }

    #[test]
    fn test_parse_arithmetic_mod() {
        match parse_condition_simple("x % 2") {
            SwiftExpr::Mod { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: 2 }));
            }
            _ => panic!("Expected Mod"),
        }
    }

    #[test]
    fn test_parse_parentheses() {
        match parse_condition_simple("(x + 1) * 2") {
            SwiftExpr::Mul { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Add { .. }));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: 2 }));
            }
            _ => panic!("Expected Mul with Add inside"),
        }
    }

    #[test]
    fn test_parse_nested_parens() {
        match parse_condition_simple("((x))") {
            SwiftExpr::ParamRef { name, .. } => {
                assert_eq!(name, "x");
            }
            _ => panic!("Expected ParamRef"),
        }
    }

    #[test]
    fn test_parse_field_access() {
        match parse_condition_simple("x.count") {
            SwiftExpr::Field { base, field } => {
                assert!(matches!(*base, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert_eq!(field, "count");
            }
            _ => panic!("Expected Field"),
        }
    }

    #[test]
    fn test_parse_chained_field_access() {
        match parse_condition_simple("self.data.count") {
            SwiftExpr::Field { base, field } => {
                assert_eq!(field, "count");
                assert!(matches!(*base, SwiftExpr::Field { .. }));
            }
            _ => panic!("Expected nested Field"),
        }
    }

    #[test]
    fn test_parse_unicode_field_access() {
        // Unicode field names are valid in Swift
        match parse_condition_simple("商品.価格") {
            SwiftExpr::Field { base, field } => {
                assert!(matches!(*base, SwiftExpr::ParamRef { ref name, .. } if name == "商品"));
                assert_eq!(field, "価格");
            }
            _ => panic!("Expected Field with Unicode names"),
        }

        // Chained Unicode field access
        match parse_condition_simple("注文.商品.価格") {
            SwiftExpr::Field { base, field } => {
                assert_eq!(field, "価格");
                match *base {
                    SwiftExpr::Field {
                        ref base,
                        ref field,
                    } => {
                        assert!(
                            matches!(**base, SwiftExpr::ParamRef { ref name, .. } if name == "注文")
                        );
                        assert_eq!(field, "商品");
                    }
                    _ => panic!("Expected nested Field"),
                }
            }
            _ => panic!("Expected nested Field"),
        }
    }

    #[test]
    fn test_parse_array_index() {
        match parse_condition_simple("arr[0]") {
            SwiftExpr::Index { base, index } => {
                assert!(matches!(*base, SwiftExpr::ParamRef { ref name, .. } if name == "arr"));
                assert!(matches!(*index, SwiftExpr::IntLit { value: 0 }));
            }
            _ => panic!("Expected Index"),
        }
    }

    #[test]
    fn test_parse_array_index_with_expr() {
        match parse_condition_simple("arr[i + 1]") {
            SwiftExpr::Index { base, index } => {
                assert!(matches!(*base, SwiftExpr::ParamRef { ref name, .. } if name == "arr"));
                assert!(matches!(*index, SwiftExpr::Add { .. }));
            }
            _ => panic!("Expected Index with Add"),
        }
    }

    #[test]
    fn test_parse_function_call() {
        match parse_condition_simple("abs(x)") {
            SwiftExpr::Call { func, args } => {
                assert_eq!(func, "abs");
                assert_eq!(args.len(), 1);
                assert!(matches!(&args[0], SwiftExpr::ParamRef { name, .. } if name == "x"));
            }
            _ => panic!("Expected Call"),
        }
    }

    #[test]
    fn test_parse_function_call_multi_args() {
        match parse_condition_simple("max(x, y)") {
            SwiftExpr::Call { func, args } => {
                assert_eq!(func, "max");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected Call with 2 args"),
        }
    }

    #[test]
    fn test_parse_old_expr() {
        match parse_condition_simple("old(x)") {
            SwiftExpr::Old { expr } => {
                assert!(matches!(*expr, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
            }
            _ => panic!("Expected Old"),
        }
    }

    #[test]
    fn test_parse_complex_postcondition() {
        // result >= old(x) && result <= old(x) + 10
        match parse_condition_simple("result >= old(x) && result <= old(x) + 10") {
            SwiftExpr::And { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Ge { .. }));
                assert!(matches!(*rhs, SwiftExpr::Le { .. }));
            }
            _ => panic!("Expected And"),
        }
    }

    #[test]
    fn test_parse_negative_comparison() {
        // x > -1 should parse correctly
        match parse_condition_simple("x > -1") {
            SwiftExpr::Gt { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: -1 }));
            }
            _ => panic!("Expected Gt with negative literal"),
        }
    }

    #[test]
    fn test_parse_operator_precedence() {
        // x + y * z should be x + (y * z)
        match parse_condition_simple("x + y * z") {
            SwiftExpr::Add { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::Mul { .. }));
            }
            _ => panic!("Expected Add with Mul rhs"),
        }
    }

    #[test]
    fn test_parse_comparison_vs_arithmetic_precedence() {
        // x + 1 > y should be (x + 1) > y
        match parse_condition_simple("x + 1 > y") {
            SwiftExpr::Gt { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Add { .. }));
                assert!(matches!(*rhs, SwiftExpr::ParamRef { ref name, .. } if name == "y"));
            }
            _ => panic!("Expected Gt with Add lhs"),
        }
    }

    #[test]
    fn test_parse_whitespace_handling() {
        // Various whitespace should be handled
        let expr1 = parse_condition_simple("x>0");
        let expr2 = parse_condition_simple("x > 0");
        let expr3 = parse_condition_simple("  x  >  0  ");

        assert!(matches!(expr1, SwiftExpr::Gt { .. }));
        assert!(matches!(expr2, SwiftExpr::Gt { .. }));
        assert!(matches!(expr3, SwiftExpr::Gt { .. }));
    }

    // Edge case tests added in iteration #150

    #[test]
    fn test_parse_empty_string() {
        // Empty string becomes a ParamRef with empty name
        match parse_condition_simple("") {
            SwiftExpr::ParamRef { name, index } => {
                assert_eq!(name, "");
                assert_eq!(index, -1);
            }
            _ => panic!("Expected ParamRef for empty string"),
        }
    }

    #[test]
    fn test_parse_whitespace_only() {
        // Whitespace-only string becomes a ParamRef with empty name after trim
        match parse_condition_simple("   ") {
            SwiftExpr::ParamRef { name, index } => {
                assert_eq!(name, "");
                assert_eq!(index, -1);
            }
            _ => panic!("Expected ParamRef for whitespace-only"),
        }
    }

    #[test]
    fn test_parse_double_negation() {
        // !!x should parse as Not(Not(ParamRef))
        match parse_condition_simple("!!x") {
            SwiftExpr::Not { operand } => match *operand {
                SwiftExpr::Not { operand: inner } => {
                    assert!(matches!(*inner, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                }
                _ => panic!("Expected inner Not"),
            },
            _ => panic!("Expected outer Not"),
        }
    }

    #[test]
    fn test_parse_logical_precedence_and_binds_tighter() {
        // a || b && c should be a || (b && c) - AND binds tighter than OR
        match parse_condition_simple("a || b && c") {
            SwiftExpr::Or { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "a"));
                assert!(matches!(*rhs, SwiftExpr::And { .. }));
            }
            _ => panic!("Expected Or with And on right"),
        }
    }

    #[test]
    fn test_parse_logical_right_associative() {
        // a && b && c parses as a && (b && c) - right associative
        // This is standard for recursive descent parsers and semantically equivalent
        match parse_condition_simple("a && b && c") {
            SwiftExpr::And { lhs, rhs } => {
                // Left should be just 'a', right should be 'b && c'
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "a"));
                assert!(matches!(*rhs, SwiftExpr::And { .. }));
            }
            _ => panic!("Expected And with And on right"),
        }
    }

    #[test]
    fn test_parse_comparison_with_negative_literal() {
        // x > -5 should parse correctly with negative literal
        match parse_condition_simple("x > -5") {
            SwiftExpr::Gt { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                // The parser may treat -5 as Sub(0, 5) or IntLit(-5)
                match *rhs {
                    SwiftExpr::IntLit { value } => assert_eq!(value, -5),
                    SwiftExpr::Sub { .. } => { /* also acceptable */ }
                    _ => panic!("Expected negative literal or subtraction"),
                }
            }
            _ => panic!("Expected Gt"),
        }
    }

    #[test]
    fn test_parse_negated_comparison() {
        // !(x > 0) should parse as Not(Gt(...))
        match parse_condition_simple("!(x > 0)") {
            SwiftExpr::Not { operand } => {
                assert!(matches!(*operand, SwiftExpr::Gt { .. }));
            }
            _ => panic!("Expected Not"),
        }
    }

    #[test]
    fn test_parse_complex_nested_expression() {
        // (a + b) * (c - d) should parse with correct structure
        match parse_condition_simple("(a + b) * (c - d)") {
            SwiftExpr::Mul { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Add { .. }));
                assert!(matches!(*rhs, SwiftExpr::Sub { .. }));
            }
            _ => panic!("Expected Mul"),
        }
    }

    #[test]
    fn test_parse_not_with_and() {
        // !a && b should parse as (!a) && b, not !(a && b)
        match parse_condition_simple("!a && b") {
            SwiftExpr::And { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Not { .. }));
                assert!(matches!(*rhs, SwiftExpr::ParamRef { ref name, .. } if name == "b"));
            }
            _ => panic!("Expected And with Not on left"),
        }
    }

    #[test]
    fn test_parse_empty_function_call() {
        // func() should parse as a call with no arguments
        match parse_condition_simple("isEmpty()") {
            SwiftExpr::Call { func, args } => {
                assert_eq!(func, "isEmpty");
                assert!(args.is_empty());
            }
            _ => panic!("Expected Call"),
        }
    }

    // ========== Unit tests for helper functions ==========

    #[test]
    fn test_is_wrapped_in_parens_simple() {
        assert!(super::is_wrapped_in_parens("(a)"));
        assert!(super::is_wrapped_in_parens("(a + b)"));
        assert!(super::is_wrapped_in_parens("((a))"));
    }

    #[test]
    fn test_is_wrapped_in_parens_false_cases() {
        assert!(!super::is_wrapped_in_parens("a"));
        assert!(!super::is_wrapped_in_parens("a + b"));
        assert!(!super::is_wrapped_in_parens("(a) + (b)"));
        assert!(!super::is_wrapped_in_parens("(a)(b)"));
    }

    #[test]
    fn test_is_wrapped_in_parens_nested() {
        assert!(super::is_wrapped_in_parens("((a + b) * c)"));
        assert!(super::is_wrapped_in_parens("(func(x, y))"));
        assert!(!super::is_wrapped_in_parens("func(x, y)"));
    }

    #[test]
    fn test_is_wrapped_in_parens_whitespace() {
        assert!(super::is_wrapped_in_parens("  (a)  "));
        assert!(super::is_wrapped_in_parens("(  a  )"));
    }

    #[test]
    fn test_is_wrapped_in_parens_empty() {
        assert!(super::is_wrapped_in_parens("()"));
        assert!(!super::is_wrapped_in_parens(""));
    }

    #[test]
    fn test_find_operator_outside_parens_simple() {
        assert_eq!(super::find_operator_outside_parens("a == b", "=="), Some(2));
        assert_eq!(super::find_operator_outside_parens("a != b", "!="), Some(2));
        assert_eq!(super::find_operator_outside_parens("a && b", "&&"), Some(2));
        assert_eq!(super::find_operator_outside_parens("a || b", "||"), Some(2));
    }

    #[test]
    fn test_find_operator_outside_parens_nested() {
        // Operator inside parens should not be found
        assert_eq!(
            super::find_operator_outside_parens("(a == b) && c", "=="),
            None
        );
        // Operator outside parens should be found
        assert_eq!(
            super::find_operator_outside_parens("(a == b) && c", "&&"),
            Some(9)
        );
    }

    #[test]
    fn test_find_operator_outside_parens_brackets() {
        // Operator inside brackets should not be found
        assert_eq!(
            super::find_operator_outside_parens("arr[i == j]", "=="),
            None
        );
    }

    #[test]
    fn test_find_operator_outside_parens_single_char_disambiguation() {
        // < should not match <= (checks next char is = or <)
        assert_eq!(super::find_operator_outside_parens("a <= b", "<"), None);
        // > should not match >= (checks next char is = or >)
        assert_eq!(super::find_operator_outside_parens("a >= b", ">"), None);
        // First = of == is skipped (next char is =), but second = is found
        // This is expected: function prevents matching < of <=, but doesn't
        // prevent matching the second char of a multi-char operator
        assert_eq!(super::find_operator_outside_parens("a == b", "="), Some(3));
        // ! before = in != is skipped (next char is =)
        assert_eq!(super::find_operator_outside_parens("a != b", "!"), None);
    }

    #[test]
    fn test_find_operator_outside_parens_compound_operators() {
        // Multi-char operators work correctly
        assert_eq!(super::find_operator_outside_parens("a <= b", "<="), Some(2));
        assert_eq!(super::find_operator_outside_parens("a >= b", ">="), Some(2));
        // Actual < should be found when not followed by = or <
        assert_eq!(super::find_operator_outside_parens("a < b", "<"), Some(2));
        assert_eq!(super::find_operator_outside_parens("a > b", ">"), Some(2));
    }

    #[test]
    fn test_find_operator_outside_parens_not_found() {
        assert_eq!(super::find_operator_outside_parens("a + b", "=="), None);
        assert_eq!(super::find_operator_outside_parens("", "&&"), None);
    }

    #[test]
    fn test_find_additive_operator_outside_parens_plus() {
        assert_eq!(
            super::find_additive_operator_outside_parens("a + b"),
            Some(2)
        );
        assert_eq!(
            super::find_additive_operator_outside_parens("x + y + z"),
            Some(2)
        );
    }

    #[test]
    fn test_find_additive_operator_outside_parens_minus() {
        assert_eq!(
            super::find_additive_operator_outside_parens("a - b"),
            Some(2)
        );
    }

    #[test]
    fn test_find_additive_operator_outside_parens_unary_minus() {
        // Unary minus at start should not be found
        assert_eq!(super::find_additive_operator_outside_parens("-a"), None);
        // Unary minus after operator should not be found as binary
        assert_eq!(super::find_additive_operator_outside_parens("a * -b"), None);
    }

    #[test]
    fn test_find_additive_operator_outside_parens_nested() {
        // Inside parens should not be found
        assert_eq!(
            super::find_additive_operator_outside_parens("(a + b) * c"),
            None
        );
        // Outside parens should be found
        assert_eq!(
            super::find_additive_operator_outside_parens("(a * b) + c"),
            Some(8)
        );
    }

    #[test]
    fn test_find_last_dot_outside_parens_simple() {
        assert_eq!(super::find_last_dot_outside_parens("a.b"), Some(1));
        assert_eq!(super::find_last_dot_outside_parens("a.b.c"), Some(3));
    }

    #[test]
    fn test_find_last_dot_outside_parens_nested() {
        // Dot inside parens should not be the result
        assert_eq!(super::find_last_dot_outside_parens("(a.b)"), None);
        // Should find the last dot outside parens
        assert_eq!(super::find_last_dot_outside_parens("(a.b).c"), Some(5));
    }

    #[test]
    fn test_find_last_dot_outside_parens_brackets() {
        // Dot inside brackets should not be found
        assert_eq!(super::find_last_dot_outside_parens("arr[i.j]"), None);
        assert_eq!(super::find_last_dot_outside_parens("arr[i.j].x"), Some(8));
    }

    #[test]
    fn test_find_last_dot_outside_parens_none() {
        assert_eq!(super::find_last_dot_outside_parens("abc"), None);
        assert_eq!(super::find_last_dot_outside_parens(""), None);
    }

    #[test]
    fn test_is_valid_field_ident_valid() {
        assert!(super::is_valid_field_ident("x"));
        assert!(super::is_valid_field_ident("count"));
        assert!(super::is_valid_field_ident("_private"));
        assert!(super::is_valid_field_ident("value123"));
        assert!(super::is_valid_field_ident("snake_case"));
    }

    #[test]
    fn test_is_valid_field_ident_invalid() {
        assert!(!super::is_valid_field_ident(""));
        assert!(!super::is_valid_field_ident("123"));
        assert!(!super::is_valid_field_ident("123abc"));
        assert!(!super::is_valid_field_ident("a-b"));
        assert!(!super::is_valid_field_ident("a b"));
    }

    #[test]
    fn test_is_valid_field_ident_whitespace() {
        // Whitespace should be trimmed
        assert!(super::is_valid_field_ident("  x  "));
        assert!(super::is_valid_field_ident("\tcount\t"));
    }

    #[test]
    fn test_is_valid_field_ident_unicode() {
        // Swift supports Unicode identifiers
        assert!(super::is_valid_field_ident("価格")); // Japanese "price"
        assert!(super::is_valid_field_ident("北京")); // Chinese "Beijing"
        assert!(super::is_valid_field_ident("カウント")); // Japanese katakana "count"
        assert!(super::is_valid_field_ident("α")); // Greek alpha
        assert!(super::is_valid_field_ident("β1")); // Greek with number
        assert!(super::is_valid_field_ident("_日本語")); // Underscore + Japanese
        // Numbers at start still invalid (even Unicode numbers)
        assert!(!super::is_valid_field_ident("1あ"));
    }

    #[test]
    fn test_find_matching_open_bracket_simple() {
        assert_eq!(super::find_matching_open_bracket("arr[0]"), Some(3));
        assert_eq!(super::find_matching_open_bracket("x[i]"), Some(1));
    }

    #[test]
    fn test_find_matching_open_bracket_nested() {
        assert_eq!(super::find_matching_open_bracket("arr[i[j]]"), Some(3));
        assert_eq!(super::find_matching_open_bracket("a[b[c[d]]]"), Some(1));
    }

    #[test]
    fn test_find_matching_open_bracket_none() {
        assert_eq!(super::find_matching_open_bracket("abc"), None);
        assert_eq!(super::find_matching_open_bracket(""), None);
    }

    #[test]
    fn test_find_matching_open_paren_for_call_simple() {
        assert_eq!(super::find_matching_open_paren_for_call("func()"), Some(4));
        assert_eq!(super::find_matching_open_paren_for_call("f(x)"), Some(1));
    }

    #[test]
    fn test_find_matching_open_paren_for_call_nested() {
        assert_eq!(
            super::find_matching_open_paren_for_call("func(g(x))"),
            Some(4)
        );
        assert_eq!(
            super::find_matching_open_paren_for_call("a(b(c(d)))"),
            Some(1)
        );
    }

    #[test]
    fn test_find_matching_open_paren_for_call_none() {
        assert_eq!(super::find_matching_open_paren_for_call("abc"), None);
        assert_eq!(super::find_matching_open_paren_for_call(""), None);
    }

    #[test]
    fn test_split_args_single() {
        assert_eq!(super::split_args("x"), vec!["x"]);
        assert_eq!(super::split_args("  x  "), vec!["x"]);
    }

    #[test]
    fn test_split_args_multiple() {
        assert_eq!(super::split_args("a, b, c"), vec!["a", "b", "c"]);
        assert_eq!(super::split_args("x,y,z"), vec!["x", "y", "z"]);
    }

    #[test]
    fn test_split_args_nested_parens() {
        // Commas inside parens should not split
        assert_eq!(super::split_args("f(a, b), c"), vec!["f(a, b)", "c"]);
        assert_eq!(super::split_args("x, g(y, z)"), vec!["x", "g(y, z)"]);
    }

    #[test]
    fn test_split_args_nested_brackets() {
        // Commas inside brackets should not split
        assert_eq!(super::split_args("arr[0, 1], b"), vec!["arr[0, 1]", "b"]);
    }

    #[test]
    fn test_split_args_empty() {
        assert_eq!(super::split_args(""), Vec::<&str>::new());
        assert_eq!(super::split_args("   "), Vec::<&str>::new());
    }

    #[test]
    fn test_split_args_complex() {
        assert_eq!(
            super::split_args("a + b, f(x, y), arr[i, j]"),
            vec!["a + b", "f(x, y)", "arr[i, j]"]
        );
    }

    // ========== Additional tests for complete coverage ==========

    // Less-than comparison operators
    #[test]
    fn test_parse_comparison_lt() {
        match parse_condition_simple("x < 10") {
            SwiftExpr::Lt { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: 10 }));
            }
            _ => panic!("Expected Lt"),
        }
    }

    #[test]
    fn test_parse_comparison_le() {
        match parse_condition_simple("count <= 100") {
            SwiftExpr::Le { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "count"));
                assert!(matches!(*rhs, SwiftExpr::IntLit { value: 100 }));
            }
            _ => panic!("Expected Le"),
        }
    }

    #[test]
    fn test_parse_comparison_chain_lt_lt() {
        // a < b < c parses as (a < b) < c due to left-to-right scan
        // The parser finds first < outside parens
        match parse_condition_simple("a < b < c") {
            SwiftExpr::Lt { lhs, rhs } => {
                // First Lt found: lhs = "a", rhs = "b < c"
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "a"));
                assert!(matches!(*rhs, SwiftExpr::Lt { .. }));
            }
            _ => panic!("Expected Lt"),
        }
    }

    // Unary negation for expressions (not just literals)
    #[test]
    fn test_parse_unary_neg_param() {
        match parse_condition_simple("-x") {
            SwiftExpr::Neg { operand } => {
                assert!(matches!(*operand, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
            }
            _ => panic!("Expected Neg"),
        }
    }

    #[test]
    fn test_parse_unary_neg_expression() {
        // -(a + b) should be Neg(Add(...))
        match parse_condition_simple("-(a + b)") {
            SwiftExpr::Neg { operand } => {
                assert!(matches!(*operand, SwiftExpr::Add { .. }));
            }
            _ => panic!("Expected Neg"),
        }
    }

    #[test]
    fn test_parse_unary_neg_field() {
        match parse_condition_simple("-x.count") {
            SwiftExpr::Neg { operand } => {
                assert!(matches!(*operand, SwiftExpr::Field { .. }));
            }
            _ => panic!("Expected Neg with Field"),
        }
    }

    // Complex old() expressions
    #[test]
    fn test_parse_old_field_access() {
        match parse_condition_simple("old(x.count)") {
            SwiftExpr::Old { expr } => {
                assert!(matches!(*expr, SwiftExpr::Field { .. }));
            }
            _ => panic!("Expected Old with Field"),
        }
    }

    #[test]
    fn test_parse_old_index_access() {
        match parse_condition_simple("old(arr[0])") {
            SwiftExpr::Old { expr } => {
                assert!(matches!(*expr, SwiftExpr::Index { .. }));
            }
            _ => panic!("Expected Old with Index"),
        }
    }

    #[test]
    fn test_parse_old_arithmetic() {
        match parse_condition_simple("old(x + 1)") {
            SwiftExpr::Old { expr } => {
                assert!(matches!(*expr, SwiftExpr::Add { .. }));
            }
            _ => panic!("Expected Old with Add"),
        }
    }

    #[test]
    fn test_parse_old_comparison() {
        // result > old(x) - common postcondition pattern
        match parse_condition_simple("result > old(x)") {
            SwiftExpr::Gt { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ResultRef));
                assert!(matches!(*rhs, SwiftExpr::Old { .. }));
            }
            _ => panic!("Expected Gt with Old"),
        }
    }

    // Nested function calls
    #[test]
    fn test_parse_nested_function_calls() {
        match parse_condition_simple("f(g(x))") {
            SwiftExpr::Call { func, args } => {
                assert_eq!(func, "f");
                assert_eq!(args.len(), 1);
                match &args[0] {
                    SwiftExpr::Call {
                        func: inner_func,
                        args: inner_args,
                    } => {
                        assert_eq!(inner_func, "g");
                        assert_eq!(inner_args.len(), 1);
                    }
                    _ => panic!("Expected inner Call"),
                }
            }
            _ => panic!("Expected outer Call"),
        }
    }

    #[test]
    fn test_parse_deeply_nested_function_calls() {
        match parse_condition_simple("a(b(c(d(x))))") {
            SwiftExpr::Call { func, args } => {
                assert_eq!(func, "a");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("Expected Call"),
        }
    }

    #[test]
    fn test_parse_function_call_with_complex_args() {
        match parse_condition_simple("max(a + b, c * d)") {
            SwiftExpr::Call { func, args } => {
                assert_eq!(func, "max");
                assert_eq!(args.len(), 2);
                assert!(matches!(&args[0], SwiftExpr::Add { .. }));
                assert!(matches!(&args[1], SwiftExpr::Mul { .. }));
            }
            _ => panic!("Expected Call"),
        }
    }

    // Field/Index combinations
    #[test]
    fn test_parse_field_on_index() {
        // arr[0].field
        match parse_condition_simple("arr[0].field") {
            SwiftExpr::Field { base, field } => {
                assert_eq!(field, "field");
                assert!(matches!(*base, SwiftExpr::Index { .. }));
            }
            _ => panic!("Expected Field on Index"),
        }
    }

    #[test]
    fn test_parse_index_on_field() {
        // x.arr[0]
        match parse_condition_simple("x.arr[0]") {
            SwiftExpr::Index { base, index } => {
                assert!(matches!(*base, SwiftExpr::Field { .. }));
                assert!(matches!(*index, SwiftExpr::IntLit { value: 0 }));
            }
            _ => panic!("Expected Index on Field"),
        }
    }

    #[test]
    fn test_parse_nested_index() {
        // matrix[i][j]
        match parse_condition_simple("matrix[i][j]") {
            SwiftExpr::Index { base, index } => {
                assert!(matches!(*index, SwiftExpr::ParamRef { ref name, .. } if name == "j"));
                assert!(matches!(*base, SwiftExpr::Index { .. }));
            }
            _ => panic!("Expected nested Index"),
        }
    }

    #[test]
    fn test_parse_deep_field_chain() {
        // a.b.c.d.e
        match parse_condition_simple("a.b.c.d.e") {
            SwiftExpr::Field { base, field } => {
                assert_eq!(field, "e");
                // Check it's a chain of Field expressions
                match *base {
                    SwiftExpr::Field { field: ref f, .. } => assert_eq!(f, "d"),
                    _ => panic!("Expected Field chain"),
                }
            }
            _ => panic!("Expected Field"),
        }
    }

    // Multiple parameters with parse_condition
    #[test]
    fn test_parse_multiple_params_lookup() {
        let params = sample_params();
        match parse_condition("x + y + count", &params) {
            SwiftExpr::Add { lhs, rhs } => {
                match *lhs {
                    SwiftExpr::ParamRef { ref name, index } => {
                        assert_eq!(name, "x");
                        assert_eq!(index, 0);
                    }
                    _ => panic!("Expected ParamRef x"),
                }
                match *rhs {
                    SwiftExpr::Add { ref lhs, ref rhs } => {
                        match **lhs {
                            SwiftExpr::ParamRef { ref name, index } => {
                                assert_eq!(name, "y");
                                assert_eq!(index, 1);
                            }
                            _ => panic!("Expected ParamRef y"),
                        }
                        match **rhs {
                            SwiftExpr::ParamRef { ref name, index } => {
                                assert_eq!(name, "count");
                                assert_eq!(index, 2);
                            }
                            _ => panic!("Expected ParamRef count"),
                        }
                    }
                    _ => panic!("Expected inner Add"),
                }
            }
            _ => panic!("Expected Add"),
        }
    }

    #[test]
    fn test_parse_condition_empty_params() {
        let params: HashMap<String, usize> = HashMap::new();
        match parse_condition("x", &params) {
            SwiftExpr::ParamRef { name, index } => {
                assert_eq!(name, "x");
                assert_eq!(index, -1);
            }
            _ => panic!("Expected ParamRef"),
        }
    }

    // Large integers
    #[test]
    fn test_parse_large_positive_int() {
        match parse_condition_simple("9223372036854775807") {
            SwiftExpr::IntLit { value } => {
                assert_eq!(value, i64::MAX);
            }
            _ => panic!("Expected IntLit"),
        }
    }

    #[test]
    fn test_parse_large_negative_int() {
        match parse_condition_simple("-9223372036854775808") {
            SwiftExpr::IntLit { value } => {
                assert_eq!(value, i64::MIN);
            }
            _ => panic!("Expected IntLit"),
        }
    }

    #[test]
    fn test_parse_int_overflow_becomes_param() {
        // Number larger than i64::MAX can't parse as int, becomes ParamRef
        match parse_condition_simple("99999999999999999999") {
            SwiftExpr::ParamRef { name, index } => {
                assert_eq!(name, "99999999999999999999");
                assert_eq!(index, -1);
            }
            _ => panic!("Expected ParamRef for overflow"),
        }
    }

    // Subtraction chains
    #[test]
    fn test_parse_subtraction_chain() {
        // a - b - c should parse as a - (b - c) due to right-to-left recursion
        match parse_condition_simple("a - b - c") {
            SwiftExpr::Sub { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "a"));
                assert!(matches!(*rhs, SwiftExpr::Sub { .. }));
            }
            _ => panic!("Expected Sub"),
        }
    }

    #[test]
    fn test_parse_mixed_add_sub() {
        // a + b - c
        match parse_condition_simple("a + b - c") {
            SwiftExpr::Add { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "a"));
                match *rhs {
                    SwiftExpr::Sub { .. } => {}
                    _ => panic!("Expected Sub on right"),
                }
            }
            _ => panic!("Expected Add"),
        }
    }

    // Test Unicode variable names in arithmetic (validates byte offset fix)
    #[test]
    fn test_parse_arithmetic_unicode_variable_names() {
        // Unicode variable names: "価格" (kakaku, "price") + "税" (zei, "tax")
        // This tests that the arithmetic operator finding uses byte offsets correctly
        // since multi-byte Unicode chars would cause issues with char offset
        match parse_condition_simple("価格 + 税") {
            SwiftExpr::Add { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "価格"));
                assert!(matches!(*rhs, SwiftExpr::ParamRef { ref name, .. } if name == "税"));
            }
            _ => panic!("Expected Add"),
        }

        // Subtraction with Unicode names
        match parse_condition_simple("総額 - 割引") {
            SwiftExpr::Sub { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "総額"));
                assert!(matches!(*rhs, SwiftExpr::ParamRef { ref name, .. } if name == "割引"));
            }
            _ => panic!("Expected Sub"),
        }
    }

    // Mixed operations with different precedences
    #[test]
    fn test_parse_sub_mul_precedence() {
        // a - b * c should be a - (b * c)
        match parse_condition_simple("a - b * c") {
            SwiftExpr::Sub { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "a"));
                assert!(matches!(*rhs, SwiftExpr::Mul { .. }));
            }
            _ => panic!("Expected Sub with Mul"),
        }
    }

    #[test]
    fn test_parse_div_mod_chain() {
        // a / b % c - division found first
        match parse_condition_simple("a / b % c") {
            SwiftExpr::Div { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "a"));
                assert!(matches!(*rhs, SwiftExpr::Mod { .. }));
            }
            _ => panic!("Expected Div with Mod"),
        }
    }

    // Deeply nested parentheses
    #[test]
    fn test_parse_deeply_nested_parens() {
        match parse_condition_simple("((((x))))") {
            SwiftExpr::ParamRef { name, .. } => {
                assert_eq!(name, "x");
            }
            _ => panic!("Expected ParamRef"),
        }
    }

    #[test]
    fn test_parse_nested_parens_with_ops() {
        // (((a + b)))
        match parse_condition_simple("(((a + b)))") {
            SwiftExpr::Add { .. } => {}
            _ => panic!("Expected Add"),
        }
    }

    // Complex mixed expressions
    #[test]
    fn test_parse_complex_logical_arithmetic() {
        // (x > 0 && y < 10) || z == 0
        match parse_condition_simple("(x > 0 && y < 10) || z == 0") {
            SwiftExpr::Or { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::And { .. }));
                assert!(matches!(*rhs, SwiftExpr::Eq { .. }));
            }
            _ => panic!("Expected Or"),
        }
    }

    #[test]
    fn test_parse_postcondition_pattern() {
        // Common pattern: result == old(x) + 1
        match parse_condition_simple("result == old(x) + 1") {
            SwiftExpr::Eq { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ResultRef));
                assert!(matches!(*rhs, SwiftExpr::Add { .. }));
            }
            _ => panic!("Expected Eq"),
        }
    }

    #[test]
    fn test_parse_bounds_check_pattern() {
        // Common pattern: 0 <= i && i < arr.count
        match parse_condition_simple("0 <= i && i < arr.count") {
            SwiftExpr::And { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Le { .. }));
                assert!(matches!(*rhs, SwiftExpr::Lt { .. }));
            }
            _ => panic!("Expected And"),
        }
    }

    // Expression constructors direct tests
    #[test]
    fn test_make_ge() {
        let lhs = Box::new(SwiftExpr::IntLit { value: 1 });
        let rhs = Box::new(SwiftExpr::IntLit { value: 2 });
        assert!(matches!(super::make_ge(lhs, rhs), SwiftExpr::Ge { .. }));
    }

    #[test]
    fn test_make_le() {
        let lhs = Box::new(SwiftExpr::IntLit { value: 1 });
        let rhs = Box::new(SwiftExpr::IntLit { value: 2 });
        assert!(matches!(super::make_le(lhs, rhs), SwiftExpr::Le { .. }));
    }

    #[test]
    fn test_make_eq() {
        let lhs = Box::new(SwiftExpr::IntLit { value: 1 });
        let rhs = Box::new(SwiftExpr::IntLit { value: 2 });
        assert!(matches!(super::make_eq(lhs, rhs), SwiftExpr::Eq { .. }));
    }

    #[test]
    fn test_make_ne() {
        let lhs = Box::new(SwiftExpr::IntLit { value: 1 });
        let rhs = Box::new(SwiftExpr::IntLit { value: 2 });
        assert!(matches!(super::make_ne(lhs, rhs), SwiftExpr::Ne { .. }));
    }

    #[test]
    fn test_make_gt() {
        let lhs = Box::new(SwiftExpr::IntLit { value: 1 });
        let rhs = Box::new(SwiftExpr::IntLit { value: 2 });
        assert!(matches!(super::make_gt(lhs, rhs), SwiftExpr::Gt { .. }));
    }

    #[test]
    fn test_make_lt() {
        let lhs = Box::new(SwiftExpr::IntLit { value: 1 });
        let rhs = Box::new(SwiftExpr::IntLit { value: 2 });
        assert!(matches!(super::make_lt(lhs, rhs), SwiftExpr::Lt { .. }));
    }

    // Additional helper function edge cases
    #[test]
    fn test_is_wrapped_in_parens_unbalanced_open() {
        assert!(!super::is_wrapped_in_parens("((a)"));
    }

    #[test]
    fn test_is_wrapped_in_parens_unbalanced_close() {
        assert!(!super::is_wrapped_in_parens("(a))"));
    }

    #[test]
    fn test_is_wrapped_in_parens_only_start() {
        assert!(!super::is_wrapped_in_parens("(abc"));
    }

    #[test]
    fn test_is_wrapped_in_parens_only_end() {
        assert!(!super::is_wrapped_in_parens("abc)"));
    }

    #[test]
    fn test_find_operator_multiple_same_op() {
        // Should find first occurrence
        assert_eq!(
            super::find_operator_outside_parens("a && b && c", "&&"),
            Some(2)
        );
    }

    #[test]
    fn test_find_operator_at_start() {
        // Operator at very start
        assert_eq!(super::find_operator_outside_parens("==b", "=="), Some(0));
    }

    #[test]
    fn test_find_operator_at_end() {
        // Should find operator even at end position
        assert_eq!(super::find_operator_outside_parens("a==", "=="), Some(1));
    }

    #[test]
    fn test_find_additive_after_close_paren() {
        // + after ) is binary
        assert_eq!(
            super::find_additive_operator_outside_parens("(a) + b"),
            Some(4)
        );
    }

    #[test]
    fn test_find_additive_after_close_bracket() {
        // + after ] is binary
        assert_eq!(
            super::find_additive_operator_outside_parens("arr[0] + 1"),
            Some(7)
        );
    }

    #[test]
    fn test_find_additive_after_underscore() {
        // + after identifier with underscore is binary
        assert_eq!(
            super::find_additive_operator_outside_parens("foo_bar + 1"),
            Some(8)
        );
    }

    #[test]
    fn test_find_last_dot_multiple() {
        // Should return last dot
        assert_eq!(super::find_last_dot_outside_parens("a.b.c.d"), Some(5));
    }

    #[test]
    fn test_find_last_dot_with_parens_and_brackets() {
        // Complex expression with multiple dot locations
        assert_eq!(
            super::find_last_dot_outside_parens("(a.b)[c.d].e"),
            Some(10)
        );
    }

    #[test]
    fn test_is_valid_field_ident_all_underscore() {
        assert!(super::is_valid_field_ident("___"));
        assert!(super::is_valid_field_ident("_1_2_3"));
    }

    #[test]
    fn test_is_valid_field_ident_special_chars() {
        assert!(!super::is_valid_field_ident("a.b"));
        assert!(!super::is_valid_field_ident("a[0]"));
        assert!(!super::is_valid_field_ident("a(b)"));
        assert!(!super::is_valid_field_ident("a+b"));
    }

    #[test]
    fn test_find_matching_bracket_unbalanced() {
        // More ] than [
        assert_eq!(super::find_matching_open_bracket("a]]"), None);
    }

    #[test]
    fn test_find_matching_bracket_at_start() {
        assert_eq!(super::find_matching_open_bracket("[x]"), Some(0));
    }

    #[test]
    fn test_find_matching_paren_at_start() {
        assert_eq!(super::find_matching_open_paren_for_call("(x)"), Some(0));
    }

    #[test]
    fn test_split_args_trailing_comma() {
        // Trailing comma results in empty last arg which is filtered
        assert_eq!(super::split_args("a, b, "), vec!["a", "b"]);
    }

    #[test]
    fn test_split_args_leading_comma() {
        // Leading comma results in empty first arg (not filtered)
        assert_eq!(super::split_args(", a, b"), vec!["", "a", "b"]);
    }

    #[test]
    fn test_split_args_consecutive_commas() {
        // Consecutive commas produce empty strings (not filtered)
        assert_eq!(super::split_args("a,, b"), vec!["a", "", "b"]);
    }

    #[test]
    fn test_split_args_deeply_nested() {
        assert_eq!(super::split_args("f(g(h(x))), y"), vec!["f(g(h(x)))", "y"]);
    }

    // Special identifier names
    #[test]
    fn test_parse_self_field() {
        match parse_condition_simple("self.value") {
            SwiftExpr::Field { base, field } => {
                assert!(matches!(*base, SwiftExpr::ParamRef { ref name, .. } if name == "self"));
                assert_eq!(field, "value");
            }
            _ => panic!("Expected Field"),
        }
    }

    #[test]
    fn test_parse_underscore_identifier() {
        match parse_condition_simple("_private") {
            SwiftExpr::ParamRef { name, .. } => {
                assert_eq!(name, "_private");
            }
            _ => panic!("Expected ParamRef"),
        }
    }

    #[test]
    fn test_parse_identifier_with_numbers() {
        match parse_condition_simple("var123") {
            SwiftExpr::ParamRef { name, .. } => {
                assert_eq!(name, "var123");
            }
            _ => panic!("Expected ParamRef"),
        }
    }

    // Function call edge cases
    #[test]
    fn test_parse_function_call_three_args() {
        match parse_condition_simple("clamp(x, min, max)") {
            SwiftExpr::Call { func, args } => {
                assert_eq!(func, "clamp");
                assert_eq!(args.len(), 3);
            }
            _ => panic!("Expected Call"),
        }
    }

    #[test]
    fn test_parse_function_call_nested_parens_in_args() {
        match parse_condition_simple("f((a + b))") {
            SwiftExpr::Call { func, args } => {
                assert_eq!(func, "f");
                assert_eq!(args.len(), 1);
                assert!(matches!(&args[0], SwiftExpr::Add { .. }));
            }
            _ => panic!("Expected Call"),
        }
    }

    // Comparison with expressions on both sides
    #[test]
    fn test_parse_comparison_expressions_both_sides() {
        // (a + 1) >= (b - 1)
        match parse_condition_simple("(a + 1) >= (b - 1)") {
            SwiftExpr::Ge { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Add { .. }));
                assert!(matches!(*rhs, SwiftExpr::Sub { .. }));
            }
            _ => panic!("Expected Ge"),
        }
    }

    // Not with complex expression
    #[test]
    fn test_parse_not_with_or() {
        // !a || b
        match parse_condition_simple("!a || b") {
            SwiftExpr::Or { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Not { .. }));
                assert!(matches!(*rhs, SwiftExpr::ParamRef { ref name, .. } if name == "b"));
            }
            _ => panic!("Expected Or"),
        }
    }

    #[test]
    fn test_parse_not_with_comparison() {
        // !x == y parses as (!x) == y
        match parse_condition_simple("!x == y") {
            SwiftExpr::Eq { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::Not { .. }));
                assert!(matches!(*rhs, SwiftExpr::ParamRef { ref name, .. } if name == "y"));
            }
            _ => panic!("Expected Eq"),
        }
    }

    // Zero literal special cases
    #[test]
    fn test_parse_negative_zero() {
        // -0 is still 0
        match parse_condition_simple("-0") {
            SwiftExpr::IntLit { value } => {
                assert_eq!(value, 0);
            }
            _ => panic!("Expected IntLit"),
        }
    }

    // Whitespace variations
    #[test]
    fn test_parse_tab_whitespace() {
        match parse_condition_simple("x\t>\t0") {
            SwiftExpr::Gt { .. } => {}
            _ => panic!("Expected Gt"),
        }
    }

    #[test]
    fn test_parse_newline_in_expression() {
        // Newlines should be handled as whitespace
        match parse_condition_simple("x\n>\n0") {
            SwiftExpr::Gt { .. } => {}
            _ => panic!("Expected Gt"),
        }
    }

    // Field access on result
    #[test]
    fn test_parse_result_field_access() {
        match parse_condition_simple("result.count") {
            SwiftExpr::Field { base, field } => {
                assert!(matches!(*base, SwiftExpr::ResultRef));
                assert_eq!(field, "count");
            }
            _ => panic!("Expected Field on ResultRef"),
        }
    }

    // Index access on result
    #[test]
    fn test_parse_result_index_access() {
        match parse_condition_simple("result[0]") {
            SwiftExpr::Index { base, index } => {
                assert!(matches!(*base, SwiftExpr::ResultRef));
                assert!(matches!(*index, SwiftExpr::IntLit { value: 0 }));
            }
            _ => panic!("Expected Index on ResultRef"),
        }
    }

    // nil comparisons
    #[test]
    fn test_parse_nil_comparison_eq() {
        match parse_condition_simple("x == nil") {
            SwiftExpr::Eq { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ParamRef { ref name, .. } if name == "x"));
                assert!(matches!(*rhs, SwiftExpr::NilLit));
            }
            _ => panic!("Expected Eq with nil"),
        }
    }

    #[test]
    fn test_parse_nil_comparison_ne() {
        match parse_condition_simple("result != nil") {
            SwiftExpr::Ne { lhs, rhs } => {
                assert!(matches!(*lhs, SwiftExpr::ResultRef));
                assert!(matches!(*rhs, SwiftExpr::NilLit));
            }
            _ => panic!("Expected Ne with nil"),
        }
    }
}
