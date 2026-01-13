//! Proof hint generation (Phase 8.2)
//!
//! This module provides lightweight, deterministic "AI-style" proof hints by
//! pattern-matching on VC IR predicates. The intent is to surface actionable
//! next steps (tactics, built-in lemmas, and configuration knobs) when an
//! automatic backend returns `Unknown` or a proof attempt stalls.
//!
//! The hints here are intentionally heuristic and conservative: they do not
//! attempt to prove anything, only suggest likely next actions.

use crate::{Expr, Predicate, TacticKind};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

/// Kind of proof hint.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofHintKind {
    /// Suggest adding a `#[tactic(...)]` annotation.
    Tactic(TacticKind),
    /// Suggest using a named built-in lemma.
    BuiltinLemma { name: String },
    /// Suggest increasing per-VC timeout (milliseconds).
    TimeoutMs(u64),
    /// Suggest increasing bounded-model-check depth.
    BmcDepth(usize),
}

/// A single proof hint.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ProofHint {
    pub kind: ProofHintKind,
    pub description: String,
    /// Confidence in [0.0, 1.0].
    pub confidence: f64,
}

impl ProofHint {
    pub fn new(kind: ProofHintKind, description: impl Into<String>, confidence: f64) -> Self {
        Self {
            kind,
            description: description.into(),
            confidence: confidence.clamp(0.0, 1.0),
        }
    }
}

#[derive(Debug, Default)]
struct Features {
    vars: BTreeSet<String>,
    uses_add: bool,
    uses_mul: bool,
    uses_div: bool,
    uses_rem: bool,
    uses_abs: bool,
    uses_minmax: bool,
    uses_arrays: bool,
    uses_quantifiers: bool,
    uses_implication: bool,
    uses_disjunction: bool,
    uses_ite: bool,
}

fn collect_predicate_features(pred: &Predicate, features: &mut Features) {
    match pred {
        Predicate::Bool(_) => {}
        Predicate::Expr(e) => collect_expr_features(e, features),
        Predicate::Not(inner) => collect_predicate_features(inner, features),
        Predicate::And(preds) => {
            for p in preds {
                collect_predicate_features(p, features);
            }
        }
        Predicate::Or(preds) => {
            features.uses_disjunction = true;
            for p in preds {
                collect_predicate_features(p, features);
            }
        }
        Predicate::Implies(a, b) => {
            features.uses_implication = true;
            collect_predicate_features(a, features);
            collect_predicate_features(b, features);
        }
        Predicate::Iff(a, b) => {
            collect_predicate_features(a, features);
            collect_predicate_features(b, features);
        }
        Predicate::Forall { vars, body, .. } | Predicate::Exists { vars, body } => {
            features.uses_quantifiers = true;
            for (name, _) in vars {
                features.vars.insert(name.clone());
            }
            collect_predicate_features(body, features);
        }
        Predicate::Let { bindings, body } => {
            for (name, expr) in bindings {
                features.vars.insert(name.clone());
                collect_expr_features(expr, features);
            }
            collect_predicate_features(body, features);
        }
    }
}

fn collect_expr_features(expr: &Expr, features: &mut Features) {
    match expr {
        Expr::Var(name) => {
            features.vars.insert(name.clone());
        }
        Expr::Old(inner) | Expr::Sorted(inner) => collect_expr_features(inner, features),
        Expr::Neg(inner)
        | Expr::Not(inner)
        | Expr::BitNot(inner)
        | Expr::Deref(inner)
        | Expr::AddrOf(inner)
        | Expr::Abs(inner)
        | Expr::ArrayLen(inner)
        | Expr::TensorShape(inner) => {
            if matches!(expr, Expr::Abs(_)) {
                features.uses_abs = true;
            }
            if matches!(expr, Expr::ArrayLen(_)) {
                features.uses_arrays = true;
            }
            collect_expr_features(inner, features);
        }
        Expr::Add(a, b) => {
            features.uses_add = true;
            collect_expr_features(a, features);
            collect_expr_features(b, features);
        }
        Expr::Sub(a, b) => {
            collect_expr_features(a, features);
            collect_expr_features(b, features);
        }
        Expr::Mul(a, b) => {
            features.uses_mul = true;
            collect_expr_features(a, features);
            collect_expr_features(b, features);
        }
        Expr::Div(a, b) => {
            features.uses_div = true;
            collect_expr_features(a, features);
            collect_expr_features(b, features);
        }
        Expr::Rem(a, b) => {
            features.uses_rem = true;
            collect_expr_features(a, features);
            collect_expr_features(b, features);
        }
        Expr::BitAnd(a, b)
        | Expr::BitOr(a, b)
        | Expr::BitXor(a, b)
        | Expr::Shl(a, b)
        | Expr::Shr(a, b)
        | Expr::Eq(a, b)
        | Expr::Ne(a, b)
        | Expr::Lt(a, b)
        | Expr::Le(a, b)
        | Expr::Gt(a, b)
        | Expr::Ge(a, b)
        | Expr::And(a, b)
        | Expr::Or(a, b)
        | Expr::Min(a, b)
        | Expr::Max(a, b)
        | Expr::Permutation(a, b) => {
            if matches!(expr, Expr::Min(_, _) | Expr::Max(_, _)) {
                features.uses_minmax = true;
            }
            if matches!(expr, Expr::Or(_, _)) {
                features.uses_disjunction = true;
            }
            collect_expr_features(a, features);
            collect_expr_features(b, features);
        }
        Expr::Ite { cond, then_, else_ } => {
            features.uses_ite = true;
            collect_expr_features(cond, features);
            collect_expr_features(then_, features);
            collect_expr_features(else_, features);
        }
        Expr::ArrayIndex(array, index) => {
            features.uses_arrays = true;
            collect_expr_features(array, features);
            collect_expr_features(index, features);
        }
        Expr::ArraySlice { array, start, end } => {
            features.uses_arrays = true;
            collect_expr_features(array, features);
            collect_expr_features(start, features);
            collect_expr_features(end, features);
        }
        Expr::TupleField(base, _) | Expr::StructField(base, _) => {
            collect_expr_features(base, features);
        }
        Expr::Apply { args, .. } => {
            for a in args {
                collect_expr_features(a, features);
            }
        }
        Expr::Forall { vars, body } | Expr::Exists { vars, body } => {
            features.uses_quantifiers = true;
            for (name, _) in vars {
                features.vars.insert(name.clone());
            }
            collect_expr_features(body, features);
        }
        Expr::Cast { expr, .. } => collect_expr_features(expr, features),
        Expr::TensorIndex { tensor, indices } => {
            for i in indices {
                collect_expr_features(i, features);
            }
            collect_expr_features(tensor, features);
        }
        Expr::TensorReshape { tensor, .. } => collect_expr_features(tensor, features),
        Expr::Contains {
            collection,
            element,
        } => {
            collect_expr_features(collection, features);
            collect_expr_features(element, features);
        }
        Expr::Result
        | Expr::BoolLit(_)
        | Expr::IntLit(_)
        | Expr::FloatLit(_)
        | Expr::BitVecLit { .. }
        | Expr::Raw(_) => {}
        // Enum operations (Phase N3.1c)
        Expr::IsVariant { expr, .. } => collect_expr_features(expr, features),
        Expr::Discriminant(expr) => collect_expr_features(expr, features),
        Expr::VariantField { expr, .. } => collect_expr_features(expr, features),
    }
}

fn pick_induction_var(features: &Features) -> Option<String> {
    let preferred = ["n", "i", "k", "idx", "len", "size"];
    for p in preferred {
        if features.vars.contains(p) {
            return Some(p.to_string());
        }
    }
    features.vars.iter().next().cloned()
}

fn try_extract_sign_case_split(pred: &Predicate) -> Option<String> {
    let Predicate::Expr(e) = pred else {
        return None;
    };
    let (Expr::Ge(lhs, rhs) | Expr::Gt(lhs, rhs) | Expr::Le(lhs, rhs) | Expr::Lt(lhs, rhs)) = e
    else {
        return None;
    };
    let (Expr::Var(name), Expr::IntLit(0)) = (&**lhs, &**rhs) else {
        return None;
    };
    Some(name.clone())
}

fn maybe_case_split_condition(pred: &Predicate) -> Option<String> {
    match pred {
        Predicate::Implies(antecedent, _) => {
            if let Some(name) = try_extract_sign_case_split(antecedent) {
                return Some(format!("{name} >= 0"));
            }
            None
        }
        _ => None,
    }
}

/// Generate heuristic proof hints from a goal predicate.
///
/// This is intended for use when a backend fails (Unknown/timeout) and we want
/// to surface next steps. The output is deterministic.
#[must_use]
pub fn generate_proof_hints(goal: &Predicate) -> Vec<ProofHint> {
    let mut features = Features::default();
    collect_predicate_features(goal, &mut features);

    let mut hints: Vec<ProofHint> = Vec::new();

    let mut suggested_lemmas: BTreeSet<String> = BTreeSet::new();
    let mut suggest_lemma = |name: &str, description: &str, confidence: f64| {
        if suggested_lemmas.insert(name.to_string()) {
            hints.push(ProofHint::new(
                ProofHintKind::BuiltinLemma {
                    name: name.to_string(),
                },
                description,
                confidence,
            ));
        }
    };

    if features.uses_add {
        suggest_lemma(
            "add_commutative",
            "Try using the built-in lemma `add_commutative` for commutativity of addition.",
            0.65,
        );
        suggest_lemma(
            "add_associative",
            "Try using the built-in lemma `add_associative` for reassociating additions.",
            0.55,
        );
    }

    if features.uses_mul {
        suggest_lemma(
            "mul_commutative",
            "Try using the built-in lemma `mul_commutative` for commutativity of multiplication.",
            0.65,
        );
        suggest_lemma(
            "mul_associative",
            "Try using the built-in lemma `mul_associative` for reassociating multiplications.",
            0.55,
        );
    }

    if features.uses_add && features.uses_mul {
        suggest_lemma(
            "distributive",
            "Try using the built-in lemma `distributive` (a*(b+c) = a*b + a*c).",
            0.5,
        );
    }

    if features.uses_div || features.uses_rem {
        suggest_lemma(
            "div_mod_identity",
            "Try using the built-in lemma `div_mod_identity` relating div and mod.",
            0.55,
        );
        suggest_lemma(
            "mod_bounds",
            "Try using the built-in lemma `mod_bounds` (0 <= a% b < b for b>0).",
            0.45,
        );
    }

    if features.uses_abs {
        suggest_lemma(
            "abs_nonneg",
            "Try using the built-in lemma `abs_nonneg` (abs(x) >= 0).",
            0.6,
        );
    }

    if features.uses_minmax {
        suggest_lemma(
            "min_le",
            "Try using the built-in lemma `min_le` (min(a,b) <= a and <= b).",
            0.45,
        );
        suggest_lemma(
            "max_ge",
            "Try using the built-in lemma `max_ge` (max(a,b) >= a and >= b).",
            0.45,
        );
    }

    if features.uses_arrays {
        suggest_lemma(
            "zero_index_valid",
            "If indexing is involved, `zero_index_valid` can help (0 is a valid index when len>0).",
            0.35,
        );
        suggest_lemma(
            "last_index",
            "If indexing is involved, `last_index` can help (len-1 is in bounds when len>0).",
            0.35,
        );
    }

    if features.uses_quantifiers && (features.uses_add || features.uses_mul) {
        if let Some(var) = pick_induction_var(&features) {
            hints.push(ProofHint::new(
                ProofHintKind::Tactic(TacticKind::induction(var.clone())),
                format!("Consider `#[tactic(induction({var}))]` for quantified/arithmetic goals."),
                0.7,
            ));
        }
    }

    if features.uses_implication || features.uses_disjunction || features.uses_ite {
        if let Some(cond) = maybe_case_split_condition(goal) {
            hints.push(ProofHint::new(
                ProofHintKind::Tactic(TacticKind::case_split(cond.clone())),
                format!("Consider `#[tactic(case_split({cond}))]` to split proof cases."),
                0.55,
            ));
        } else {
            hints.push(ProofHint::new(
                ProofHintKind::Tactic(TacticKind::case_split("...".to_string())),
                "Consider `#[tactic(case_split(...))]` to split proof cases on a key condition."
                    .to_string(),
                0.4,
            ));
        }
    }

    if features.uses_quantifiers {
        // Quantifiers are frequently the reason solvers return Unknown; suggest a larger timeout.
        hints.push(ProofHint::new(
            ProofHintKind::TimeoutMs(60_000),
            "Try increasing timeout for this VC (e.g., 60s) when quantifiers are present."
                .to_string(),
            0.35,
        ));
    }

    // If we saw an obvious sign split in an implication antecedent, suggest the specialized helper.
    if let Predicate::Implies(antecedent, _) = goal {
        if let Some(var) = try_extract_sign_case_split(antecedent) {
            hints.push(ProofHint::new(
                ProofHintKind::Tactic(TacticKind::case_split_sign(var.clone())),
                format!("Consider `#[tactic(case_split_sign({var}))]` for sign-based branches."),
                0.75,
            ));
        }
    }

    // If no useful variable was discovered but we have quantifiers, add a generic induction suggestion.
    if features.uses_quantifiers
        && hints
            .iter()
            .all(|h| !matches!(h.kind, ProofHintKind::Tactic(TacticKind::Induction(_))))
    {
        hints.push(ProofHint::new(
            ProofHintKind::Tactic(TacticKind::Induction(crate::InductionTarget::Parameter(0))),
            "Consider induction on the primary parameter when proving recursive/quantified properties."
                .to_string(),
            0.4,
        ));
    }

    // Keep output small and deterministic: cap at 10 hints with stable ordering.
    hints.truncate(10);
    hints
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::VcType;

    // === ProofHintKind tests ===

    #[test]
    fn test_proof_hint_kind_equality() {
        assert_eq!(
            ProofHintKind::TimeoutMs(5000),
            ProofHintKind::TimeoutMs(5000)
        );
        assert_ne!(
            ProofHintKind::TimeoutMs(5000),
            ProofHintKind::TimeoutMs(6000)
        );
        assert_eq!(ProofHintKind::BmcDepth(10), ProofHintKind::BmcDepth(10));
        assert_eq!(
            ProofHintKind::BuiltinLemma {
                name: "foo".to_string()
            },
            ProofHintKind::BuiltinLemma {
                name: "foo".to_string()
            }
        );
    }

    #[test]
    fn test_proof_hint_kind_serialization() {
        let kinds = vec![
            ProofHintKind::Tactic(TacticKind::induction("n".to_string())),
            ProofHintKind::BuiltinLemma {
                name: "add_commutative".to_string(),
            },
            ProofHintKind::TimeoutMs(30000),
            ProofHintKind::BmcDepth(20),
        ];
        for kind in kinds {
            let json = serde_json::to_string(&kind).unwrap();
            let parsed: ProofHintKind = serde_json::from_str(&json).unwrap();
            assert_eq!(kind, parsed);
        }
    }

    // === ProofHint tests ===

    #[test]
    fn test_proof_hint_new() {
        let hint = ProofHint::new(ProofHintKind::TimeoutMs(10000), "Increase timeout", 0.75);
        assert_eq!(hint.confidence, 0.75);
        assert_eq!(hint.description, "Increase timeout");
        assert!(matches!(hint.kind, ProofHintKind::TimeoutMs(10000)));
    }

    #[test]
    fn test_proof_hint_confidence_clamping() {
        // Confidence above 1.0 should be clamped to 1.0
        let hint = ProofHint::new(ProofHintKind::BmcDepth(5), "test", 1.5);
        assert_eq!(hint.confidence, 1.0);

        // Confidence below 0.0 should be clamped to 0.0
        let hint = ProofHint::new(ProofHintKind::BmcDepth(5), "test", -0.5);
        assert_eq!(hint.confidence, 0.0);

        // Confidence within range should be unchanged
        let hint = ProofHint::new(ProofHintKind::BmcDepth(5), "test", 0.42);
        assert_eq!(hint.confidence, 0.42);
    }

    #[test]
    fn test_proof_hint_serialization() {
        let hint = ProofHint::new(
            ProofHintKind::BuiltinLemma {
                name: "mul_commutative".to_string(),
            },
            "Try commutativity",
            0.65,
        );
        let json = serde_json::to_string(&hint).unwrap();
        let parsed: ProofHint = serde_json::from_str(&json).unwrap();
        assert_eq!(hint, parsed);
    }

    // === Feature collection tests ===

    #[test]
    fn test_collect_expr_features_basic_ops() {
        let mut features = Features::default();
        let expr = Expr::var("a").add(Expr::var("b"));
        collect_expr_features(&expr, &mut features);
        assert!(features.uses_add);
        assert!(features.vars.contains("a"));
        assert!(features.vars.contains("b"));
    }

    #[test]
    fn test_collect_expr_features_mul_div_rem() {
        let mut features = Features::default();
        let expr = Expr::Div(
            Box::new(Expr::var("x").mul(Expr::var("y"))),
            Box::new(Expr::var("z")),
        );
        collect_expr_features(&expr, &mut features);
        assert!(features.uses_mul);
        assert!(features.uses_div);
        assert!(features.vars.contains("x"));
        assert!(features.vars.contains("y"));
        assert!(features.vars.contains("z"));

        let mut features2 = Features::default();
        let expr2 = Expr::Rem(Box::new(Expr::var("a")), Box::new(Expr::int(10)));
        collect_expr_features(&expr2, &mut features2);
        assert!(features2.uses_rem);
    }

    #[test]
    fn test_collect_expr_features_abs() {
        let mut features = Features::default();
        let expr = Expr::Abs(Box::new(Expr::var("x")));
        collect_expr_features(&expr, &mut features);
        assert!(features.uses_abs);
        assert!(features.vars.contains("x"));
    }

    #[test]
    fn test_collect_expr_features_minmax() {
        let mut features = Features::default();
        let expr = Expr::Min(Box::new(Expr::var("a")), Box::new(Expr::var("b")));
        collect_expr_features(&expr, &mut features);
        assert!(features.uses_minmax);

        let mut features2 = Features::default();
        let expr2 = Expr::Max(Box::new(Expr::var("x")), Box::new(Expr::var("y")));
        collect_expr_features(&expr2, &mut features2);
        assert!(features2.uses_minmax);
    }

    #[test]
    fn test_collect_expr_features_arrays() {
        let mut features = Features::default();
        let expr = Expr::ArrayIndex(Box::new(Expr::var("arr")), Box::new(Expr::var("i")));
        collect_expr_features(&expr, &mut features);
        assert!(features.uses_arrays);
        assert!(features.vars.contains("arr"));
        assert!(features.vars.contains("i"));

        let mut features2 = Features::default();
        let expr2 = Expr::ArrayLen(Box::new(Expr::var("vec")));
        collect_expr_features(&expr2, &mut features2);
        assert!(features2.uses_arrays);
    }

    #[test]
    fn test_collect_expr_features_ite() {
        let mut features = Features::default();
        let expr = Expr::Ite {
            cond: Box::new(Expr::var("cond")),
            then_: Box::new(Expr::var("then_val")),
            else_: Box::new(Expr::var("else_val")),
        };
        collect_expr_features(&expr, &mut features);
        assert!(features.uses_ite);
        assert!(features.vars.contains("cond"));
        assert!(features.vars.contains("then_val"));
        assert!(features.vars.contains("else_val"));
    }

    #[test]
    fn test_collect_expr_features_quantifiers() {
        let mut features = Features::default();
        let expr = Expr::Forall {
            vars: vec![(
                "n".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Expr::var("n").ge(Expr::int(0))),
        };
        collect_expr_features(&expr, &mut features);
        assert!(features.uses_quantifiers);
        assert!(features.vars.contains("n"));

        let mut features2 = Features::default();
        let expr2 = Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Expr::var("x").eq(Expr::int(42))),
        };
        collect_expr_features(&expr2, &mut features2);
        assert!(features2.uses_quantifiers);
    }

    #[test]
    fn test_collect_predicate_features_or() {
        let mut features = Features::default();
        let pred = Predicate::Or(vec![
            Predicate::expr(Expr::var("a").gt(Expr::int(0))),
            Predicate::expr(Expr::var("b").gt(Expr::int(0))),
        ]);
        collect_predicate_features(&pred, &mut features);
        assert!(features.uses_disjunction);
    }

    #[test]
    fn test_collect_predicate_features_implies() {
        let mut features = Features::default();
        let pred = Predicate::Implies(
            Box::new(Predicate::expr(Expr::var("x").ge(Expr::int(0)))),
            Box::new(Predicate::expr(Expr::var("x").ge(Expr::int(-1)))),
        );
        collect_predicate_features(&pred, &mut features);
        assert!(features.uses_implication);
    }

    #[test]
    fn test_collect_predicate_features_let_bindings() {
        let mut features = Features::default();
        let pred = Predicate::Let {
            bindings: vec![("y".to_string(), Expr::var("x").add(Expr::int(1)))],
            body: Box::new(Predicate::expr(Expr::var("y").gt(Expr::var("x")))),
        };
        collect_predicate_features(&pred, &mut features);
        assert!(features.vars.contains("y"));
        assert!(features.vars.contains("x"));
        assert!(features.uses_add);
    }

    // === pick_induction_var tests ===

    #[test]
    fn test_pick_induction_var_preferred() {
        let mut features = Features::default();
        features.vars.insert("n".to_string());
        features.vars.insert("x".to_string());
        assert_eq!(pick_induction_var(&features), Some("n".to_string()));
    }

    #[test]
    fn test_pick_induction_var_second_preferred() {
        let mut features = Features::default();
        features.vars.insert("i".to_string());
        features.vars.insert("x".to_string());
        assert_eq!(pick_induction_var(&features), Some("i".to_string()));
    }

    #[test]
    fn test_pick_induction_var_fallback() {
        let mut features = Features::default();
        features.vars.insert("foo".to_string());
        assert_eq!(pick_induction_var(&features), Some("foo".to_string()));
    }

    #[test]
    fn test_pick_induction_var_empty() {
        let features = Features::default();
        assert_eq!(pick_induction_var(&features), None);
    }

    // === try_extract_sign_case_split tests ===

    #[test]
    fn test_extract_sign_case_split_ge_zero() {
        let pred = Predicate::expr(Expr::var("x").ge(Expr::int(0)));
        assert_eq!(try_extract_sign_case_split(&pred), Some("x".to_string()));
    }

    #[test]
    fn test_extract_sign_case_split_gt_zero() {
        let pred = Predicate::expr(Expr::var("y").gt(Expr::int(0)));
        assert_eq!(try_extract_sign_case_split(&pred), Some("y".to_string()));
    }

    #[test]
    fn test_extract_sign_case_split_le_zero() {
        let pred = Predicate::expr(Expr::var("z").le(Expr::int(0)));
        assert_eq!(try_extract_sign_case_split(&pred), Some("z".to_string()));
    }

    #[test]
    fn test_extract_sign_case_split_lt_zero() {
        let pred = Predicate::expr(Expr::var("w").lt(Expr::int(0)));
        assert_eq!(try_extract_sign_case_split(&pred), Some("w".to_string()));
    }

    #[test]
    fn test_extract_sign_case_split_non_zero() {
        // Comparing against non-zero should not match
        let pred = Predicate::expr(Expr::var("x").ge(Expr::int(1)));
        assert_eq!(try_extract_sign_case_split(&pred), None);
    }

    #[test]
    fn test_extract_sign_case_split_non_var() {
        // Complex expression on LHS should not match
        let pred = Predicate::expr(Expr::var("x").add(Expr::var("y")).ge(Expr::int(0)));
        assert_eq!(try_extract_sign_case_split(&pred), None);
    }

    #[test]
    fn test_extract_sign_case_split_non_expr() {
        // Non-Expr predicate should not match
        let pred = Predicate::Bool(true);
        assert_eq!(try_extract_sign_case_split(&pred), None);
    }

    // === maybe_case_split_condition tests ===

    #[test]
    fn test_maybe_case_split_condition_with_sign() {
        let antecedent = Predicate::expr(Expr::var("x").ge(Expr::int(0)));
        let consequent = Predicate::expr(Expr::var("x").ge(Expr::int(-5)));
        let pred = Predicate::Implies(Box::new(antecedent), Box::new(consequent));
        assert_eq!(
            maybe_case_split_condition(&pred),
            Some("x >= 0".to_string())
        );
    }

    #[test]
    fn test_maybe_case_split_condition_no_sign() {
        let antecedent = Predicate::expr(Expr::var("x").eq(Expr::int(5)));
        let consequent = Predicate::expr(Expr::var("x").gt(Expr::int(0)));
        let pred = Predicate::Implies(Box::new(antecedent), Box::new(consequent));
        assert_eq!(maybe_case_split_condition(&pred), None);
    }

    #[test]
    fn test_maybe_case_split_condition_non_implies() {
        let pred = Predicate::expr(Expr::var("x").ge(Expr::int(0)));
        assert_eq!(maybe_case_split_condition(&pred), None);
    }

    // === generate_proof_hints tests ===

    #[test]
    fn test_generate_proof_hints_suggests_add_lemmas() {
        let goal = Predicate::expr(
            Expr::var("a")
                .add(Expr::var("b"))
                .eq(Expr::var("b").add(Expr::var("a"))),
        );
        let hints = generate_proof_hints(&goal);
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "add_commutative"
        )));
    }

    #[test]
    fn test_generate_proof_hints_suggests_induction_for_quantified_arithmetic() {
        let body = Predicate::expr(Expr::var("n").add(Expr::int(1)).ge(Expr::var("n")));
        let goal = Predicate::forall(
            vec![(
                "n".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body,
        );

        let hints = generate_proof_hints(&goal);
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::Tactic(TacticKind::Induction(crate::InductionTarget::Variable(ref v))) if v == "n"
        )));
    }

    #[test]
    fn test_generate_proof_hints_suggests_case_split_sign() {
        let antecedent = Predicate::expr(Expr::var("x").ge(Expr::int(0)));
        let consequent = Predicate::expr(Expr::var("x").ge(Expr::int(-5)));
        let goal = Predicate::Implies(Box::new(antecedent), Box::new(consequent));

        let hints = generate_proof_hints(&goal);
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::Tactic(TacticKind::CaseSplit(crate::CaseSplitCondition::Sign(ref v))) if v == "x"
        )));
    }

    #[test]
    fn test_generate_proof_hints_suggests_mul_lemmas() {
        let goal = Predicate::expr(
            Expr::var("a")
                .mul(Expr::var("b"))
                .eq(Expr::var("b").mul(Expr::var("a"))),
        );
        let hints = generate_proof_hints(&goal);
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "mul_commutative"
        )));
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "mul_associative"
        )));
    }

    #[test]
    fn test_generate_proof_hints_suggests_distributive() {
        // a * (b + c) should suggest distributive lemma (has both add and mul)
        let goal = Predicate::expr(Expr::var("a").mul(Expr::var("b").add(Expr::var("c"))));
        let hints = generate_proof_hints(&goal);
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "distributive"
        )));
    }

    #[test]
    fn test_generate_proof_hints_suggests_div_mod_lemmas() {
        // (a / b) * b + (a % b) == a
        let a_div_b = Expr::Div(Box::new(Expr::var("a")), Box::new(Expr::var("b")));
        let a_mod_b = Expr::Rem(Box::new(Expr::var("a")), Box::new(Expr::var("b")));
        let goal = Predicate::expr(a_div_b.mul(Expr::var("b")).add(a_mod_b).eq(Expr::var("a")));
        let hints = generate_proof_hints(&goal);
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "div_mod_identity"
        )));
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "mod_bounds"
        )));
    }

    #[test]
    fn test_generate_proof_hints_suggests_abs_lemma() {
        let goal = Predicate::expr(Expr::Abs(Box::new(Expr::var("x"))).ge(Expr::int(0)));
        let hints = generate_proof_hints(&goal);
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "abs_nonneg"
        )));
    }

    #[test]
    fn test_generate_proof_hints_suggests_minmax_lemmas() {
        let min_ab = Expr::Min(Box::new(Expr::var("a")), Box::new(Expr::var("b")));
        let goal = Predicate::expr(min_ab.le(Expr::var("a")));
        let hints = generate_proof_hints(&goal);
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "min_le"
        )));

        let max_ab = Expr::Max(Box::new(Expr::var("a")), Box::new(Expr::var("b")));
        let goal2 = Predicate::expr(max_ab.ge(Expr::var("a")));
        let hints2 = generate_proof_hints(&goal2);
        assert!(hints2.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "max_ge"
        )));
    }

    #[test]
    fn test_generate_proof_hints_suggests_array_lemmas() {
        let goal = Predicate::expr(
            Expr::ArrayIndex(Box::new(Expr::var("arr")), Box::new(Expr::int(0))).ge(Expr::int(0)),
        );
        let hints = generate_proof_hints(&goal);
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "zero_index_valid"
        )));
        assert!(hints.iter().any(|h| matches!(
            h.kind,
            ProofHintKind::BuiltinLemma { ref name } if name == "last_index"
        )));
    }

    #[test]
    fn test_generate_proof_hints_timeout_for_quantifiers() {
        let goal = Predicate::forall(
            vec![(
                "n".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            Predicate::expr(Expr::var("n").ge(Expr::var("n"))),
        );
        let hints = generate_proof_hints(&goal);
        assert!(hints
            .iter()
            .any(|h| matches!(h.kind, ProofHintKind::TimeoutMs(60_000))));
    }

    #[test]
    fn test_generate_proof_hints_generic_case_split() {
        // Disjunction without sign split should suggest generic case split
        let goal = Predicate::Or(vec![
            Predicate::expr(Expr::var("a").eq(Expr::int(1))),
            Predicate::expr(Expr::var("a").eq(Expr::int(2))),
        ]);
        let hints = generate_proof_hints(&goal);
        assert!(hints
            .iter()
            .any(|h| matches!(h.kind, ProofHintKind::Tactic(TacticKind::CaseSplit(_)))));
    }

    #[test]
    fn test_generate_proof_hints_truncates_to_10() {
        // Create a complex goal that triggers many hints
        // n * (n + 1) / 2 == len(arr)
        let n_times_np1 = Expr::var("n").mul(Expr::var("n").add(Expr::int(1)));
        let divided = Expr::Div(Box::new(n_times_np1), Box::new(Expr::int(2)));
        let body = Predicate::Or(vec![Predicate::Implies(
            Box::new(Predicate::expr(Expr::var("n").ge(Expr::int(0)))),
            Box::new(Predicate::expr(
                divided.eq(Expr::ArrayLen(Box::new(Expr::var("arr")))),
            )),
        )]);
        let goal = Predicate::forall(
            vec![(
                "n".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body,
        );
        let hints = generate_proof_hints(&goal);
        assert!(hints.len() <= 10);
    }

    #[test]
    fn test_generate_proof_hints_empty_for_simple_bool() {
        let goal = Predicate::Bool(true);
        let hints = generate_proof_hints(&goal);
        // Simple bool should not trigger many hints
        assert!(hints.len() < 5);
    }

    #[test]
    fn test_generate_proof_hints_no_duplicate_lemmas() {
        // Multiple additions should not suggest add_commutative twice
        let goal = Predicate::expr(
            Expr::var("a")
                .add(Expr::var("b"))
                .add(Expr::var("c"))
                .eq(Expr::var("c").add(Expr::var("b")).add(Expr::var("a"))),
        );
        let hints = generate_proof_hints(&goal);
        let add_comm_count = hints
            .iter()
            .filter(|h| {
                matches!(
                    h.kind,
                    ProofHintKind::BuiltinLemma { ref name } if name == "add_commutative"
                )
            })
            .count();
        assert_eq!(add_comm_count, 1);
    }
}
