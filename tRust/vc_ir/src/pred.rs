//! Predicates in the VC IR
//!
//! Predicates are boolean-valued assertions used in verification conditions.

// Allow builder method names that overlap with std traits - intentional DSL design
#![allow(clippy::should_implement_trait)]

use crate::{Expr, VcType};
use serde::{Deserialize, Serialize};

/// A predicate (boolean assertion)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Predicate {
    /// Literal true/false
    Bool(bool),

    /// An expression that evaluates to bool
    Expr(Expr),

    /// Logical negation
    Not(Box<Predicate>),

    /// Logical conjunction
    And(Vec<Predicate>),

    /// Logical disjunction
    Or(Vec<Predicate>),

    /// Implication
    Implies(Box<Predicate>, Box<Predicate>),

    /// Biconditional (iff)
    Iff(Box<Predicate>, Box<Predicate>),

    /// Universal quantification
    Forall {
        vars: Vec<(String, VcType)>,
        triggers: Vec<Vec<Expr>>, // SMT triggers for instantiation
        body: Box<Predicate>,
    },

    /// Existential quantification
    Exists {
        vars: Vec<(String, VcType)>,
        body: Box<Predicate>,
    },

    /// Let binding for common subexpressions
    Let {
        bindings: Vec<(String, Expr)>,
        body: Box<Predicate>,
    },
}

impl Predicate {
    #[must_use]
    pub const fn t() -> Self {
        Self::Bool(true)
    }

    #[must_use]
    pub const fn f() -> Self {
        Self::Bool(false)
    }

    #[must_use]
    pub const fn expr(e: Expr) -> Self {
        Self::Expr(e)
    }

    #[must_use]
    pub fn not(self) -> Self {
        Self::Not(Box::new(self))
    }

    #[must_use]
    pub fn and(preds: Vec<Self>) -> Self {
        if preds.is_empty() {
            Self::Bool(true)
        } else if preds.len() == 1 {
            preds
                .into_iter()
                .next()
                .expect("len()==1 guarantees element exists")
        } else {
            Self::And(preds)
        }
    }

    #[must_use]
    pub fn or(preds: Vec<Self>) -> Self {
        if preds.is_empty() {
            Self::Bool(false)
        } else if preds.len() == 1 {
            preds
                .into_iter()
                .next()
                .expect("len()==1 guarantees element exists")
        } else {
            Self::Or(preds)
        }
    }

    #[must_use]
    pub fn implies(self, other: Self) -> Self {
        Self::Implies(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn iff(self, other: Self) -> Self {
        Self::Iff(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn forall(vars: Vec<(String, VcType)>, body: Self) -> Self {
        Self::Forall {
            vars,
            triggers: vec![],
            body: Box::new(body),
        }
    }

    #[must_use]
    pub fn forall_with_triggers(
        vars: Vec<(String, VcType)>,
        triggers: Vec<Vec<Expr>>,
        body: Self,
    ) -> Self {
        Self::Forall {
            vars,
            triggers,
            body: Box::new(body),
        }
    }

    #[must_use]
    pub fn exists(vars: Vec<(String, VcType)>, body: Self) -> Self {
        Self::Exists {
            vars,
            body: Box::new(body),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum PredPrec {
    Lowest = 0,
    Iff = 1,
    Implies = 2,
    Or = 3,
    And = 4,
    Unary = 5,
    Atom = 6,
}

const fn pred_prec(p: &Predicate) -> PredPrec {
    match p {
        Predicate::Iff(_, _) => PredPrec::Iff,
        Predicate::Implies(_, _) => PredPrec::Implies,
        Predicate::Or(_) => PredPrec::Or,
        Predicate::And(_) => PredPrec::And,
        Predicate::Not(_) => PredPrec::Unary,
        Predicate::Bool(_)
        | Predicate::Expr(_)
        | Predicate::Forall { .. }
        | Predicate::Exists { .. }
        | Predicate::Let { .. } => PredPrec::Atom,
    }
}

fn fmt_pred(
    p: &Predicate,
    parent_prec: PredPrec,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    let prec = pred_prec(p);
    let needs_parens = prec < parent_prec;
    if needs_parens {
        write!(f, "(")?;
    }

    match p {
        Predicate::Bool(v) => write!(f, "{v}")?,
        Predicate::Expr(e) => write!(f, "{e}")?,
        Predicate::Not(inner) => {
            write!(f, "!")?;
            fmt_pred(inner, PredPrec::Unary, f)?;
        }
        Predicate::And(preds) => {
            for (i, pred) in preds.iter().enumerate() {
                if i > 0 {
                    write!(f, " && ")?;
                }
                fmt_pred(pred, PredPrec::And, f)?;
            }
        }
        Predicate::Or(preds) => {
            for (i, pred) in preds.iter().enumerate() {
                if i > 0 {
                    write!(f, " || ")?;
                }
                fmt_pred(pred, PredPrec::Or, f)?;
            }
        }
        Predicate::Implies(a, b) => {
            fmt_pred(a, PredPrec::Implies, f)?;
            write!(f, " => ")?;
            fmt_pred(b, PredPrec::And, f)?;
        }
        Predicate::Iff(a, b) => {
            fmt_pred(a, PredPrec::Iff, f)?;
            write!(f, " <=> ")?;
            fmt_pred(b, PredPrec::Implies, f)?;
        }
        Predicate::Forall {
            vars,
            triggers,
            body,
        } => {
            write!(f, "forall ")?;
            fmt_vars(vars, f)?;
            if !triggers.is_empty() {
                write!(f, " /* triggers: ")?;
                for (i, trig) in triggers.iter().enumerate() {
                    if i > 0 {
                        write!(f, "; ")?;
                    }
                    write!(f, "[")?;
                    for (j, e) in trig.iter().enumerate() {
                        if j > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{e}")?;
                    }
                    write!(f, "]")?;
                }
                write!(f, " */")?;
            }
            write!(f, " {{ ")?;
            fmt_pred(body, PredPrec::Lowest, f)?;
            write!(f, " }}")?;
        }
        Predicate::Exists { vars, body } => {
            write!(f, "exists ")?;
            fmt_vars(vars, f)?;
            write!(f, " {{ ")?;
            fmt_pred(body, PredPrec::Lowest, f)?;
            write!(f, " }}")?;
        }
        Predicate::Let { bindings, body } => {
            write!(f, "let ")?;
            for (i, (name, expr)) in bindings.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{name} = {expr}")?;
            }
            write!(f, "; ")?;
            fmt_pred(body, PredPrec::Lowest, f)?;
        }
    }

    if needs_parens {
        write!(f, ")")?;
    }
    Ok(())
}

fn fmt_vars(vars: &[(String, VcType)], f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for (i, (name, ty)) in vars.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{name}: {ty}")?;
    }
    Ok(())
}

impl std::fmt::Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_pred(self, PredPrec::Lowest, f)
    }
}

// === Borrow Tracking Types (Phase N3.1b) ===

/// Unique identifier for a borrow
///
/// Each borrow in a function gets a unique ID for tracking.
/// This enables:
/// - Matching BorrowBegin with BorrowEnd
/// - Tracking reborrow hierarchies
/// - Detecting use-after-free through stale borrow IDs
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BorrowId(pub u32);

impl BorrowId {
    /// Create a new borrow ID
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }
}

impl std::fmt::Display for BorrowId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "borrow_{}", self.0)
    }
}

/// The kind of borrow
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BorrowKind {
    /// Shared borrow: &T (read-only, multiple allowed)
    Shared,
    /// Mutable borrow: &mut T (exclusive access)
    Mutable,
    /// Two-phase borrow (for method calls like `v.push(v.len())`)
    /// Initially acts as shared, converts to mutable at activation
    TwoPhase,
}

impl std::fmt::Display for BorrowKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Shared => write!(f, "&"),
            Self::Mutable => write!(f, "&mut"),
            Self::TwoPhase => write!(f, "&2phase"),
        }
    }
}

/// The kind of access through a borrow
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BorrowAccessKind {
    /// Read access (allowed for both shared and mutable borrows)
    Read,
    /// Write access (only allowed for mutable borrows)
    Write,
}

impl std::fmt::Display for BorrowAccessKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Read => write!(f, "read"),
            Self::Write => write!(f, "write"),
        }
    }
}

/// Separation logic assertions for heap reasoning
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SeparationAssertion {
    /// Empty heap
    Emp,

    /// Points-to: x |-> v
    PointsTo { location: Expr, value: Expr },

    /// Separating conjunction: P * Q (heaps are disjoint)
    SepConj(Box<SeparationAssertion>, Box<SeparationAssertion>),

    /// Separating implication (magic wand): P -* Q
    SepImpl(Box<SeparationAssertion>, Box<SeparationAssertion>),

    /// Pure assertion (no heap)
    Pure(Predicate),

    /// Existential
    Exists {
        vars: Vec<(String, VcType)>,
        body: Box<SeparationAssertion>,
    },

    /// Predicate application (for recursive data structures)
    Pred { name: String, args: Vec<Expr> },

    /// List segment: lseg(x, y) means linked list from x to y
    ListSeg {
        head: Expr,
        tail: Expr,
        element_type: VcType,
    },

    /// Tree rooted at node
    Tree { root: Expr, element_type: VcType },

    // === Borrow Lifecycle Assertions (Phase N3.1b) ===
    /// Borrow begins: marks the start of a borrow region
    ///
    /// When a borrow begins, we assert that the location is valid and
    /// transfer the permission to the borrow. For mutable borrows, this
    /// means exclusive access. For shared borrows, this means read-only access.
    ///
    /// In separation logic terms:
    /// - Mutable: `location |-> value` becomes `borrow_id |-> (location, value)`
    /// - Shared: `location |-> value` becomes `location |-> value * borrow_id.read`
    BorrowBegin {
        borrow_id: BorrowId,
        kind: BorrowKind,
        location: Expr,
        /// The value at the location when the borrow begins
        value: Expr,
    },

    /// Borrow ends: marks the end of a borrow region
    ///
    /// When a borrow ends, the permission is returned:
    /// - Mutable borrows: `borrow_id |-> (location, value')` becomes `location |-> value'`
    /// - Shared borrows: permission token is released
    ///
    /// This enables use-after-free detection: any access after BorrowEnd
    /// for an expired borrow generates a proof obligation that will fail.
    BorrowEnd {
        borrow_id: BorrowId,
        /// For mutable borrows, the potentially modified value
        final_value: Option<Expr>,
    },

    /// Reborrow: create a new borrow from an existing borrow
    ///
    /// When we reborrow (e.g., `&mut *existing_ref`), the new borrow
    /// must be nested within the existing borrow's lifetime.
    ///
    /// Generates proof obligations:
    /// - new_borrow lifetime ⊆ parent_borrow lifetime
    /// - If parent is mutable, new can be shared or mutable
    /// - If parent is shared, new must be shared
    Reborrow {
        new_borrow: BorrowId,
        parent_borrow: BorrowId,
        new_kind: BorrowKind,
    },

    /// Borrow access: any read/write through a borrow
    ///
    /// Generates proof obligation that borrow is still active (not ended)
    BorrowAccess {
        borrow_id: BorrowId,
        access_kind: BorrowAccessKind,
        location: Expr,
    },
}

impl SeparationAssertion {
    #[must_use]
    pub const fn emp() -> Self {
        Self::Emp
    }

    #[must_use]
    pub const fn points_to(location: Expr, value: Expr) -> Self {
        Self::PointsTo { location, value }
    }

    #[must_use]
    pub fn sep_conj(self, other: Self) -> Self {
        Self::SepConj(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub const fn pure(p: Predicate) -> Self {
        Self::Pure(p)
    }

    // === Borrow lifecycle builders (Phase N3.1b) ===

    /// Create a BorrowBegin assertion
    #[must_use]
    pub const fn borrow_begin(
        borrow_id: BorrowId,
        kind: BorrowKind,
        location: Expr,
        value: Expr,
    ) -> Self {
        Self::BorrowBegin {
            borrow_id,
            kind,
            location,
            value,
        }
    }

    /// Create a BorrowEnd assertion
    #[must_use]
    pub const fn borrow_end(borrow_id: BorrowId, final_value: Option<Expr>) -> Self {
        Self::BorrowEnd {
            borrow_id,
            final_value,
        }
    }

    /// Create a Reborrow assertion
    #[must_use]
    pub const fn reborrow(
        new_borrow: BorrowId,
        parent_borrow: BorrowId,
        new_kind: BorrowKind,
    ) -> Self {
        Self::Reborrow {
            new_borrow,
            parent_borrow,
            new_kind,
        }
    }

    /// Create a BorrowAccess assertion for read
    #[must_use]
    pub const fn borrow_read(borrow_id: BorrowId, location: Expr) -> Self {
        Self::BorrowAccess {
            borrow_id,
            access_kind: BorrowAccessKind::Read,
            location,
        }
    }

    /// Create a BorrowAccess assertion for write
    #[must_use]
    pub const fn borrow_write(borrow_id: BorrowId, location: Expr) -> Self {
        Self::BorrowAccess {
            borrow_id,
            access_kind: BorrowAccessKind::Write,
            location,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ============================================
    // Predicate tests
    // ============================================

    #[test]
    fn test_predicate_literals() {
        let t = Predicate::t();
        assert!(matches!(t, Predicate::Bool(true)));

        let f = Predicate::f();
        assert!(matches!(f, Predicate::Bool(false)));
    }

    #[test]
    fn test_predicate_from_expr() {
        let e = Expr::var("x").gt(Expr::int(0));
        let p = Predicate::expr(e);
        assert!(matches!(p, Predicate::Expr(_)));
    }

    #[test]
    fn test_predicate_display_basic() {
        let p = Predicate::expr(Expr::var("age").gt(Expr::int(18)));
        assert_eq!(p.to_string(), "age > 18");

        let p = Predicate::and(vec![
            Predicate::expr(Expr::var("a").gt(Expr::int(0))),
            Predicate::expr(Expr::var("b").gt(Expr::int(0))),
        ]);
        assert_eq!(p.to_string(), "a > 0 && b > 0");
    }

    #[test]
    fn test_predicate_not() {
        let p = Predicate::t().not();
        assert!(matches!(p, Predicate::Not(_)));

        // Double negation
        let pp = p.not();
        assert!(matches!(pp, Predicate::Not(_)));
    }

    #[test]
    fn test_predicate_and() {
        // Empty and = true
        let empty_and = Predicate::and(vec![]);
        assert!(matches!(empty_and, Predicate::Bool(true)));

        // Single element = that element
        let single = Predicate::and(vec![Predicate::t()]);
        assert!(matches!(single, Predicate::Bool(true)));

        // Multiple elements = And
        let multi = Predicate::and(vec![Predicate::t(), Predicate::f(), Predicate::t()]);
        assert!(matches!(multi, Predicate::And(ref v) if v.len() == 3));
    }

    #[test]
    fn test_predicate_or() {
        // Empty or = false
        let empty_or = Predicate::or(vec![]);
        assert!(matches!(empty_or, Predicate::Bool(false)));

        // Single element = that element
        let single = Predicate::or(vec![Predicate::f()]);
        assert!(matches!(single, Predicate::Bool(false)));

        // Multiple elements = Or
        let multi = Predicate::or(vec![Predicate::t(), Predicate::f()]);
        assert!(matches!(multi, Predicate::Or(ref v) if v.len() == 2));
    }

    #[test]
    fn test_predicate_implies() {
        let p = Predicate::t();
        let q = Predicate::f();
        let imp = p.implies(q);
        assert!(matches!(imp, Predicate::Implies(_, _)));
    }

    #[test]
    fn test_predicate_iff() {
        let p = Predicate::t();
        let q = Predicate::t();
        let iff = p.iff(q);
        assert!(matches!(iff, Predicate::Iff(_, _)));
    }

    #[test]
    fn test_predicate_forall() {
        let body = Predicate::expr(Expr::var("x").gt(Expr::int(0)));
        let forall = Predicate::forall(
            vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body,
        );

        match forall {
            Predicate::Forall {
                vars,
                triggers,
                body: _,
            } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "x");
                assert!(triggers.is_empty()); // No triggers by default
            }
            _ => panic!("Expected Forall"),
        }
    }

    #[test]
    fn test_predicate_forall_with_triggers() {
        let body = Predicate::expr(Expr::var("x").gt(Expr::int(0)));
        let trigger = vec![Expr::var("x")];
        let forall = Predicate::forall_with_triggers(
            vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            vec![trigger],
            body,
        );

        match forall {
            Predicate::Forall { triggers, .. } => {
                assert_eq!(triggers.len(), 1);
            }
            _ => panic!("Expected Forall"),
        }
    }

    #[test]
    fn test_predicate_exists() {
        let body = Predicate::expr(Expr::var("x").eq(Expr::int(42)));
        let exists = Predicate::exists(
            vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body,
        );

        match exists {
            Predicate::Exists { vars, body: _ } => {
                assert_eq!(vars.len(), 1);
            }
            _ => panic!("Expected Exists"),
        }
    }

    #[test]
    fn test_predicate_let() {
        let pred = Predicate::Let {
            bindings: vec![("y".to_string(), Expr::var("x").mul(Expr::int(2)))],
            body: Box::new(Predicate::expr(Expr::var("y").gt(Expr::int(0)))),
        };

        match pred {
            Predicate::Let { bindings, body: _ } => {
                assert_eq!(bindings.len(), 1);
                assert_eq!(bindings[0].0, "y");
            }
            _ => panic!("Expected Let"),
        }
    }

    #[test]
    fn test_complex_predicate() {
        // (x > 0) && (y > 0) => (x + y > 0)
        let x_pos = Predicate::expr(Expr::var("x").gt(Expr::int(0)));
        let y_pos = Predicate::expr(Expr::var("y").gt(Expr::int(0)));
        let sum_pos = Predicate::expr(Expr::var("x").add(Expr::var("y")).gt(Expr::int(0)));

        let antecedent = Predicate::and(vec![x_pos, y_pos]);
        let implication = antecedent.implies(sum_pos);

        assert!(matches!(implication, Predicate::Implies(_, _)));
    }

    #[test]
    fn test_predicate_serialization() {
        let pred = Predicate::and(vec![
            Predicate::t(),
            Predicate::expr(Expr::var("x").gt(Expr::int(0))),
        ]);

        let json = serde_json::to_string(&pred).expect("serialize");
        let parsed: Predicate = serde_json::from_str(&json).expect("deserialize");

        assert!(matches!(parsed, Predicate::And(_)));
    }

    // ============================================
    // SeparationAssertion tests
    // ============================================

    #[test]
    fn test_sep_emp() {
        let emp = SeparationAssertion::emp();
        assert!(matches!(emp, SeparationAssertion::Emp));
    }

    #[test]
    fn test_sep_points_to() {
        let loc = Expr::var("ptr");
        let val = Expr::int(42);
        let pts = SeparationAssertion::points_to(loc, val);

        assert!(matches!(pts, SeparationAssertion::PointsTo { .. }));
    }

    #[test]
    fn test_sep_conj() {
        let p1 = SeparationAssertion::emp();
        let p2 = SeparationAssertion::points_to(Expr::var("x"), Expr::int(1));
        let conj = p1.sep_conj(p2);

        assert!(matches!(conj, SeparationAssertion::SepConj(_, _)));
    }

    #[test]
    fn test_sep_pure() {
        let pred = Predicate::t();
        let pure = SeparationAssertion::pure(pred);

        assert!(matches!(pure, SeparationAssertion::Pure(_)));
    }

    #[test]
    fn test_sep_impl() {
        let p = SeparationAssertion::emp();
        let q = SeparationAssertion::points_to(Expr::var("x"), Expr::int(0));
        let wand = SeparationAssertion::SepImpl(Box::new(p), Box::new(q));

        assert!(matches!(wand, SeparationAssertion::SepImpl(_, _)));
    }

    #[test]
    fn test_sep_exists() {
        let body = SeparationAssertion::points_to(Expr::var("x"), Expr::var("v"));
        let exists = SeparationAssertion::Exists {
            vars: vec![(
                "v".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(body),
        };

        assert!(matches!(exists, SeparationAssertion::Exists { .. }));
    }

    #[test]
    fn test_sep_pred_application() {
        let pred = SeparationAssertion::Pred {
            name: "is_list".to_string(),
            args: vec![Expr::var("head"), Expr::var("len")],
        };

        match pred {
            SeparationAssertion::Pred { name, args } => {
                assert_eq!(name, "is_list");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected Pred"),
        }
    }

    #[test]
    fn test_sep_list_seg() {
        let lseg = SeparationAssertion::ListSeg {
            head: Expr::var("head"),
            tail: Expr::var("null"),
            element_type: VcType::Int {
                signed: true,
                bits: 32,
            },
        };

        assert!(matches!(lseg, SeparationAssertion::ListSeg { .. }));
    }

    #[test]
    fn test_sep_tree() {
        let tree = SeparationAssertion::Tree {
            root: Expr::var("root"),
            element_type: VcType::Int {
                signed: false,
                bits: 64,
            },
        };

        assert!(matches!(tree, SeparationAssertion::Tree { .. }));
    }

    #[test]
    fn test_complex_separation_assertion() {
        // x |-> 1 * y |-> 2 * Pure(x != y)
        let pts_x = SeparationAssertion::points_to(Expr::var("x"), Expr::int(1));
        let pts_y = SeparationAssertion::points_to(Expr::var("y"), Expr::int(2));
        let neq =
            SeparationAssertion::pure(Predicate::expr(Expr::var("x").eq(Expr::var("y")).not()));

        let combined = pts_x.sep_conj(pts_y).sep_conj(neq);
        assert!(matches!(combined, SeparationAssertion::SepConj(_, _)));
    }

    #[test]
    fn test_separation_serialization() {
        let sep = SeparationAssertion::points_to(Expr::var("ptr"), Expr::int(0));

        let json = serde_json::to_string(&sep).expect("serialize");
        let parsed: SeparationAssertion = serde_json::from_str(&json).expect("deserialize");

        assert!(matches!(parsed, SeparationAssertion::PointsTo { .. }));
    }

    // ============================================
    // Borrow lifecycle tests (Phase N3.1b)
    // ============================================

    #[test]
    fn test_borrow_id() {
        let id1 = BorrowId::new(1);
        let id2 = BorrowId::new(2);
        let id1_copy = BorrowId::new(1);

        assert_eq!(id1, id1_copy);
        assert_ne!(id1, id2);
        assert_eq!(id1.to_string(), "borrow_1");
        assert_eq!(id2.to_string(), "borrow_2");
    }

    #[test]
    fn test_borrow_kind_display() {
        assert_eq!(BorrowKind::Shared.to_string(), "&");
        assert_eq!(BorrowKind::Mutable.to_string(), "&mut");
        assert_eq!(BorrowKind::TwoPhase.to_string(), "&2phase");
    }

    #[test]
    fn test_borrow_access_kind_display() {
        assert_eq!(BorrowAccessKind::Read.to_string(), "read");
        assert_eq!(BorrowAccessKind::Write.to_string(), "write");
    }

    #[test]
    fn test_borrow_begin() {
        let borrow = SeparationAssertion::borrow_begin(
            BorrowId::new(1),
            BorrowKind::Mutable,
            Expr::var("x"),
            Expr::int(42),
        );

        match borrow {
            SeparationAssertion::BorrowBegin {
                borrow_id,
                kind,
                location: _,
                value: _,
            } => {
                assert_eq!(borrow_id, BorrowId::new(1));
                assert_eq!(kind, BorrowKind::Mutable);
            }
            _ => panic!("Expected BorrowBegin"),
        }
    }

    #[test]
    fn test_borrow_end() {
        let borrow_end = SeparationAssertion::borrow_end(BorrowId::new(1), Some(Expr::int(100)));

        match borrow_end {
            SeparationAssertion::BorrowEnd {
                borrow_id,
                final_value,
            } => {
                assert_eq!(borrow_id, BorrowId::new(1));
                assert!(final_value.is_some());
            }
            _ => panic!("Expected BorrowEnd"),
        }
    }

    #[test]
    fn test_reborrow() {
        let reborrow =
            SeparationAssertion::reborrow(BorrowId::new(2), BorrowId::new(1), BorrowKind::Mutable);

        match reborrow {
            SeparationAssertion::Reborrow {
                new_borrow,
                parent_borrow,
                new_kind,
            } => {
                assert_eq!(new_borrow, BorrowId::new(2));
                assert_eq!(parent_borrow, BorrowId::new(1));
                assert_eq!(new_kind, BorrowKind::Mutable);
            }
            _ => panic!("Expected Reborrow"),
        }
    }

    #[test]
    fn test_borrow_read_access() {
        let access = SeparationAssertion::borrow_read(BorrowId::new(1), Expr::var("x"));

        match access {
            SeparationAssertion::BorrowAccess {
                borrow_id,
                access_kind,
                location: _,
            } => {
                assert_eq!(borrow_id, BorrowId::new(1));
                assert_eq!(access_kind, BorrowAccessKind::Read);
            }
            _ => panic!("Expected BorrowAccess"),
        }
    }

    #[test]
    fn test_borrow_write_access() {
        let access = SeparationAssertion::borrow_write(BorrowId::new(1), Expr::var("x"));

        match access {
            SeparationAssertion::BorrowAccess {
                borrow_id,
                access_kind,
                location: _,
            } => {
                assert_eq!(borrow_id, BorrowId::new(1));
                assert_eq!(access_kind, BorrowAccessKind::Write);
            }
            _ => panic!("Expected BorrowAccess"),
        }
    }

    #[test]
    fn test_borrow_lifecycle_serialization() {
        // Test BorrowBegin serialization
        let begin = SeparationAssertion::borrow_begin(
            BorrowId::new(1),
            BorrowKind::Mutable,
            Expr::var("x"),
            Expr::int(10),
        );
        let json = serde_json::to_string(&begin).expect("serialize begin");
        let parsed: SeparationAssertion = serde_json::from_str(&json).expect("deserialize begin");
        assert!(matches!(parsed, SeparationAssertion::BorrowBegin { .. }));

        // Test BorrowEnd serialization
        let end = SeparationAssertion::borrow_end(BorrowId::new(1), None);
        let json = serde_json::to_string(&end).expect("serialize end");
        let parsed: SeparationAssertion = serde_json::from_str(&json).expect("deserialize end");
        assert!(matches!(parsed, SeparationAssertion::BorrowEnd { .. }));

        // Test Reborrow serialization
        let reborrow =
            SeparationAssertion::reborrow(BorrowId::new(2), BorrowId::new(1), BorrowKind::Shared);
        let json = serde_json::to_string(&reborrow).expect("serialize reborrow");
        let parsed: SeparationAssertion =
            serde_json::from_str(&json).expect("deserialize reborrow");
        assert!(matches!(parsed, SeparationAssertion::Reborrow { .. }));
    }

    #[test]
    fn test_borrow_lifecycle_composition() {
        // Test composing borrow assertions with separating conjunction
        // This models: x borrowed mutably * y borrowed shared
        let borrow_x = SeparationAssertion::borrow_begin(
            BorrowId::new(1),
            BorrowKind::Mutable,
            Expr::var("x"),
            Expr::int(1),
        );
        let borrow_y = SeparationAssertion::borrow_begin(
            BorrowId::new(2),
            BorrowKind::Shared,
            Expr::var("y"),
            Expr::int(2),
        );
        let combined = borrow_x.sep_conj(borrow_y);

        assert!(matches!(combined, SeparationAssertion::SepConj(_, _)));
    }
}
