//! Expressions in the VC IR
//!
//! These represent values and computations that appear in verification conditions.

// Allow builder method names that overlap with std traits - intentional DSL design
#![allow(clippy::should_implement_trait)]

use crate::VcType;
use serde::{Deserialize, Serialize};

/// An expression in the VC IR
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Expr {
    // Literals
    BoolLit(bool),
    IntLit(i128),
    FloatLit(f64),
    BitVecLit {
        bits: u32,
        value: Vec<u8>,
    },

    // Variables
    Var(String),
    /// Old value (for postconditions): old(x)
    Old(Box<Expr>),
    /// Return value in postconditions
    Result,

    // Arithmetic
    Neg(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Rem(Box<Expr>, Box<Expr>),

    // Bitwise
    BitAnd(Box<Expr>, Box<Expr>),
    BitOr(Box<Expr>, Box<Expr>),
    BitXor(Box<Expr>, Box<Expr>),
    BitNot(Box<Expr>),
    Shl(Box<Expr>, Box<Expr>),
    Shr(Box<Expr>, Box<Expr>),

    // Comparisons
    Eq(Box<Expr>, Box<Expr>),
    Ne(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    Ge(Box<Expr>, Box<Expr>),

    // Logical (bool-returning)
    Not(Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),

    // Conditional
    Ite {
        cond: Box<Expr>,
        then_: Box<Expr>,
        else_: Box<Expr>,
    },

    // Collections
    ArrayIndex(Box<Expr>, Box<Expr>),
    ArrayLen(Box<Expr>),
    ArraySlice {
        array: Box<Expr>,
        start: Box<Expr>,
        end: Box<Expr>,
    },
    TupleField(Box<Expr>, usize),
    StructField(Box<Expr>, String),

    // Function application (for uninterpreted functions and specs)
    Apply {
        func: String,
        args: Vec<Expr>,
    },

    // Quantified expressions (return bool)
    Forall {
        vars: Vec<(String, VcType)>,
        body: Box<Expr>,
    },
    Exists {
        vars: Vec<(String, VcType)>,
        body: Box<Expr>,
    },

    // Cast between types
    Cast {
        expr: Box<Expr>,
        to: VcType,
    },

    // Memory operations
    Deref(Box<Expr>),
    AddrOf(Box<Expr>),

    // Tensor operations (for neural network verification)
    TensorIndex {
        tensor: Box<Expr>,
        indices: Vec<Expr>,
    },
    TensorShape(Box<Expr>),
    TensorReshape {
        tensor: Box<Expr>,
        shape: Vec<usize>,
    },

    // Special functions commonly used in specs
    Abs(Box<Expr>),
    Min(Box<Expr>, Box<Expr>),
    Max(Box<Expr>, Box<Expr>),

    // Sequence/collection predicates
    Contains {
        collection: Box<Expr>,
        element: Box<Expr>,
    },
    Permutation(Box<Expr>, Box<Expr>),
    Sorted(Box<Expr>),

    /// Raw SMT-LIB expression string
    ///
    /// Used for programmatically generated expressions (e.g., from tactic execution)
    /// where constructing the full AST is impractical. The string is passed
    /// directly to the SMT backend.
    Raw(String),

    // Enum operations (Phase N3.1c)
    /// Test if an enum value is a specific variant
    ///
    /// # Arguments
    /// * `expr` - The enum value to test
    /// * `enum_type` - The enum type name (e.g., "Option", "Result", "MyEnum")
    /// * `variant` - The variant name to test for (e.g., "Some", "None", "Ok", "Err")
    ///
    /// # Examples
    /// - `matches!(opt, Some(_))` → `IsVariant { expr: opt, enum_type: "Option", variant: "Some" }`
    /// - `result.is_ok()` → `IsVariant { expr: result, enum_type: "Result", variant: "Ok" }`
    IsVariant {
        expr: Box<Expr>,
        enum_type: String,
        variant: String,
    },

    /// Get the discriminant (tag) of an enum value
    ///
    /// Returns an integer representing which variant the enum is.
    /// The mapping from variant to discriminant is type-specific.
    Discriminant(Box<Expr>),

    /// Extract the inner value from an enum variant
    ///
    /// # Arguments
    /// * `expr` - The enum value
    /// * `variant` - The variant to extract from (e.g., "Some", "Ok")
    /// * `field` - The field index (0 for simple variants like `Some(T)`)
    ///
    /// Assumes the value is already known to be the specified variant.
    /// This is typically guarded by an `IsVariant` check.
    VariantField {
        expr: Box<Expr>,
        variant: String,
        field: usize,
    },
}

impl Expr {
    // Builder methods for convenience

    pub fn var(name: impl Into<String>) -> Self {
        Self::Var(name.into())
    }

    #[must_use]
    pub const fn int(val: i128) -> Self {
        Self::IntLit(val)
    }

    #[must_use]
    pub const fn bool_(val: bool) -> Self {
        Self::BoolLit(val)
    }

    /// Create a raw SMT-LIB expression from a string
    pub fn raw(s: impl Into<String>) -> Self {
        Self::Raw(s.into())
    }

    #[must_use]
    pub fn add(self, other: Self) -> Self {
        Self::Add(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn sub(self, other: Self) -> Self {
        Self::Sub(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn mul(self, other: Self) -> Self {
        Self::Mul(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn eq(self, other: Self) -> Self {
        Self::Eq(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn lt(self, other: Self) -> Self {
        Self::Lt(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn le(self, other: Self) -> Self {
        Self::Le(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn gt(self, other: Self) -> Self {
        Self::Gt(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn ge(self, other: Self) -> Self {
        Self::Ge(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn and(self, other: Self) -> Self {
        Self::And(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn or(self, other: Self) -> Self {
        Self::Or(Box::new(self), Box::new(other))
    }

    #[must_use]
    pub fn not(self) -> Self {
        Self::Not(Box::new(self))
    }

    #[must_use]
    pub fn implies(self, other: Self) -> Self {
        // a => b is equivalent to !a || b
        Self::Or(Box::new(Self::Not(Box::new(self))), Box::new(other))
    }

    #[must_use]
    pub fn old(self) -> Self {
        Self::Old(Box::new(self))
    }

    #[must_use]
    pub fn forall(vars: Vec<(String, VcType)>, body: Self) -> Self {
        Self::Forall {
            vars,
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

    // Enum operations (Phase N3.1c)

    /// Test if an enum value is a specific variant
    ///
    /// # Example
    /// ```ignore
    /// Expr::var("opt").is_variant("Option", "Some")  // matches!(opt, Some(_))
    /// ```
    #[must_use]
    pub fn is_variant(self, enum_type: impl Into<String>, variant: impl Into<String>) -> Self {
        Self::IsVariant {
            expr: Box::new(self),
            enum_type: enum_type.into(),
            variant: variant.into(),
        }
    }

    /// Convenience method for Option::is_some()
    #[must_use]
    pub fn is_some(self) -> Self {
        self.is_variant("Option", "Some")
    }

    /// Convenience method for Option::is_none()
    #[must_use]
    pub fn is_none(self) -> Self {
        self.is_variant("Option", "None")
    }

    /// Convenience method for Result::is_ok()
    #[must_use]
    pub fn is_ok(self) -> Self {
        self.is_variant("Result", "Ok")
    }

    /// Convenience method for Result::is_err()
    #[must_use]
    pub fn is_err(self) -> Self {
        self.is_variant("Result", "Err")
    }

    /// Get the discriminant of an enum value
    #[must_use]
    pub fn discriminant(self) -> Self {
        Self::Discriminant(Box::new(self))
    }

    /// Extract a field from an enum variant
    ///
    /// # Example
    /// ```ignore
    /// Expr::var("opt").variant_field("Some", 0)  // opt.unwrap() (when opt is Some)
    /// ```
    #[must_use]
    pub fn variant_field(self, variant: impl Into<String>, field: usize) -> Self {
        Self::VariantField {
            expr: Box::new(self),
            variant: variant.into(),
            field,
        }
    }

    /// Convenience method for Option::unwrap() (get inner value from Some)
    #[must_use]
    pub fn unwrap_some(self) -> Self {
        self.variant_field("Some", 0)
    }

    /// Convenience method for Result::unwrap() (get Ok value)
    #[must_use]
    pub fn unwrap_ok(self) -> Self {
        self.variant_field("Ok", 0)
    }

    /// Convenience method for Result::unwrap_err() (get Err value)
    #[must_use]
    pub fn unwrap_err(self) -> Self {
        self.variant_field("Err", 0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ExprPrec {
    Lowest = 0,
    Or = 1,
    And = 2,
    Cmp = 3,
    BitOr = 4,
    BitXor = 5,
    BitAnd = 6,
    Shift = 7,
    Add = 8,
    Mul = 9,
    Unary = 10,
    Postfix = 11,
    Atom = 12,
}

impl ExprPrec {
    const fn next_tighter(self) -> Self {
        match self {
            Self::Lowest => Self::Or,
            Self::Or => Self::And,
            Self::And => Self::Cmp,
            Self::Cmp => Self::BitOr,
            Self::BitOr => Self::BitXor,
            Self::BitXor => Self::BitAnd,
            Self::BitAnd => Self::Shift,
            Self::Shift => Self::Add,
            Self::Add => Self::Mul,
            Self::Mul => Self::Unary,
            Self::Unary => Self::Postfix,
            Self::Postfix | Self::Atom => Self::Atom,
        }
    }
}

const fn expr_prec(e: &Expr) -> ExprPrec {
    match e {
        Expr::Or(_, _) => ExprPrec::Or,
        Expr::And(_, _) => ExprPrec::And,
        Expr::Eq(_, _)
        | Expr::Ne(_, _)
        | Expr::Lt(_, _)
        | Expr::Le(_, _)
        | Expr::Gt(_, _)
        | Expr::Ge(_, _) => ExprPrec::Cmp,
        Expr::BitOr(_, _) => ExprPrec::BitOr,
        Expr::BitXor(_, _) => ExprPrec::BitXor,
        Expr::BitAnd(_, _) => ExprPrec::BitAnd,
        Expr::Shl(_, _) | Expr::Shr(_, _) => ExprPrec::Shift,
        Expr::Add(_, _) | Expr::Sub(_, _) => ExprPrec::Add,
        Expr::Mul(_, _) | Expr::Div(_, _) | Expr::Rem(_, _) => ExprPrec::Mul,
        Expr::Neg(_)
        | Expr::Not(_)
        | Expr::BitNot(_)
        | Expr::Deref(_)
        | Expr::AddrOf(_)
        | Expr::Cast { .. } => ExprPrec::Unary,
        Expr::ArrayIndex(_, _)
        | Expr::ArrayLen(_)
        | Expr::ArraySlice { .. }
        | Expr::TupleField(_, _)
        | Expr::StructField(_, _)
        | Expr::Apply { .. }
        | Expr::TensorIndex { .. }
        | Expr::TensorShape(_)
        | Expr::TensorReshape { .. }
        | Expr::Abs(_)
        | Expr::Min(_, _)
        | Expr::Max(_, _)
        | Expr::Contains { .. }
        | Expr::Permutation(_, _)
        | Expr::Sorted(_)
        | Expr::Old(_)
        | Expr::IsVariant { .. }
        | Expr::Discriminant(_)
        | Expr::VariantField { .. } => ExprPrec::Postfix,
        Expr::BoolLit(_)
        | Expr::IntLit(_)
        | Expr::FloatLit(_)
        | Expr::BitVecLit { .. }
        | Expr::Var(_)
        | Expr::Result
        | Expr::Ite { .. }
        | Expr::Forall { .. }
        | Expr::Exists { .. }
        | Expr::Raw(_) => ExprPrec::Atom,
    }
}

fn fmt_expr(e: &Expr, parent_prec: ExprPrec, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let prec = expr_prec(e);
    let needs_parens = prec < parent_prec;
    if needs_parens {
        write!(f, "(")?;
    }

    match e {
        Expr::BoolLit(v) => write!(f, "{v}")?,
        Expr::IntLit(v) => write!(f, "{v}")?,
        Expr::FloatLit(v) => write!(f, "{v}")?,
        Expr::BitVecLit { bits, value } => {
            write!(f, "bv{bits}(0x")?;
            for b in value {
                write!(f, "{b:02x}")?;
            }
            write!(f, ")")?;
        }
        Expr::Var(name) => write!(f, "{name}")?,
        Expr::Old(inner) => {
            write!(f, "old(")?;
            fmt_expr(inner, ExprPrec::Lowest, f)?;
            write!(f, ")")?;
        }
        Expr::Result => write!(f, "result")?,

        Expr::Neg(inner) => {
            write!(f, "-")?;
            fmt_expr(inner, ExprPrec::Unary, f)?;
        }
        Expr::Not(inner) => {
            write!(f, "!")?;
            fmt_expr(inner, ExprPrec::Unary, f)?;
        }
        Expr::BitNot(inner) => {
            write!(f, "~")?;
            fmt_expr(inner, ExprPrec::Unary, f)?;
        }

        Expr::Add(a, b) => fmt_bin_op(a, "+", b, ExprPrec::Add, true, f)?,
        Expr::Sub(a, b) => fmt_bin_op(a, "-", b, ExprPrec::Add, false, f)?,
        Expr::Mul(a, b) => fmt_bin_op(a, "*", b, ExprPrec::Mul, true, f)?,
        Expr::Div(a, b) => fmt_bin_op(a, "/", b, ExprPrec::Mul, false, f)?,
        Expr::Rem(a, b) => fmt_bin_op(a, "%", b, ExprPrec::Mul, false, f)?,

        Expr::BitAnd(a, b) => fmt_bin_op(a, "&", b, ExprPrec::BitAnd, true, f)?,
        Expr::BitOr(a, b) => fmt_bin_op(a, "|", b, ExprPrec::BitOr, true, f)?,
        Expr::BitXor(a, b) => fmt_bin_op(a, "^", b, ExprPrec::BitXor, true, f)?,
        Expr::Shl(a, b) => fmt_bin_op(a, "<<", b, ExprPrec::Shift, false, f)?,
        Expr::Shr(a, b) => fmt_bin_op(a, ">>", b, ExprPrec::Shift, false, f)?,

        Expr::Eq(a, b) => fmt_bin_op(a, "==", b, ExprPrec::Cmp, false, f)?,
        Expr::Ne(a, b) => fmt_bin_op(a, "!=", b, ExprPrec::Cmp, false, f)?,
        Expr::Lt(a, b) => fmt_bin_op(a, "<", b, ExprPrec::Cmp, false, f)?,
        Expr::Le(a, b) => fmt_bin_op(a, "<=", b, ExprPrec::Cmp, false, f)?,
        Expr::Gt(a, b) => fmt_bin_op(a, ">", b, ExprPrec::Cmp, false, f)?,
        Expr::Ge(a, b) => fmt_bin_op(a, ">=", b, ExprPrec::Cmp, false, f)?,

        Expr::And(a, b) => fmt_bin_op(a, "&&", b, ExprPrec::And, true, f)?,
        Expr::Or(a, b) => fmt_bin_op(a, "||", b, ExprPrec::Or, true, f)?,

        Expr::Ite { cond, then_, else_ } => {
            write!(f, "if ")?;
            fmt_expr(cond, ExprPrec::Lowest, f)?;
            write!(f, " {{ ")?;
            fmt_expr(then_, ExprPrec::Lowest, f)?;
            write!(f, " }} else {{ ")?;
            fmt_expr(else_, ExprPrec::Lowest, f)?;
            write!(f, " }}")?;
        }

        Expr::ArrayIndex(array, index) => {
            fmt_expr(array, ExprPrec::Postfix, f)?;
            write!(f, "[")?;
            fmt_expr(index, ExprPrec::Lowest, f)?;
            write!(f, "]")?;
        }
        Expr::ArrayLen(array) => {
            fmt_expr(array, ExprPrec::Postfix, f)?;
            write!(f, ".len()")?;
        }
        Expr::ArraySlice { array, start, end } => {
            fmt_expr(array, ExprPrec::Postfix, f)?;
            write!(f, "[")?;
            fmt_expr(start, ExprPrec::Lowest, f)?;
            write!(f, "..")?;
            fmt_expr(end, ExprPrec::Lowest, f)?;
            write!(f, "]")?;
        }
        Expr::TupleField(base, idx) => {
            fmt_expr(base, ExprPrec::Postfix, f)?;
            write!(f, ".{idx}")?;
        }
        Expr::StructField(base, field) => {
            fmt_expr(base, ExprPrec::Postfix, f)?;
            write!(f, ".{field}")?;
        }

        Expr::Apply { func, args } => {
            write!(f, "{func}(")?;
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                fmt_expr(arg, ExprPrec::Lowest, f)?;
            }
            write!(f, ")")?;
        }

        Expr::Forall { vars, body } => {
            write!(f, "forall ")?;
            fmt_vars(vars, f)?;
            write!(f, ". ")?;
            fmt_expr(body, ExprPrec::Lowest, f)?;
        }
        Expr::Exists { vars, body } => {
            write!(f, "exists ")?;
            fmt_vars(vars, f)?;
            write!(f, ". ")?;
            fmt_expr(body, ExprPrec::Lowest, f)?;
        }

        Expr::Cast { expr, to } => {
            fmt_expr(expr, ExprPrec::Unary, f)?;
            write!(f, " as {to}")?;
        }

        Expr::Deref(inner) => {
            write!(f, "*")?;
            fmt_expr(inner, ExprPrec::Unary, f)?;
        }
        Expr::AddrOf(inner) => {
            write!(f, "&")?;
            fmt_expr(inner, ExprPrec::Unary, f)?;
        }

        Expr::TensorIndex { tensor, indices } => {
            fmt_expr(tensor, ExprPrec::Postfix, f)?;
            write!(f, "[")?;
            for (i, idx) in indices.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                fmt_expr(idx, ExprPrec::Lowest, f)?;
            }
            write!(f, "]")?;
        }
        Expr::TensorShape(tensor) => {
            fmt_expr(tensor, ExprPrec::Postfix, f)?;
            write!(f, ".shape()")?;
        }
        Expr::TensorReshape { tensor, shape } => {
            write!(f, "reshape(")?;
            fmt_expr(tensor, ExprPrec::Lowest, f)?;
            write!(f, ", [")?;
            for (i, dim) in shape.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{dim}")?;
            }
            write!(f, "])")?;
        }

        Expr::Abs(x) => {
            write!(f, "abs(")?;
            fmt_expr(x, ExprPrec::Lowest, f)?;
            write!(f, ")")?;
        }
        Expr::Min(a, b) => {
            write!(f, "min(")?;
            fmt_expr(a, ExprPrec::Lowest, f)?;
            write!(f, ", ")?;
            fmt_expr(b, ExprPrec::Lowest, f)?;
            write!(f, ")")?;
        }
        Expr::Max(a, b) => {
            write!(f, "max(")?;
            fmt_expr(a, ExprPrec::Lowest, f)?;
            write!(f, ", ")?;
            fmt_expr(b, ExprPrec::Lowest, f)?;
            write!(f, ")")?;
        }

        Expr::Contains {
            collection,
            element,
        } => {
            write!(f, "contains(")?;
            fmt_expr(collection, ExprPrec::Lowest, f)?;
            write!(f, ", ")?;
            fmt_expr(element, ExprPrec::Lowest, f)?;
            write!(f, ")")?;
        }
        Expr::Permutation(a, b) => {
            write!(f, "permutation(")?;
            fmt_expr(a, ExprPrec::Lowest, f)?;
            write!(f, ", ")?;
            fmt_expr(b, ExprPrec::Lowest, f)?;
            write!(f, ")")?;
        }
        Expr::Sorted(x) => {
            write!(f, "sorted(")?;
            fmt_expr(x, ExprPrec::Lowest, f)?;
            write!(f, ")")?;
        }

        Expr::Raw(s) => write!(f, "{s}")?,

        // Enum operations (Phase N3.1c)
        Expr::IsVariant {
            expr,
            enum_type,
            variant,
        } => {
            // Display as Rust-like syntax: matches!(expr, Variant(_)) or expr.is_some()
            match (enum_type.as_str(), variant.as_str()) {
                ("Option", "Some") => {
                    fmt_expr(expr, ExprPrec::Postfix, f)?;
                    write!(f, ".is_some()")?;
                }
                ("Option", "None") => {
                    fmt_expr(expr, ExprPrec::Postfix, f)?;
                    write!(f, ".is_none()")?;
                }
                ("Result", "Ok") => {
                    fmt_expr(expr, ExprPrec::Postfix, f)?;
                    write!(f, ".is_ok()")?;
                }
                ("Result", "Err") => {
                    fmt_expr(expr, ExprPrec::Postfix, f)?;
                    write!(f, ".is_err()")?;
                }
                _ => {
                    write!(f, "matches!(")?;
                    fmt_expr(expr, ExprPrec::Lowest, f)?;
                    write!(f, ", {enum_type}::{variant}(_))")?;
                }
            }
        }
        Expr::Discriminant(expr) => {
            write!(f, "discriminant(")?;
            fmt_expr(expr, ExprPrec::Lowest, f)?;
            write!(f, ")")?;
        }
        Expr::VariantField {
            expr,
            variant,
            field,
        } => {
            // Display as field access: expr.variant_field(0) or expr.unwrap()
            match (variant.as_str(), *field) {
                ("Some", 0) => {
                    fmt_expr(expr, ExprPrec::Postfix, f)?;
                    write!(f, ".unwrap()")?;
                }
                ("Ok", 0) => {
                    fmt_expr(expr, ExprPrec::Postfix, f)?;
                    write!(f, ".unwrap()")?;
                }
                ("Err", 0) => {
                    fmt_expr(expr, ExprPrec::Postfix, f)?;
                    write!(f, ".unwrap_err()")?;
                }
                _ => {
                    fmt_expr(expr, ExprPrec::Postfix, f)?;
                    write!(f, ".{variant}.{field}")?;
                }
            }
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

fn fmt_bin_op(
    a: &Expr,
    op: &str,
    b: &Expr,
    prec: ExprPrec,
    associative: bool,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    fmt_expr(a, prec, f)?;
    write!(f, " {op} ")?;

    let b_prec = expr_prec(b);
    let b_parent_prec = if associative {
        prec
    } else {
        prec.next_tighter()
    };
    // Need parens if: (1) right operand has lower precedence, or
    // (2) operator is non-associative and right operand has same precedence
    let needs_parens = b_prec < b_parent_prec || (!associative && b_prec == prec);
    if needs_parens {
        write!(f, "(")?;
        fmt_expr(b, ExprPrec::Lowest, f)?;
        write!(f, ")")?;
    } else {
        fmt_expr(b, b_parent_prec, f)?;
    }
    Ok(())
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_expr(self, ExprPrec::Lowest, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_literals() {
        let int_lit = Expr::int(42);
        assert!(matches!(int_lit, Expr::IntLit(42)));

        let bool_lit = Expr::bool_(true);
        assert!(matches!(bool_lit, Expr::BoolLit(true)));

        let float_lit = Expr::FloatLit(2.5);
        assert!(matches!(float_lit, Expr::FloatLit(f) if (f - 2.5).abs() < 0.001));
    }

    #[test]
    fn test_variables() {
        let x = Expr::var("x");
        assert!(matches!(x, Expr::Var(ref name) if name == "x"));

        let y = Expr::var(String::from("long_variable_name"));
        assert!(matches!(y, Expr::Var(ref name) if name == "long_variable_name"));
    }

    #[test]
    fn test_arithmetic_builders() {
        let x = Expr::var("x");
        let y = Expr::var("y");

        // x + y
        let add = x.clone().add(y.clone());
        assert!(matches!(add, Expr::Add(_, _)));

        // x - y
        let sub = x.clone().sub(y.clone());
        assert!(matches!(sub, Expr::Sub(_, _)));

        // x * y
        let mul = x.clone().mul(y.clone());
        assert!(matches!(mul, Expr::Mul(_, _)));
    }

    #[test]
    fn test_comparison_builders() {
        let x = Expr::var("x");
        let zero = Expr::int(0);

        let eq = x.clone().eq(zero.clone());
        assert!(matches!(eq, Expr::Eq(_, _)));

        let lt = x.clone().lt(zero.clone());
        assert!(matches!(lt, Expr::Lt(_, _)));

        let le = x.clone().le(zero.clone());
        assert!(matches!(le, Expr::Le(_, _)));

        let gt = x.clone().gt(zero.clone());
        assert!(matches!(gt, Expr::Gt(_, _)));

        let ge = x.clone().ge(zero.clone());
        assert!(matches!(ge, Expr::Ge(_, _)));
    }

    #[test]
    fn test_logical_builders() {
        let a = Expr::bool_(true);
        let b = Expr::bool_(false);

        let and = a.clone().and(b.clone());
        assert!(matches!(and, Expr::And(_, _)));

        let or = a.clone().or(b.clone());
        assert!(matches!(or, Expr::Or(_, _)));

        let not = a.clone().not();
        assert!(matches!(not, Expr::Not(_)));

        // implies: a => b is !a || b
        let imp = a.clone().implies(b.clone());
        assert!(matches!(imp, Expr::Or(_, _)));
    }

    #[test]
    fn test_old_expression() {
        let x = Expr::var("x");
        let old_x = x.old();
        assert!(matches!(old_x, Expr::Old(_)));

        // Check that we can unwrap it
        if let Expr::Old(inner) = old_x {
            assert!(matches!(*inner, Expr::Var(ref name) if name == "x"));
        }
    }

    #[test]
    fn test_result_expression() {
        let result = Expr::Result;
        assert!(matches!(result, Expr::Result));
    }

    #[test]
    fn test_quantified_expressions() {
        let body = Expr::var("x").gt(Expr::int(0));
        let forall = Expr::forall(
            vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body.clone(),
        );
        assert!(matches!(forall, Expr::Forall { .. }));

        let exists = Expr::exists(
            vec![(
                "y".to_string(),
                VcType::Int {
                    signed: false,
                    bits: 64,
                },
            )],
            body,
        );
        assert!(matches!(exists, Expr::Exists { .. }));
    }

    #[test]
    fn test_complex_expression_tree() {
        // (x + 1) * (y - 2) > 0
        let x = Expr::var("x");
        let y = Expr::var("y");
        let one = Expr::int(1);
        let two = Expr::int(2);
        let zero = Expr::int(0);

        let expr = x.add(one).mul(y.sub(two)).gt(zero);
        assert!(matches!(expr, Expr::Gt(_, _)));
    }

    #[test]
    fn test_array_operations() {
        let arr = Expr::var("arr");
        let idx = Expr::int(0);

        let index = Expr::ArrayIndex(Box::new(arr.clone()), Box::new(idx));
        assert!(matches!(index, Expr::ArrayIndex(_, _)));

        let len = Expr::ArrayLen(Box::new(arr.clone()));
        assert!(matches!(len, Expr::ArrayLen(_)));

        let slice = Expr::ArraySlice {
            array: Box::new(arr),
            start: Box::new(Expr::int(0)),
            end: Box::new(Expr::int(10)),
        };
        assert!(matches!(slice, Expr::ArraySlice { .. }));
    }

    #[test]
    fn test_struct_and_tuple_access() {
        let s = Expr::var("my_struct");

        let field = Expr::StructField(Box::new(s.clone()), "name".to_string());
        assert!(matches!(field, Expr::StructField(_, ref name) if name == "name"));

        let tuple = Expr::var("my_tuple");
        let elem = Expr::TupleField(Box::new(tuple), 0);
        assert!(matches!(elem, Expr::TupleField(_, 0)));
    }

    #[test]
    fn test_function_application() {
        let apply = Expr::Apply {
            func: "sqrt".to_string(),
            args: vec![Expr::var("x")],
        };
        assert!(matches!(apply, Expr::Apply { ref func, .. } if func == "sqrt"));
    }

    #[test]
    fn test_special_functions() {
        let x = Expr::var("x");
        let abs = Expr::Abs(Box::new(x.clone()));
        assert!(matches!(abs, Expr::Abs(_)));

        let min = Expr::Min(Box::new(x.clone()), Box::new(Expr::int(10)));
        assert!(matches!(min, Expr::Min(_, _)));

        let max = Expr::Max(Box::new(x.clone()), Box::new(Expr::int(0)));
        assert!(matches!(max, Expr::Max(_, _)));
    }

    #[test]
    fn test_collection_predicates() {
        let arr = Expr::var("arr");
        let elem = Expr::int(5);

        let contains = Expr::Contains {
            collection: Box::new(arr.clone()),
            element: Box::new(elem),
        };
        assert!(matches!(contains, Expr::Contains { .. }));

        let sorted = Expr::Sorted(Box::new(arr.clone()));
        assert!(matches!(sorted, Expr::Sorted(_)));

        let arr2 = Expr::var("arr2");
        let perm = Expr::Permutation(Box::new(arr.clone()), Box::new(arr2));
        assert!(matches!(perm, Expr::Permutation(_, _)));
    }

    #[test]
    fn test_bitwise_operations() {
        let a = Expr::var("a");
        let b = Expr::var("b");

        assert!(matches!(
            Expr::BitAnd(Box::new(a.clone()), Box::new(b.clone())),
            Expr::BitAnd(_, _)
        ));
        assert!(matches!(
            Expr::BitOr(Box::new(a.clone()), Box::new(b.clone())),
            Expr::BitOr(_, _)
        ));
        assert!(matches!(
            Expr::BitXor(Box::new(a.clone()), Box::new(b.clone())),
            Expr::BitXor(_, _)
        ));
        assert!(matches!(Expr::BitNot(Box::new(a.clone())), Expr::BitNot(_)));
        assert!(matches!(
            Expr::Shl(Box::new(a.clone()), Box::new(Expr::int(2))),
            Expr::Shl(_, _)
        ));
        assert!(matches!(
            Expr::Shr(Box::new(a.clone()), Box::new(Expr::int(2))),
            Expr::Shr(_, _)
        ));
    }

    #[test]
    fn test_memory_operations() {
        let ptr = Expr::var("ptr");

        let deref = Expr::Deref(Box::new(ptr.clone()));
        assert!(matches!(deref, Expr::Deref(_)));

        let addr = Expr::AddrOf(Box::new(Expr::var("x")));
        assert!(matches!(addr, Expr::AddrOf(_)));
    }

    #[test]
    fn test_tensor_operations() {
        let tensor = Expr::var("tensor");

        let idx = Expr::TensorIndex {
            tensor: Box::new(tensor.clone()),
            indices: vec![Expr::int(0), Expr::int(1)],
        };
        assert!(matches!(idx, Expr::TensorIndex { .. }));

        let shape = Expr::TensorShape(Box::new(tensor.clone()));
        assert!(matches!(shape, Expr::TensorShape(_)));

        let reshape = Expr::TensorReshape {
            tensor: Box::new(tensor),
            shape: vec![3, 4],
        };
        assert!(matches!(reshape, Expr::TensorReshape { ref shape, .. } if *shape == vec![3, 4]));
    }

    #[test]
    fn test_cast() {
        let x = Expr::var("x");
        let cast = Expr::Cast {
            expr: Box::new(x),
            to: VcType::Float { bits: 64 },
        };
        assert!(matches!(cast, Expr::Cast { .. }));
    }

    #[test]
    fn test_if_then_else() {
        let cond = Expr::var("cond");
        let then_ = Expr::int(1);
        let else_ = Expr::int(0);

        let ite = Expr::Ite {
            cond: Box::new(cond),
            then_: Box::new(then_),
            else_: Box::new(else_),
        };
        assert!(matches!(ite, Expr::Ite { .. }));
    }

    #[test]
    fn test_bitvec_literal() {
        let bv = Expr::BitVecLit {
            bits: 8,
            value: vec![0xFF],
        };
        assert!(matches!(bv, Expr::BitVecLit { bits: 8, .. }));
    }

    #[test]
    fn test_negation() {
        let x = Expr::var("x");
        let neg = Expr::Neg(Box::new(x));
        assert!(matches!(neg, Expr::Neg(_)));
    }

    #[test]
    fn test_div_rem() {
        let x = Expr::var("x");
        let y = Expr::var("y");

        let div = Expr::Div(Box::new(x.clone()), Box::new(y.clone()));
        assert!(matches!(div, Expr::Div(_, _)));

        let rem = Expr::Rem(Box::new(x), Box::new(y));
        assert!(matches!(rem, Expr::Rem(_, _)));
    }

    #[test]
    fn test_serialization() {
        // Test that expressions can be serialized/deserialized (serde derive)
        let expr = Expr::var("x").add(Expr::int(1));
        let json = serde_json::to_string(&expr).expect("serialize");
        let parsed: Expr = serde_json::from_str(&json).expect("deserialize");

        // Verify structure is preserved
        assert!(matches!(parsed, Expr::Add(_, _)));
    }

    #[test]
    fn test_display_basic() {
        let e = Expr::var("age").gt(Expr::int(18));
        assert_eq!(e.to_string(), "age > 18");

        let e = Expr::var("a").and(Expr::var("b")).or(Expr::var("c"));
        assert_eq!(e.to_string(), "a && b || c");

        let e = Expr::var("result").add(Expr::int(1)).mul(Expr::int(2));
        assert_eq!(e.to_string(), "(result + 1) * 2");
    }

    // Phase N3.1c: Enum operation tests

    #[test]
    fn test_is_variant_builder() {
        let opt = Expr::var("opt");

        // Test is_variant builder
        let is_some = opt.clone().is_variant("Option", "Some");
        assert!(matches!(
            is_some,
            Expr::IsVariant {
                ref enum_type,
                ref variant,
                ..
            } if enum_type == "Option" && variant == "Some"
        ));

        // Test convenience methods
        let is_some2 = Expr::var("opt").is_some();
        assert!(matches!(
            is_some2,
            Expr::IsVariant {
                ref enum_type,
                ref variant,
                ..
            } if enum_type == "Option" && variant == "Some"
        ));

        let is_none = Expr::var("opt").is_none();
        assert!(matches!(
            is_none,
            Expr::IsVariant {
                ref enum_type,
                ref variant,
                ..
            } if enum_type == "Option" && variant == "None"
        ));

        let is_ok = Expr::var("res").is_ok();
        assert!(matches!(
            is_ok,
            Expr::IsVariant {
                ref enum_type,
                ref variant,
                ..
            } if enum_type == "Result" && variant == "Ok"
        ));

        let is_err = Expr::var("res").is_err();
        assert!(matches!(
            is_err,
            Expr::IsVariant {
                ref enum_type,
                ref variant,
                ..
            } if enum_type == "Result" && variant == "Err"
        ));
    }

    #[test]
    fn test_discriminant_builder() {
        let e = Expr::var("my_enum").discriminant();
        assert!(matches!(e, Expr::Discriminant(_)));
    }

    #[test]
    fn test_variant_field_builder() {
        // Generic variant field
        let field = Expr::var("data").variant_field("Variant", 0);
        assert!(matches!(
            field,
            Expr::VariantField {
                ref variant,
                field: 0,
                ..
            } if variant == "Variant"
        ));

        // Convenience methods
        let unwrap_some = Expr::var("opt").unwrap_some();
        assert!(matches!(
            unwrap_some,
            Expr::VariantField {
                ref variant,
                field: 0,
                ..
            } if variant == "Some"
        ));

        let unwrap_ok = Expr::var("res").unwrap_ok();
        assert!(matches!(
            unwrap_ok,
            Expr::VariantField {
                ref variant,
                field: 0,
                ..
            } if variant == "Ok"
        ));

        let unwrap_err = Expr::var("res").unwrap_err();
        assert!(matches!(
            unwrap_err,
            Expr::VariantField {
                ref variant,
                field: 0,
                ..
            } if variant == "Err"
        ));
    }

    #[test]
    fn test_enum_display() {
        // Option variants display
        assert_eq!(Expr::var("opt").is_some().to_string(), "opt.is_some()");
        assert_eq!(Expr::var("opt").is_none().to_string(), "opt.is_none()");

        // Result variants display
        assert_eq!(Expr::var("res").is_ok().to_string(), "res.is_ok()");
        assert_eq!(Expr::var("res").is_err().to_string(), "res.is_err()");

        // Generic enum display
        let custom = Expr::var("val").is_variant("MyEnum", "Active");
        assert_eq!(custom.to_string(), "matches!(val, MyEnum::Active(_))");

        // Discriminant display
        assert_eq!(Expr::var("e").discriminant().to_string(), "discriminant(e)");

        // Variant field display
        assert_eq!(Expr::var("opt").unwrap_some().to_string(), "opt.unwrap()");
        assert_eq!(Expr::var("res").unwrap_ok().to_string(), "res.unwrap()");
        assert_eq!(
            Expr::var("res").unwrap_err().to_string(),
            "res.unwrap_err()"
        );

        // Generic variant field
        let custom_field = Expr::var("data").variant_field("Custom", 2);
        assert_eq!(custom_field.to_string(), "data.Custom.2");
    }

    #[test]
    fn test_enum_serialization() {
        // Test IsVariant serialization
        let is_some = Expr::var("opt").is_some();
        let json = serde_json::to_string(&is_some).expect("serialize");
        let parsed: Expr = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(parsed, Expr::IsVariant { .. }));

        // Test Discriminant serialization
        let disc = Expr::var("e").discriminant();
        let json = serde_json::to_string(&disc).expect("serialize");
        let parsed: Expr = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(parsed, Expr::Discriminant(_)));

        // Test VariantField serialization
        let field = Expr::var("opt").unwrap_some();
        let json = serde_json::to_string(&field).expect("serialize");
        let parsed: Expr = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(parsed, Expr::VariantField { .. }));
    }
}
