//! MIR to VC IR Encoder
//!
//! This module is responsible for encoding MIR constructs into the
//! verification condition intermediate representation.

use crate::{
    AggregateKind, BinOp, Constant, MirFunction, MirType, NullOp, Operand, Place, Projection,
    Rvalue, UnOp,
};
use vc_ir::{Expr, Predicate, VcType};

/// Encoder state for translating MIR to VC IR
pub struct MirEncoder {
    /// Map from local indices to their current SSA names
    local_versions: Vec<u32>,
}

impl MirEncoder {
    #[must_use]
    pub fn new(func: &MirFunction) -> Self {
        let num_locals = func.locals.len();
        Self {
            local_versions: vec![0; num_locals],
        }
    }

    /// Encode a MIR type to VC type
    #[allow(clippy::only_used_in_recursion)] // False positive: self is needed for method call
    #[must_use]
    pub fn encode_type(&self, ty: &MirType) -> VcType {
        match ty {
            MirType::Bool => VcType::Bool,
            MirType::Int { signed, bits } => VcType::Int {
                signed: *signed,
                bits: *bits,
            },
            MirType::Float { bits } => VcType::Float { bits: *bits },
            MirType::Ref { mutable, inner } => VcType::Ref {
                mutable: *mutable,
                inner: Box::new(self.encode_type(inner)),
            },
            MirType::Array { elem, len } => VcType::Array {
                elem: Box::new(self.encode_type(elem)),
                len: Some(*len),
            },
            MirType::Tuple(elems) => {
                VcType::Tuple(elems.iter().map(|t| self.encode_type(t)).collect())
            }
            MirType::Adt { name } => VcType::Struct {
                name: name.clone(),
                fields: vec![],
            },
            // Closure type - encoded as opaque struct with captured values
            MirType::Closure { def_id, captures } => VcType::Struct {
                name: format!("closure#{def_id}"),
                fields: captures
                    .iter()
                    .enumerate()
                    .map(|(i, t)| (format!("capture_{i}"), self.encode_type(t)))
                    .collect(),
            },
            // Function pointer type - encoded as opaque function type
            MirType::FnPtr { params, ret } => VcType::Struct {
                name: format!(
                    "fn_ptr({}) -> {:?}",
                    params
                        .iter()
                        .map(|t| format!("{:?}", self.encode_type(t)))
                        .collect::<Vec<_>>()
                        .join(", "),
                    self.encode_type(ret)
                ),
                fields: vec![],
            },
            // Named function reference
            MirType::FnDef { name } => VcType::Struct {
                name: format!("fn#{name}"),
                fields: vec![],
            },
        }
    }

    /// Encode a place (lvalue) to an expression
    #[must_use]
    pub fn encode_place(&self, place: &Place) -> Expr {
        let version = self.local_versions.get(place.local.0).copied().unwrap_or(0);
        let base_name = format!("_{}_{}", place.local.0, version);
        let mut expr = Expr::Var(base_name);

        for proj in &place.projections {
            expr = match proj {
                Projection::Deref => Expr::Deref(Box::new(expr)),
                Projection::Field(idx) => Expr::TupleField(Box::new(expr), *idx),
                Projection::Index(local) => {
                    let idx_version = self.local_versions.get(local.0).copied().unwrap_or(0);
                    let idx_expr = Expr::Var(format!("_{}_{}", local.0, idx_version));
                    Expr::ArrayIndex(Box::new(expr), Box::new(idx_expr))
                }
            };
        }

        expr
    }

    /// Encode an operand to an expression
    #[must_use]
    pub fn encode_operand(&self, op: &Operand) -> Expr {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.encode_place(place),
            Operand::Constant(c) => self.encode_constant(c),
        }
    }

    /// Encode a constant to an expression
    #[must_use]
    pub const fn encode_constant(&self, c: &Constant) -> Expr {
        match c {
            Constant::Bool(b) => Expr::BoolLit(*b),
            Constant::Int(i) => Expr::IntLit(*i),
            Constant::Float(f) => Expr::FloatLit(*f),
        }
    }

    /// Encode an rvalue to an expression
    #[must_use]
    pub fn encode_rvalue(&self, rv: &Rvalue) -> Expr {
        match rv {
            Rvalue::Use(op) => self.encode_operand(op),

            Rvalue::BinaryOp(binop, lhs, rhs) => self.encode_binop(*binop, lhs, rhs),

            Rvalue::UnaryOp(unop, operand) => {
                let e = Box::new(self.encode_operand(operand));
                match unop {
                    UnOp::Not => Expr::Not(e),
                    UnOp::Neg => Expr::Neg(e),
                }
            }

            Rvalue::Ref { place, .. } => Expr::AddrOf(Box::new(self.encode_place(place))),

            Rvalue::Aggregate { kind, operands } => self.encode_aggregate(kind, operands),

            Rvalue::Len(place) => Expr::ArrayLen(Box::new(self.encode_place(place))),

            Rvalue::Cast { operand, ty, .. } => Expr::Cast {
                expr: Box::new(self.encode_operand(operand)),
                to: self.encode_type(ty),
            },

            Rvalue::Discriminant(place) => {
                // Discriminant is encoded as a special field access
                Expr::StructField(
                    Box::new(self.encode_place(place)),
                    "discriminant".to_string(),
                )
            }

            Rvalue::Repeat { operand, count } => {
                // Encode as array construction with repeated value
                let elem = self.encode_operand(operand);
                Expr::Apply {
                    func: "array_repeat".to_string(),
                    args: vec![elem, Expr::IntLit(*count as i128)],
                }
            }

            Rvalue::CheckedBinaryOp(binop, lhs, rhs) => {
                // Checked ops return a tuple (result, overflow_flag)
                // For verification, we model this as just the result
                // The overflow check becomes a separate VC
                self.encode_binop(*binop, lhs, rhs)
            }

            Rvalue::NullaryOp(nullop, ty) => match nullop {
                NullOp::SizeOf => Expr::Apply {
                    func: "sizeof".to_string(),
                    args: vec![Expr::Var(format!("type_{ty:?}"))],
                },
                NullOp::AlignOf => Expr::Apply {
                    func: "alignof".to_string(),
                    args: vec![Expr::Var(format!("type_{ty:?}"))],
                },
            },
        }
    }

    /// Encode a binary operation
    fn encode_binop(&self, binop: BinOp, lhs: &Operand, rhs: &Operand) -> Expr {
        let l = Box::new(self.encode_operand(lhs));
        let r = Box::new(self.encode_operand(rhs));
        match binop {
            BinOp::Add => Expr::Add(l, r),
            BinOp::Sub => Expr::Sub(l, r),
            BinOp::Mul => Expr::Mul(l, r),
            BinOp::Div => Expr::Div(l, r),
            BinOp::Rem => Expr::Rem(l, r),
            BinOp::Eq => Expr::Eq(l, r),
            BinOp::Ne => Expr::Ne(l, r),
            BinOp::Lt => Expr::Lt(l, r),
            BinOp::Le => Expr::Le(l, r),
            BinOp::Gt => Expr::Gt(l, r),
            BinOp::Ge => Expr::Ge(l, r),
            BinOp::BitAnd => Expr::BitAnd(l, r),
            BinOp::BitOr => Expr::BitOr(l, r),
            BinOp::BitXor => Expr::BitXor(l, r),
            BinOp::Shl => Expr::Shl(l, r),
            BinOp::Shr => Expr::Shr(l, r),
        }
    }

    /// Encode an aggregate construction
    fn encode_aggregate(&self, kind: &AggregateKind, operands: &[Operand]) -> Expr {
        let encoded_ops: Vec<Expr> = operands.iter().map(|op| self.encode_operand(op)).collect();

        match kind {
            AggregateKind::Array(_elem_ty) => {
                // Array literal as function application
                Expr::Apply {
                    func: "array".to_string(),
                    args: encoded_ops,
                }
            }
            AggregateKind::Tuple => {
                // Tuple as function application
                Expr::Apply {
                    func: "tuple".to_string(),
                    args: encoded_ops,
                }
            }
            AggregateKind::Adt { name, variant } => {
                // ADT construction
                let func_name = if let Some(v) = variant {
                    format!("{name}::variant_{v}")
                } else {
                    format!("{name}::new")
                };
                Expr::Apply {
                    func: func_name,
                    args: encoded_ops,
                }
            }
            AggregateKind::Closure { def_id } => {
                // Closure construction - captures as arguments
                Expr::Apply {
                    func: format!("closure#{def_id}"),
                    args: encoded_ops,
                }
            }
            AggregateKind::Coroutine { def_id } => {
                // Coroutine/generator construction
                Expr::Apply {
                    func: format!("coroutine#{def_id}"),
                    args: encoded_ops,
                }
            }
        }
    }

    /// Update local version for SSA assignment
    pub fn bump_local_version(&mut self, local: usize) -> u32 {
        if local < self.local_versions.len() {
            self.local_versions[local] += 1;
            self.local_versions[local]
        } else {
            0
        }
    }

    /// Get current version of a local
    #[must_use]
    pub fn local_version(&self, local: usize) -> u32 {
        self.local_versions.get(local).copied().unwrap_or(0)
    }
}

/// Encode a predicate with substitutions applied
#[must_use]
pub fn substitute(pred: &Predicate, var: &str, expr: &Expr) -> Predicate {
    match pred {
        Predicate::Bool(b) => Predicate::Bool(*b),
        Predicate::Expr(e) => Predicate::Expr(substitute_expr(e, var, expr)),
        Predicate::Not(p) => Predicate::Not(Box::new(substitute(p, var, expr))),
        Predicate::And(preds) => {
            Predicate::And(preds.iter().map(|p| substitute(p, var, expr)).collect())
        }
        Predicate::Or(preds) => {
            Predicate::Or(preds.iter().map(|p| substitute(p, var, expr)).collect())
        }
        Predicate::Implies(a, b) => Predicate::Implies(
            Box::new(substitute(a, var, expr)),
            Box::new(substitute(b, var, expr)),
        ),
        Predicate::Forall {
            vars,
            triggers,
            body,
        } => {
            // Don't substitute if var is bound
            if vars.iter().any(|(n, _)| n == var) {
                pred.clone()
            } else {
                Predicate::Forall {
                    vars: vars.clone(),
                    triggers: triggers
                        .iter()
                        .map(|t| t.iter().map(|e| substitute_expr(e, var, expr)).collect())
                        .collect(),
                    body: Box::new(substitute(body, var, expr)),
                }
            }
        }
        Predicate::Iff(a, b) => Predicate::Iff(
            Box::new(substitute(a, var, expr)),
            Box::new(substitute(b, var, expr)),
        ),
        Predicate::Let { bindings, body } => {
            // Don't substitute in bindings that shadow var
            let new_bindings: Vec<_> = bindings
                .iter()
                .map(|(n, e)| (n.clone(), substitute_expr(e, var, expr)))
                .collect();
            let shadowed = bindings.iter().any(|(n, _)| n == var);
            Predicate::Let {
                bindings: new_bindings,
                body: if shadowed {
                    body.clone()
                } else {
                    Box::new(substitute(body, var, expr))
                },
            }
        }
        Predicate::Exists { vars, body } => {
            if vars.iter().any(|(n, _)| n == var) {
                pred.clone()
            } else {
                Predicate::Exists {
                    vars: vars.clone(),
                    body: Box::new(substitute(body, var, expr)),
                }
            }
        }
    }
}

/// Substitute a variable in an expression
fn substitute_expr(e: &Expr, var: &str, replacement: &Expr) -> Expr {
    match e {
        Expr::Var(name) if name == var => replacement.clone(),
        Expr::Var(_)
        | Expr::BoolLit(_)
        | Expr::IntLit(_)
        | Expr::FloatLit(_)
        | Expr::BitVecLit { .. }
        | Expr::Result => e.clone(),

        Expr::Old(inner) => Expr::Old(Box::new(substitute_expr(inner, var, replacement))),
        Expr::Neg(inner) => Expr::Neg(Box::new(substitute_expr(inner, var, replacement))),
        Expr::Not(inner) => Expr::Not(Box::new(substitute_expr(inner, var, replacement))),
        Expr::BitNot(inner) => Expr::BitNot(Box::new(substitute_expr(inner, var, replacement))),
        Expr::Deref(inner) => Expr::Deref(Box::new(substitute_expr(inner, var, replacement))),
        Expr::AddrOf(inner) => Expr::AddrOf(Box::new(substitute_expr(inner, var, replacement))),
        Expr::Abs(inner) => Expr::Abs(Box::new(substitute_expr(inner, var, replacement))),
        Expr::ArrayLen(inner) => Expr::ArrayLen(Box::new(substitute_expr(inner, var, replacement))),
        Expr::TensorShape(inner) => {
            Expr::TensorShape(Box::new(substitute_expr(inner, var, replacement)))
        }

        Expr::Add(l, r) => Expr::Add(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Sub(l, r) => Expr::Sub(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Mul(l, r) => Expr::Mul(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Div(l, r) => Expr::Div(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Rem(l, r) => Expr::Rem(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::BitAnd(l, r) => Expr::BitAnd(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::BitOr(l, r) => Expr::BitOr(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::BitXor(l, r) => Expr::BitXor(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Shl(l, r) => Expr::Shl(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Shr(l, r) => Expr::Shr(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Eq(l, r) => Expr::Eq(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Ne(l, r) => Expr::Ne(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Lt(l, r) => Expr::Lt(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Le(l, r) => Expr::Le(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Gt(l, r) => Expr::Gt(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Ge(l, r) => Expr::Ge(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::And(l, r) => Expr::And(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Or(l, r) => Expr::Or(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Min(l, r) => Expr::Min(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::Max(l, r) => Expr::Max(
            Box::new(substitute_expr(l, var, replacement)),
            Box::new(substitute_expr(r, var, replacement)),
        ),
        Expr::ArrayIndex(arr, idx) => Expr::ArrayIndex(
            Box::new(substitute_expr(arr, var, replacement)),
            Box::new(substitute_expr(idx, var, replacement)),
        ),
        Expr::Permutation(a, b) => Expr::Permutation(
            Box::new(substitute_expr(a, var, replacement)),
            Box::new(substitute_expr(b, var, replacement)),
        ),

        Expr::Ite { cond, then_, else_ } => Expr::Ite {
            cond: Box::new(substitute_expr(cond, var, replacement)),
            then_: Box::new(substitute_expr(then_, var, replacement)),
            else_: Box::new(substitute_expr(else_, var, replacement)),
        },

        Expr::ArraySlice { array, start, end } => Expr::ArraySlice {
            array: Box::new(substitute_expr(array, var, replacement)),
            start: Box::new(substitute_expr(start, var, replacement)),
            end: Box::new(substitute_expr(end, var, replacement)),
        },

        Expr::TupleField(inner, idx) => {
            Expr::TupleField(Box::new(substitute_expr(inner, var, replacement)), *idx)
        }
        Expr::StructField(inner, field) => Expr::StructField(
            Box::new(substitute_expr(inner, var, replacement)),
            field.clone(),
        ),

        Expr::Apply { func, args } => Expr::Apply {
            func: func.clone(),
            args: args
                .iter()
                .map(|a| substitute_expr(a, var, replacement))
                .collect(),
        },

        Expr::Forall { vars, body } => {
            if vars.iter().any(|(n, _)| n == var) {
                e.clone()
            } else {
                Expr::Forall {
                    vars: vars.clone(),
                    body: Box::new(substitute_expr(body, var, replacement)),
                }
            }
        }
        Expr::Exists { vars, body } => {
            if vars.iter().any(|(n, _)| n == var) {
                e.clone()
            } else {
                Expr::Exists {
                    vars: vars.clone(),
                    body: Box::new(substitute_expr(body, var, replacement)),
                }
            }
        }

        Expr::Cast { expr: inner, to } => Expr::Cast {
            expr: Box::new(substitute_expr(inner, var, replacement)),
            to: to.clone(),
        },

        Expr::TensorIndex { tensor, indices } => Expr::TensorIndex {
            tensor: Box::new(substitute_expr(tensor, var, replacement)),
            indices: indices
                .iter()
                .map(|i| substitute_expr(i, var, replacement))
                .collect(),
        },
        Expr::TensorReshape { tensor, shape } => Expr::TensorReshape {
            tensor: Box::new(substitute_expr(tensor, var, replacement)),
            shape: shape.clone(),
        },

        Expr::Contains {
            collection,
            element,
        } => Expr::Contains {
            collection: Box::new(substitute_expr(collection, var, replacement)),
            element: Box::new(substitute_expr(element, var, replacement)),
        },

        Expr::Sorted(inner) => Expr::Sorted(Box::new(substitute_expr(inner, var, replacement))),

        // For raw SMT-LIB strings, perform simple string substitution
        // We convert the replacement to a string representation
        Expr::Raw(s) => {
            let replacement_str = expr_to_smt_str(replacement);
            // Use word boundary substitution to avoid partial matches
            let pattern = format!(r"\b{}\b", regex::escape(var));
            if let Ok(re) = regex::Regex::new(&pattern) {
                Expr::Raw(re.replace_all(s, &replacement_str).to_string())
            } else {
                Expr::Raw(s.replace(var, &replacement_str))
            }
        }

        // Enum operations (Phase N3.1c)
        Expr::IsVariant {
            expr: inner,
            enum_type,
            variant,
        } => Expr::IsVariant {
            expr: Box::new(substitute_expr(inner, var, replacement)),
            enum_type: enum_type.clone(),
            variant: variant.clone(),
        },
        Expr::Discriminant(inner) => {
            Expr::Discriminant(Box::new(substitute_expr(inner, var, replacement)))
        }
        Expr::VariantField {
            expr: inner,
            variant,
            field,
        } => Expr::VariantField {
            expr: Box::new(substitute_expr(inner, var, replacement)),
            variant: variant.clone(),
            field: *field,
        },
    }
}

/// Convert an Expr to its SMT-LIB string representation (basic cases)
fn expr_to_smt_str(e: &Expr) -> String {
    match e {
        Expr::Var(name) => name.clone(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::IntLit(n) => n.to_string(),
        Expr::FloatLit(f) => f.to_string(),
        Expr::Result => "result".to_string(),
        Expr::Raw(s) => s.clone(),
        // For complex expressions, use Debug format as fallback
        _ => format!("{e:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        AggregateKind, CastKind, Constant, Local, LocalDecl, MirFunction, MirType, NullOp, Operand,
        Place, Projection, Rvalue,
    };
    use vc_ir::{Expr, SourceSpan};

    fn make_test_func(num_locals: usize) -> MirFunction {
        MirFunction {
            name: "test".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: (0..num_locals)
                .map(|i| LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some(format!("_{i}")),
                })
                .collect(),
            blocks: vec![],
            span: SourceSpan::default(),
        }
    }

    #[test]
    fn test_encode_array_aggregate() {
        let func = make_test_func(3);
        let encoder = MirEncoder::new(&func);

        let rv = Rvalue::Aggregate {
            kind: AggregateKind::Array(MirType::Int {
                signed: true,
                bits: 32,
            }),
            operands: vec![
                Operand::Constant(Constant::Int(1)),
                Operand::Constant(Constant::Int(2)),
                Operand::Constant(Constant::Int(3)),
            ],
        };

        let expr = encoder.encode_rvalue(&rv);

        match expr {
            Expr::Apply { func, args } => {
                assert_eq!(func, "array");
                assert_eq!(args.len(), 3);
                assert!(matches!(args[0], Expr::IntLit(1)));
                assert!(matches!(args[1], Expr::IntLit(2)));
                assert!(matches!(args[2], Expr::IntLit(3)));
            }
            _ => panic!("Expected Apply expression, got {expr:?}"),
        }
    }

    #[test]
    fn test_encode_tuple_aggregate() {
        let func = make_test_func(3);
        let encoder = MirEncoder::new(&func);

        let rv = Rvalue::Aggregate {
            kind: AggregateKind::Tuple,
            operands: vec![
                Operand::Constant(Constant::Int(42)),
                Operand::Constant(Constant::Bool(true)),
            ],
        };

        let expr = encoder.encode_rvalue(&rv);

        match expr {
            Expr::Apply { func, args } => {
                assert_eq!(func, "tuple");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected Apply expression"),
        }
    }

    #[test]
    fn test_encode_struct_aggregate() {
        let func = make_test_func(3);
        let encoder = MirEncoder::new(&func);

        let rv = Rvalue::Aggregate {
            kind: AggregateKind::Adt {
                name: "Point".to_string(),
                variant: None,
            },
            operands: vec![
                Operand::Constant(Constant::Int(10)),
                Operand::Constant(Constant::Int(20)),
            ],
        };

        let expr = encoder.encode_rvalue(&rv);

        match expr {
            Expr::Apply { func, args } => {
                assert_eq!(func, "Point::new");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected Apply expression"),
        }
    }

    #[test]
    fn test_encode_array_len() {
        let func = make_test_func(3);
        let encoder = MirEncoder::new(&func);

        let rv = Rvalue::Len(Place {
            local: Local(1),
            projections: vec![],
        });

        let expr = encoder.encode_rvalue(&rv);

        match expr {
            Expr::ArrayLen(inner) => match *inner {
                Expr::Var(name) => assert_eq!(name, "_1_0"),
                _ => panic!("Expected Var"),
            },
            _ => panic!("Expected ArrayLen"),
        }
    }

    #[test]
    fn test_encode_cast() {
        let func = make_test_func(3);
        let encoder = MirEncoder::new(&func);

        let rv = Rvalue::Cast {
            kind: CastKind::IntToInt,
            operand: Operand::Constant(Constant::Int(42)),
            ty: MirType::Int {
                signed: true,
                bits: 64,
            },
        };

        let expr = encoder.encode_rvalue(&rv);

        match expr {
            Expr::Cast { expr: inner, to } => {
                assert!(matches!(*inner, Expr::IntLit(42)));
                assert!(matches!(
                    to,
                    VcType::Int {
                        signed: true,
                        bits: 64
                    }
                ));
            }
            _ => panic!("Expected Cast"),
        }
    }

    #[test]
    fn test_encode_repeat() {
        let func = make_test_func(3);
        let encoder = MirEncoder::new(&func);

        let rv = Rvalue::Repeat {
            operand: Operand::Constant(Constant::Int(0)),
            count: 10,
        };

        let expr = encoder.encode_rvalue(&rv);

        match expr {
            Expr::Apply { func, args } => {
                assert_eq!(func, "array_repeat");
                assert_eq!(args.len(), 2);
                assert!(matches!(args[0], Expr::IntLit(0)));
                assert!(matches!(args[1], Expr::IntLit(10)));
            }
            _ => panic!("Expected Apply"),
        }
    }

    #[test]
    fn test_encode_discriminant() {
        let func = make_test_func(3);
        let encoder = MirEncoder::new(&func);

        let rv = Rvalue::Discriminant(Place {
            local: Local(1),
            projections: vec![],
        });

        let expr = encoder.encode_rvalue(&rv);

        match expr {
            Expr::StructField(inner, field) => {
                assert_eq!(field, "discriminant");
                match *inner {
                    Expr::Var(name) => assert_eq!(name, "_1_0"),
                    _ => panic!("Expected Var"),
                }
            }
            _ => panic!("Expected StructField"),
        }
    }

    #[test]
    fn test_encode_place_with_projections() {
        let func = make_test_func(3);
        let encoder = MirEncoder::new(&func);

        // Test field projection
        let place_field = Place {
            local: Local(1),
            projections: vec![Projection::Field(2)],
        };
        let expr_field = encoder.encode_place(&place_field);

        match expr_field {
            Expr::TupleField(inner, idx) => {
                assert_eq!(idx, 2);
                match *inner {
                    Expr::Var(name) => assert_eq!(name, "_1_0"),
                    _ => panic!("Expected Var"),
                }
            }
            _ => panic!("Expected TupleField"),
        }

        // Test deref projection
        let place_deref = Place {
            local: Local(1),
            projections: vec![Projection::Deref],
        };
        let expr_deref = encoder.encode_place(&place_deref);

        match expr_deref {
            Expr::Deref(inner) => match *inner {
                Expr::Var(name) => assert_eq!(name, "_1_0"),
                _ => panic!("Expected Var"),
            },
            _ => panic!("Expected Deref"),
        }

        // Test index projection
        let place_idx = Place {
            local: Local(1),
            projections: vec![Projection::Index(Local(2))],
        };
        let expr_idx = encoder.encode_place(&place_idx);

        match expr_idx {
            Expr::ArrayIndex(arr, idx) => {
                match *arr {
                    Expr::Var(name) => assert_eq!(name, "_1_0"),
                    _ => panic!("Expected Var for array"),
                }
                match *idx {
                    Expr::Var(name) => assert_eq!(name, "_2_0"),
                    _ => panic!("Expected Var for index"),
                }
            }
            _ => panic!("Expected ArrayIndex"),
        }
    }

    #[test]
    fn test_encode_sizeof() {
        let func = make_test_func(1);
        let encoder = MirEncoder::new(&func);

        let rv = Rvalue::NullaryOp(
            NullOp::SizeOf,
            MirType::Int {
                signed: true,
                bits: 32,
            },
        );
        let expr = encoder.encode_rvalue(&rv);

        match expr {
            Expr::Apply { func, .. } => {
                assert_eq!(func, "sizeof");
            }
            _ => panic!("Expected Apply"),
        }
    }

    #[test]
    fn test_encode_checked_binop() {
        let func = make_test_func(3);
        let encoder = MirEncoder::new(&func);

        let rv = Rvalue::CheckedBinaryOp(
            crate::BinOp::Add,
            Operand::Constant(Constant::Int(1)),
            Operand::Constant(Constant::Int(2)),
        );

        let expr = encoder.encode_rvalue(&rv);

        // CheckedBinaryOp should encode like a regular BinaryOp for verification
        match expr {
            Expr::Add(l, r) => {
                assert!(matches!(*l, Expr::IntLit(1)));
                assert!(matches!(*r, Expr::IntLit(2)));
            }
            _ => panic!("Expected Add"),
        }
    }
}
