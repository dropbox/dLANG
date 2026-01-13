//! Specification expression parser
//!
//! Parses tRust specification expressions, which are Rust expressions
//! extended with verification-specific constructs.

use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    token, BinOp, Expr, ExprBinary, ExprCall, ExprParen, ExprPath, ExprUnary, Ident, Result, Token,
    Type, UnOp,
};

/// A specification expression
#[derive(Debug, Clone)]
pub enum SpecExpr {
    /// A standard Rust expression
    Rust(Expr),

    /// Universal quantifier: forall |x: T| pred
    Forall {
        params: Vec<QuantParam>,
        body: Box<SpecExpr>,
    },

    /// Existential quantifier: exists |x: T| pred
    Exists {
        params: Vec<QuantParam>,
        body: Box<SpecExpr>,
    },

    /// Implication: a => b
    Implies {
        lhs: Box<SpecExpr>,
        rhs: Box<SpecExpr>,
    },

    /// Old value: old(expr)
    Old(Box<SpecExpr>),

    /// Binary operation with spec extensions
    BinOp {
        left: Box<SpecExpr>,
        op: SpecBinOp,
        right: Box<SpecExpr>,
    },

    /// Unary operation
    UnaryOp {
        op: SpecUnaryOp,
        operand: Box<SpecExpr>,
    },
}

/// Quantifier parameter
#[derive(Debug, Clone)]
pub struct QuantParam {
    pub name: Ident,
    pub ty: Type,
}

/// Binary operators in specs
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecBinOp {
    And,
    Or,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

/// Unary operators in specs
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecUnaryOp {
    Not,
    Neg,
}

impl Parse for SpecExpr {
    fn parse(input: ParseStream) -> Result<Self> {
        // First check for forall/exists quantifiers before syn takes over
        if input.peek(Ident) {
            let ident: Ident = input.fork().parse()?;
            let ident_str = ident.to_string();

            if ident_str == "forall" {
                input.parse::<Ident>()?;
                return parse_quantifier(input, true);
            }

            if ident_str == "exists" {
                input.parse::<Ident>()?;
                return parse_quantifier(input, false);
            }
        }

        // Use syn to parse the expression, then transform it
        let expr: Expr = input.parse()?;

        // Check if there's a => (implication) following
        // This handles: expr => expr
        if input.peek(Token![=]) && input.peek2(Token![>]) {
            input.parse::<Token![=]>()?;
            input.parse::<Token![>]>()?;
            let rhs = Self::parse(input)?;
            let lhs = transform_expr(expr);
            return Ok(Self::Implies {
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            });
        }

        Ok(transform_expr(expr))
    }
}

/// Transform a syn `Expr` into a `SpecExpr`
fn transform_expr(expr: Expr) -> SpecExpr {
    match expr {
        // Handle binary operators
        Expr::Binary(ExprBinary {
            left, op, right, ..
        }) => {
            if let Some(spec_op) = convert_binop(&op) {
                SpecExpr::BinOp {
                    left: Box::new(transform_expr(*left)),
                    op: spec_op,
                    right: Box::new(transform_expr(*right)),
                }
            } else {
                // Unknown binary op, keep as Rust
                SpecExpr::Rust(Expr::Binary(ExprBinary {
                    attrs: vec![],
                    left,
                    op,
                    right,
                }))
            }
        }

        // Handle unary operators
        Expr::Unary(ExprUnary { op, expr, .. }) => {
            if let Some(spec_op) = convert_unop(op) {
                SpecExpr::UnaryOp {
                    op: spec_op,
                    operand: Box::new(transform_expr(*expr)),
                }
            } else {
                SpecExpr::Rust(Expr::Unary(ExprUnary {
                    attrs: vec![],
                    op,
                    expr,
                }))
            }
        }

        // Handle old(expr) call
        Expr::Call(ExprCall { func, args, .. }) => {
            if let Expr::Path(ExprPath { path, .. }) = func.as_ref() {
                if path.is_ident("old") {
                    let mut iter = args.iter();
                    if let (Some(inner), None) = (iter.next(), iter.next()) {
                        return SpecExpr::Old(Box::new(transform_expr(inner.clone())));
                    }
                }
            }
            // Not old(), keep as Rust
            SpecExpr::Rust(Expr::Call(ExprCall {
                attrs: vec![],
                func,
                paren_token: token::Paren::default(),
                args,
            }))
        }

        // Handle parenthesized expressions
        Expr::Paren(ExprParen { expr, .. }) => transform_expr(*expr),

        // Handle closures - might be quantifier bodies
        Expr::Closure(closure) => {
            // For now, keep as Rust - quantifiers handled separately
            SpecExpr::Rust(Expr::Closure(closure))
        }

        // Everything else stays as Rust
        other => SpecExpr::Rust(other),
    }
}

const fn convert_binop(op: &BinOp) -> Option<SpecBinOp> {
    match op {
        BinOp::And(_) => Some(SpecBinOp::And),
        BinOp::Or(_) => Some(SpecBinOp::Or),
        BinOp::Eq(_) => Some(SpecBinOp::Eq),
        BinOp::Ne(_) => Some(SpecBinOp::Ne),
        BinOp::Lt(_) => Some(SpecBinOp::Lt),
        BinOp::Le(_) => Some(SpecBinOp::Le),
        BinOp::Gt(_) => Some(SpecBinOp::Gt),
        BinOp::Ge(_) => Some(SpecBinOp::Ge),
        BinOp::Add(_) => Some(SpecBinOp::Add),
        BinOp::Sub(_) => Some(SpecBinOp::Sub),
        BinOp::Mul(_) => Some(SpecBinOp::Mul),
        BinOp::Div(_) => Some(SpecBinOp::Div),
        BinOp::Rem(_) => Some(SpecBinOp::Rem),
        _ => None,
    }
}

const fn convert_unop(op: UnOp) -> Option<SpecUnaryOp> {
    match op {
        UnOp::Not(_) => Some(SpecUnaryOp::Not),
        UnOp::Neg(_) => Some(SpecUnaryOp::Neg),
        _ => None,
    }
}

/// Parse quantifier parameters and body
fn parse_quantifier(input: ParseStream, is_forall: bool) -> Result<SpecExpr> {
    // Parse closure-like syntax: |x: T, y: U| body
    input.parse::<Token![|]>()?;

    let mut params = Vec::new();

    if !input.peek(Token![|]) {
        loop {
            let name: Ident = input.parse()?;
            input.parse::<Token![:]>()?;
            let ty: Type = input.parse()?;
            params.push(QuantParam { name, ty });

            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            } else {
                break;
            }
        }
    }

    input.parse::<Token![|]>()?;

    let body = SpecExpr::parse(input)?;

    if is_forall {
        Ok(SpecExpr::Forall {
            params,
            body: Box::new(body),
        })
    } else {
        Ok(SpecExpr::Exists {
            params,
            body: Box::new(body),
        })
    }
}

impl ToTokens for SpecExpr {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            Self::Rust(e) => e.to_tokens(tokens),

            Self::Forall { params, body } => {
                let param_tokens: Vec<_> = params
                    .iter()
                    .map(|p| {
                        let name = &p.name;
                        let ty = &p.ty;
                        quote! { #name: #ty }
                    })
                    .collect();
                let body_tokens = body.to_token_stream();
                tokens.extend(quote! {
                    forall |#(#param_tokens),*| #body_tokens
                });
            }

            Self::Exists { params, body } => {
                let param_tokens: Vec<_> = params
                    .iter()
                    .map(|p| {
                        let name = &p.name;
                        let ty = &p.ty;
                        quote! { #name: #ty }
                    })
                    .collect();
                let body_tokens = body.to_token_stream();
                tokens.extend(quote! {
                    exists |#(#param_tokens),*| #body_tokens
                });
            }

            Self::Implies { lhs, rhs } => {
                let lhs_tokens = lhs.to_token_stream();
                let rhs_tokens = rhs.to_token_stream();
                tokens.extend(quote! {
                    (#lhs_tokens) => (#rhs_tokens)
                });
            }

            Self::Old(inner) => {
                let inner_tokens = inner.to_token_stream();
                tokens.extend(quote! {
                    old(#inner_tokens)
                });
            }

            Self::BinOp { left, op, right } => {
                let left_tokens = left.to_token_stream();
                let right_tokens = right.to_token_stream();
                let op_tokens = match op {
                    SpecBinOp::And => quote! { && },
                    SpecBinOp::Or => quote! { || },
                    SpecBinOp::Eq => quote! { == },
                    SpecBinOp::Ne => quote! { != },
                    SpecBinOp::Lt => quote! { < },
                    SpecBinOp::Le => quote! { <= },
                    SpecBinOp::Gt => quote! { > },
                    SpecBinOp::Ge => quote! { >= },
                    SpecBinOp::Add => quote! { + },
                    SpecBinOp::Sub => quote! { - },
                    SpecBinOp::Mul => quote! { * },
                    SpecBinOp::Div => quote! { / },
                    SpecBinOp::Rem => quote! { % },
                };
                tokens.extend(quote! {
                    (#left_tokens) #op_tokens (#right_tokens)
                });
            }

            Self::UnaryOp { op, operand } => {
                let operand_tokens = operand.to_token_stream();
                let op_tokens = match op {
                    SpecUnaryOp::Not => quote! { ! },
                    SpecUnaryOp::Neg => quote! { - },
                };
                tokens.extend(quote! {
                    #op_tokens (#operand_tokens)
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_spec(input: &str) -> SpecExpr {
        syn::parse_str::<SpecExpr>(input).expect("Failed to parse spec expression")
    }

    #[test]
    fn test_parse_simple_expr() {
        let expr = parse_spec("x > 0");
        assert!(matches!(
            expr,
            SpecExpr::BinOp {
                op: SpecBinOp::Gt,
                ..
            }
        ));
    }

    #[test]
    fn test_parse_implication() {
        let expr = parse_spec("x > 0 => y > 0");
        assert!(matches!(expr, SpecExpr::Implies { .. }));
    }

    #[test]
    fn test_parse_forall() {
        let expr = parse_spec("forall |i: usize| i < len");
        match expr {
            SpecExpr::Forall { params, body: _ } => {
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].name.to_string(), "i");
            }
            _ => panic!("Expected Forall"),
        }
    }

    #[test]
    fn test_parse_exists() {
        let expr = parse_spec("exists |x: i32| x == 0");
        match expr {
            SpecExpr::Exists { params, body: _ } => {
                assert_eq!(params.len(), 1);
            }
            _ => panic!("Expected Exists"),
        }
    }

    #[test]
    fn test_parse_old() {
        let expr = parse_spec("old(x) + 1");
        match expr {
            SpecExpr::BinOp {
                left,
                op: SpecBinOp::Add,
                ..
            } => {
                assert!(matches!(*left, SpecExpr::Old(_)));
            }
            _ => panic!("Expected BinOp with Old, got {expr:?}"),
        }
    }

    #[test]
    fn test_parse_old_wrong_arity_stays_rust() {
        let expr = parse_spec("old()");
        match expr {
            SpecExpr::Rust(Expr::Call(ExprCall { func, args, .. })) => {
                assert!(matches!(func.as_ref(), Expr::Path(p) if p.path.is_ident("old")));
                assert!(args.is_empty());
            }
            _ => panic!("Expected Rust Call for old()"),
        }

        let expr = parse_spec("old(x, y)");
        match expr {
            SpecExpr::Rust(Expr::Call(ExprCall { func, args, .. })) => {
                assert!(matches!(func.as_ref(), Expr::Path(p) if p.path.is_ident("old")));
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected Rust Call for old(x, y)"),
        }
    }

    #[test]
    fn test_parse_complex() {
        let expr = parse_spec("forall |i: usize, j: usize| i < j && j < len => arr[i] <= arr[j]");
        match expr {
            SpecExpr::Forall { params, body } => {
                assert_eq!(params.len(), 2);
                assert!(matches!(*body, SpecExpr::Implies { .. }));
            }
            _ => panic!("Expected Forall"),
        }
    }

    #[test]
    fn test_parse_nested_quantifiers() {
        let expr = parse_spec("forall |x: i32| exists |y: i32| x + y == 0");
        match expr {
            SpecExpr::Forall { body, .. } => {
                assert!(matches!(*body, SpecExpr::Exists { .. }));
            }
            _ => panic!("Expected nested quantifiers"),
        }
    }

    #[test]
    fn test_parse_boolean_ops() {
        let expr = parse_spec("a && b || c");
        // Rust parses as (a && b) || c due to precedence
        match expr {
            SpecExpr::BinOp {
                op: SpecBinOp::Or,
                left,
                ..
            } => {
                assert!(matches!(
                    *left,
                    SpecExpr::BinOp {
                        op: SpecBinOp::And,
                        ..
                    }
                ));
            }
            _ => panic!("Expected Or with And on left, got {expr:?}"),
        }
    }

    #[test]
    fn test_parse_negation() {
        let expr = parse_spec("!valid");
        assert!(matches!(
            expr,
            SpecExpr::UnaryOp {
                op: SpecUnaryOp::Not,
                ..
            }
        ));
    }

    #[test]
    fn test_parse_arithmetic() {
        let expr = parse_spec("x + y * z");
        // Rust parses as x + (y * z) due to precedence
        match expr {
            SpecExpr::BinOp {
                op: SpecBinOp::Add,
                right,
                ..
            } => {
                assert!(matches!(
                    *right,
                    SpecExpr::BinOp {
                        op: SpecBinOp::Mul,
                        ..
                    }
                ));
            }
            _ => panic!("Expected Add with Mul on right, got {expr:?}"),
        }
    }

    #[test]
    fn test_parse_method_call() {
        let expr = parse_spec("result.len() > 0");
        assert!(matches!(
            expr,
            SpecExpr::BinOp {
                op: SpecBinOp::Gt,
                ..
            }
        ));
    }

    #[test]
    fn test_parse_array_index() {
        let expr = parse_spec("arr[i] <= arr[j]");
        assert!(matches!(
            expr,
            SpecExpr::BinOp {
                op: SpecBinOp::Le,
                ..
            }
        ));
    }

    #[test]
    fn test_parse_result_keyword() {
        // 'result' is just an identifier in Rust, should parse fine
        let expr = parse_spec("result >= 0");
        assert!(matches!(
            expr,
            SpecExpr::BinOp {
                op: SpecBinOp::Ge,
                ..
            }
        ));
    }

    #[test]
    fn test_parse_chained_comparison() {
        // Note: Rust doesn't allow chained comparisons, so this parses the first part
        let expr = parse_spec("a <= b && b <= c");
        match expr {
            SpecExpr::BinOp {
                op: SpecBinOp::And,
                left,
                right,
            } => {
                assert!(matches!(
                    *left,
                    SpecExpr::BinOp {
                        op: SpecBinOp::Le,
                        ..
                    }
                ));
                assert!(matches!(
                    *right,
                    SpecExpr::BinOp {
                        op: SpecBinOp::Le,
                        ..
                    }
                ));
            }
            _ => panic!("Expected And with Le comparisons"),
        }
    }
}
