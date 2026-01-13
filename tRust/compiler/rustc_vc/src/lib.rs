//! Verification Condition Generation from MIR
//!
//! This crate is responsible for translating Rust's MIR (Mid-level IR)
//! plus specifications into verification conditions that can be checked
//! by the proof backends.
//!
//! The key insight is that MIR is already in a form that's close to what
//! verification tools need: SSA-like, explicit control flow, explicit drops.

pub mod async_state_machine;
pub mod contract_export;
pub mod deadlock_prover;
pub mod encoder;
pub mod liveness_prover;
pub mod loop_handling;
pub mod protocol_extractor;
pub mod symbolic_execution;
pub mod verify;
pub mod weakest_precondition;
pub mod wiring;

use vc_ir::{
    BackendHint, Expr, FunctionSignature, FunctionVcs, Predicate, SourceSpan, VcId, VcKind, VcType,
    VerificationCondition,
};

/// Main entry point: generate VCs for a function
///
/// In the real implementation, this would take rustc's TyCtxt and DefId.
/// Here we sketch the algorithm with placeholder types.
#[must_use]
pub fn generate_function_vcs(func: &MirFunction, specs: &FunctionSpecs) -> FunctionVcs {
    let generator = VcGenerator::new(func, specs);
    generator.generate()
}

/// Placeholder for MIR function (would be rustc_middle::mir::Body)
#[derive(Debug)]
pub struct MirFunction {
    pub name: String,
    pub params: Vec<(String, MirType)>,
    pub return_type: MirType,
    pub blocks: Vec<BasicBlock>,
    pub locals: Vec<LocalDecl>,
    /// Source span for the function definition (for error reporting)
    pub span: SourceSpan,
}

impl Default for MirFunction {
    fn default() -> Self {
        Self {
            name: String::new(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            blocks: vec![],
            locals: vec![],
            span: SourceSpan::default(),
        }
    }
}

impl MirFunction {
    /// Check if this function is marked as `unsafe fn`
    ///
    /// # Current Limitation
    /// This placeholder struct does not track unsafe status. When integrated with
    /// rustc's real MIR (rustc_middle::mir::Body), this will query the function's
    /// safety from the HIR/MIR metadata.
    ///
    /// Returns false (unsafe detection not yet implemented for placeholder MIR).
    #[must_use]
    pub const fn is_unsafe(&self) -> bool {
        // Real implementation: query tcx.fn_sig(def_id).safety() == Unsafety::Unsafe
        false
    }

    /// Check if this function body contains `unsafe { }` blocks
    ///
    /// # Current Limitation
    /// This placeholder struct does not track unsafe blocks. When integrated with
    /// rustc's real MIR, this will scan the HIR for UnsafeBlock nodes or query
    /// the compiler's unsafe checking results.
    ///
    /// Returns false (unsafe block detection not yet implemented for placeholder MIR).
    #[must_use]
    pub const fn has_unsafe_blocks(&self) -> bool {
        // Real implementation: query tcx.unsafety_check_result(def_id) or scan HIR
        false
    }
}

/// Placeholder for MIR type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MirType {
    Bool,
    Int {
        signed: bool,
        bits: u32,
    },
    Float {
        bits: u32,
    },
    Ref {
        mutable: bool,
        inner: Box<MirType>,
    },
    Array {
        elem: Box<MirType>,
        len: usize,
    },
    Tuple(Vec<MirType>),
    Adt {
        name: String,
    },
    /// Closure type with captured variable types
    Closure {
        /// Unique identifier for this closure (e.g., module::func::{closure#0})
        def_id: String,
        /// Types of captured variables
        captures: Vec<MirType>,
    },
    /// Function pointer type
    FnPtr {
        /// Parameter types
        params: Vec<MirType>,
        /// Return type
        ret: Box<MirType>,
    },
    /// Named function reference (not a closure, not a fn ptr - a specific function)
    FnDef {
        /// Function name
        name: String,
    },
}

impl std::fmt::Display for MirType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool => write!(f, "bool"),
            Self::Int { signed, bits } => {
                let prefix = if *signed { "i" } else { "u" };
                write!(f, "{prefix}{bits}")
            }
            Self::Float { bits } => write!(f, "f{bits}"),
            Self::Ref { mutable, inner } => {
                if *mutable {
                    write!(f, "&mut {inner}")
                } else {
                    write!(f, "&{inner}")
                }
            }
            Self::Array { elem, len } => write!(f, "[{elem}; {len}]"),
            Self::Tuple(elems) => {
                write!(f, "(")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{elem}")?;
                }
                write!(f, ")")
            }
            Self::Adt { name } | Self::FnDef { name } => write!(f, "{name}"),
            Self::Closure { def_id, .. } => write!(f, "{def_id}"),
            Self::FnPtr { params, ret } => {
                write!(f, "fn(")?;
                for (i, p) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{p}")?;
                }
                write!(f, ") -> {ret}")
            }
        }
    }
}

/// Generate a monomorphized function name including generic arguments (Phase 6.5.2)
///
/// This creates a unique name for each instantiation of a generic function,
/// allowing the call graph to distinguish between different monomorphizations.
///
/// # Examples
/// - `Option::map` with `[i32, fn(i32)->bool]` -> `Option::map<i32, fn(i32) -> bool>`
/// - `Vec::push` with `[String]` -> `Vec::push<String>`
/// - `foo` with `[]` -> `foo` (non-generic)
#[must_use]
pub fn monomorphized_name(base_name: &str, generic_args: &[MirType]) -> String {
    if generic_args.is_empty() {
        base_name.to_string()
    } else {
        let args_str = generic_args
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        format!("{base_name}<{args_str}>")
    }
}

/// Basic block in MIR
#[derive(Debug)]
pub struct BasicBlock {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

/// MIR statement
#[derive(Debug)]
pub enum Statement {
    Assign { place: Place, rvalue: Rvalue },
    StorageLive(Local),
    StorageDead(Local),
    // ... other statements
}

/// Place (lvalue)
#[derive(Debug, Clone)]
pub struct Place {
    pub local: Local,
    pub projections: Vec<Projection>,
}

/// Local variable index
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Local(pub usize);

/// Projection (field access, deref, index)
#[derive(Debug, Clone)]
pub enum Projection {
    Deref,
    Field(usize),
    Index(Local),
}

/// Rvalue (right-hand side of assignment)
#[derive(Debug, Clone)]
pub enum Rvalue {
    Use(Operand),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
    Ref {
        mutable: bool,
        place: Place,
    },
    /// Array/tuple/struct literal
    Aggregate {
        kind: AggregateKind,
        operands: Vec<Operand>,
    },
    /// Get length of array/slice
    Len(Place),
    /// Type cast
    Cast {
        kind: CastKind,
        operand: Operand,
        ty: MirType,
    },
    /// Get discriminant of enum
    Discriminant(Place),
    /// Repeat value to create array: [val; count]
    Repeat {
        operand: Operand,
        count: usize,
    },
    /// Checked binary operation (returns (result, overflow_flag))
    CheckedBinaryOp(BinOp, Operand, Operand),
    /// Null operation (e.g., for ZSTs)
    NullaryOp(NullOp, MirType),
}

/// Kind of aggregate being constructed
#[derive(Debug, Clone)]
pub enum AggregateKind {
    /// Array literal
    Array(MirType),
    /// Tuple literal
    Tuple,
    /// Struct literal
    Adt {
        name: String,
        variant: Option<usize>,
    },
    /// Closure construction - operands are the captured variables
    Closure {
        /// Unique identifier for this closure def
        def_id: String,
    },
    /// Generator/coroutine construction (async blocks become generators)
    Coroutine {
        /// Unique identifier for the coroutine
        def_id: String,
    },
}

/// Kind of cast operation
#[derive(Debug, Clone)]
pub enum CastKind {
    /// Numeric cast (e.g., i32 to i64)
    IntToInt,
    /// Float to int
    FloatToInt,
    /// Int to float
    IntToFloat,
    /// Pointer cast
    PtrToPtr,
    /// Function pointer cast
    FnPtrToPtr,
    /// Pointer to address
    PtrToAddr,
    /// Address to pointer
    AddrToPtr,
}

/// Nullary operations
#[derive(Debug, Clone)]
pub enum NullOp {
    /// Size of type
    SizeOf,
    /// Alignment of type
    AlignOf,
}

/// Operand
#[derive(Debug, Clone)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

/// Constant value
#[derive(Debug, Clone)]
pub enum Constant {
    Bool(bool),
    Int(i128),
    Float(f64),
}

/// Binary operation
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

/// Unary operation
#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    Not,
    Neg,
}

/// Block terminator
#[derive(Debug, Clone)]
pub enum Terminator {
    Goto {
        target: usize,
    },
    SwitchInt {
        discr: Operand,
        targets: Vec<(u128, usize)>,
        otherwise: usize,
    },
    Return,
    Call {
        func: String,
        args: Vec<Operand>,
        destination: Place,
        target: usize,
        span: SourceSpan,
        /// Generic type arguments for monomorphized calls (Phase 6.5.2)
        /// Empty for non-generic calls
        generic_args: Vec<MirType>,
    },
    /// Indirect call through function pointer or closure
    IndirectCall {
        /// The callee - a Place containing a fn ptr or closure
        callee: Place,
        /// Type of the callee (FnPtr or Closure)
        callee_ty: MirType,
        /// Arguments to the function
        args: Vec<Operand>,
        /// Where to store the result
        destination: Place,
        /// Next basic block
        target: usize,
        /// Source location
        span: SourceSpan,
    },
    Assert {
        cond: Operand,
        expected: bool,
        target: usize,
    },
    Unreachable,
}

/// Local variable declaration
#[derive(Debug)]
pub struct LocalDecl {
    pub ty: MirType,
    pub name: Option<String>,
}

/// Function specifications (parsed from attributes)
#[derive(Clone, Debug, Default)]
pub struct FunctionSpecs {
    pub requires: Vec<vc_ir::SpecClause>,
    pub ensures: Vec<vc_ir::SpecClause>,
    pub decreases: Option<vc_ir::DecreasesClause>,
    pub pure: bool,
    pub trusted: bool,
    /// Optional API metadata for cross-language contract export (Phase 6.5.6)
    pub api_metadata: Option<crate::contract_export::ApiMetadata>,
    /// Declared effects (Phase 5)
    pub effects: Option<vc_ir::EffectSet>,
    /// Optional parameter-level refinement predicates (Phase 12)
    ///
    /// Keyed by parameter name. Values are the refinement predicate string (e.g., `"x > 0"`).
    pub param_refinements: std::collections::HashMap<String, String>,
}

/// The VC generator
struct VcGenerator<'a> {
    func: &'a MirFunction,
    specs: &'a FunctionSpecs,
    next_vc_id: u64,
    vcs: FunctionVcs,
}

impl<'a> VcGenerator<'a> {
    fn new(func: &'a MirFunction, specs: &'a FunctionSpecs) -> Self {
        Self {
            func,
            specs,
            next_vc_id: 0,
            vcs: FunctionVcs {
                name: func.name.clone(),
                signature: FunctionSignature {
                    name: func.name.clone(),
                    params: func
                        .params
                        .iter()
                        .map(|(n, t)| (n.clone(), mir_type_to_vc(t)))
                        .collect(),
                    return_type: mir_type_to_vc(&func.return_type),
                },
                requires: vec![],
                ensures: vec![],
                loop_invariants: vec![],
                assertions: vec![],
                termination: None,
            },
        }
    }

    const fn fresh_vc_id(&mut self) -> VcId {
        let id = VcId(self.next_vc_id);
        self.next_vc_id += 1;
        id
    }

    fn generate(mut self) -> FunctionVcs {
        // 1. Generate precondition VCs (callers must satisfy)
        for req in &self.specs.requires {
            let vc = VerificationCondition {
                id: self.fresh_vc_id(),
                name: format!("precondition of {}", self.func.name),
                span: req.span.clone(),
                condition: VcKind::Predicate(req.pred.clone()),
                preferred_backend: Some(BackendHint::Smt),
            };
            self.vcs.requires.push(vc);
        }

        // 2. Generate postcondition VCs using weakest precondition
        for ens in &self.specs.ensures {
            let wp = Self::weakest_precondition(&ens.pred);
            let vc = VerificationCondition {
                id: self.fresh_vc_id(),
                name: format!("postcondition of {}", self.func.name),
                span: ens.span.clone(),
                condition: VcKind::Implies {
                    antecedent: self.precondition_conjunction(),
                    consequent: wp,
                },
                preferred_backend: Some(BackendHint::Smt),
            };
            self.vcs.ensures.push(vc);
        }

        // 3. Generate borrow aliasing VCs (N3.1b: Borrow Semantics)
        // For functions with reference parameters, generate VCs ensuring
        // mutable references don't alias with other references.
        self.generate_borrow_aliasing_vcs();

        // 4. Generate termination VCs if specified
        if let Some(decreases) = &self.specs.decreases {
            let vc = self.generate_termination_vc(decreases);
            self.vcs.termination = Some(vc);
        }

        // 5. Walk MIR and generate VCs for assertions, bounds checks, etc.
        self.walk_mir();

        self.vcs
    }

    /// Generate VCs ensuring mutable reference parameters don't alias (N3.1b)
    ///
    /// In Rust's ownership model:
    /// - A `&mut T` reference must be exclusive: no other references to the same location
    /// - Multiple `&T` references can coexist (shared borrowing)
    ///
    /// For function parameters, we generate VCs of the form:
    /// `addr(mut_ref) != addr(other_ref)` for each &mut T parameter paired with other refs
    ///
    /// This documents and verifies the aliasing XOR mutability invariant.
    fn generate_borrow_aliasing_vcs(&mut self) {
        // Collect all reference parameters with their indices
        let ref_params: Vec<(usize, &str, bool)> = self
            .func
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, (name, ty))| {
                if let MirType::Ref { mutable, .. } = ty {
                    Some((idx, name.as_str(), *mutable))
                } else {
                    None
                }
            })
            .collect();

        // For each mutable reference, ensure it doesn't alias with any other reference
        for (i, (idx_a, name_a, mutable_a)) in ref_params.iter().enumerate() {
            if !mutable_a {
                continue; // Only &mut needs non-aliasing checks
            }

            for (idx_b, name_b, _mutable_b) in ref_params.iter().skip(i + 1) {
                // Generate: addr(param_a) != addr(param_b)
                // Parameters are named _1, _2, etc. in MIR convention
                let addr_a = Expr::AddrOf(Box::new(Expr::Var(format!("_{}", idx_a + 1))));
                let addr_b = Expr::AddrOf(Box::new(Expr::Var(format!("_{}", idx_b + 1))));
                let non_aliasing = Predicate::Expr(Expr::Ne(Box::new(addr_a), Box::new(addr_b)));

                let vc = VerificationCondition {
                    id: self.fresh_vc_id(),
                    name: format!("borrow aliasing: &mut {} != {}", name_a, name_b),
                    span: SourceSpan::default(),
                    condition: VcKind::Predicate(non_aliasing),
                    preferred_backend: Some(BackendHint::Smt),
                };
                self.vcs.assertions.push(vc);
            }
        }
    }

    /// Compute weakest precondition of postcondition through function body
    fn weakest_precondition(postcond: &Predicate) -> Predicate {
        // This would implement the actual WP calculus over MIR
        // For now, return the postcondition transformed for SSA form

        // The real implementation would:
        // 1. Start from return points
        // 2. Work backwards through the CFG
        // 3. Transform predicates according to WP rules:
        //    - wp(x := e, P) = P[e/x]
        //    - wp(if c then S1 else S2, P) = (c => wp(S1,P)) && (!c => wp(S2,P))
        //    - wp(while ...) requires loop invariants

        postcond.clone()
    }

    /// Conjunction of all preconditions
    fn precondition_conjunction(&self) -> Predicate {
        if self.specs.requires.is_empty() {
            Predicate::Bool(true)
        } else {
            Predicate::And(self.specs.requires.iter().map(|r| r.pred.clone()).collect())
        }
    }

    /// Generate termination verification condition
    fn generate_termination_vc(
        &mut self,
        decreases: &vc_ir::DecreasesClause,
    ) -> VerificationCondition {
        // Find all recursive calls and generate proof obligations that
        // the decreases measure actually decreases

        let recursive_calls = self.find_recursive_calls();

        VerificationCondition {
            id: self.fresh_vc_id(),
            name: format!("termination of {}", self.func.name),
            span: decreases.span.clone(),
            condition: VcKind::Termination {
                decreases: decreases.measure.clone(),
                recursive_calls,
            },
            preferred_backend: Some(BackendHint::TheoremProver),
        }
    }

    /// Find recursive calls in the function
    fn find_recursive_calls(&self) -> Vec<Expr> {
        let mut calls = vec![];
        for block in &self.func.blocks {
            if let Terminator::Call { func, .. } = &block.terminator {
                if func == &self.func.name {
                    // Found recursive call - would extract the decreases expression
                    // evaluated at the call arguments
                    calls.push(Expr::Apply {
                        func: "recursive_call_measure".to_string(),
                        args: vec![], // Would translate actual args
                    });
                }
            }
        }
        calls
    }

    /// Walk MIR and generate VCs for internal assertions
    fn walk_mir(&mut self) {
        for (block_idx, block) in self.func.blocks.iter().enumerate() {
            // Check for assert terminators
            if let Terminator::Assert { cond, expected, .. } = &block.terminator {
                let pred = operand_to_expr(cond);
                let pred = if *expected {
                    Predicate::Expr(pred)
                } else {
                    Predicate::Not(Box::new(Predicate::Expr(pred)))
                };

                let vc = VerificationCondition {
                    id: self.fresh_vc_id(),
                    name: format!("assertion in block {block_idx}"),
                    span: SourceSpan::default(),
                    condition: VcKind::Predicate(pred),
                    preferred_backend: Some(BackendHint::Smt),
                };
                self.vcs.assertions.push(vc);
            }

            // Would also check:
            // - Array bounds
            // - Division by zero
            // - Overflow (if enabled)
            // - Null pointer dereference
            // - etc.
        }
    }
}

/// Convert MIR type to VC type
fn mir_type_to_vc(ty: &MirType) -> VcType {
    match ty {
        MirType::Bool => VcType::Bool,
        MirType::Int { signed, bits } => VcType::Int {
            signed: *signed,
            bits: *bits,
        },
        MirType::Float { bits } => VcType::Float { bits: *bits },
        MirType::Ref { mutable, inner } => VcType::Ref {
            mutable: *mutable,
            inner: Box::new(mir_type_to_vc(inner)),
        },
        MirType::Array { elem, len } => VcType::Array {
            elem: Box::new(mir_type_to_vc(elem)),
            len: Some(*len),
        },
        MirType::Tuple(elems) => VcType::Tuple(elems.iter().map(mir_type_to_vc).collect()),
        MirType::Adt { name } => VcType::Struct {
            name: name.clone(),
            fields: vec![], // Would be populated from type info
        },
        MirType::Closure { def_id, captures } => VcType::Struct {
            name: format!("closure#{def_id}"),
            fields: captures
                .iter()
                .enumerate()
                .map(|(i, t)| (format!("capture_{i}"), mir_type_to_vc(t)))
                .collect(),
        },
        MirType::FnPtr { params, ret } => VcType::Struct {
            name: format!("fn_ptr({} args)", params.len()),
            fields: vec![("ret".to_string(), mir_type_to_vc(ret))],
        },
        MirType::FnDef { name } => VcType::Struct {
            name: format!("fn#{name}"),
            fields: vec![],
        },
    }
}

/// Convert operand to VC expression
fn operand_to_expr(op: &Operand) -> Expr {
    match op {
        Operand::Constant(c) => match c {
            Constant::Bool(b) => Expr::BoolLit(*b),
            Constant::Int(i) => Expr::IntLit(*i),
            Constant::Float(f) => Expr::FloatLit(*f),
        },
        Operand::Copy(place) | Operand::Move(place) => place_to_expr(place),
    }
}

/// Convert place to VC expression
fn place_to_expr(place: &Place) -> Expr {
    let mut expr = Expr::Var(format!("_{}", place.local.0));
    for proj in &place.projections {
        expr = match proj {
            Projection::Deref => Expr::Deref(Box::new(expr)),
            Projection::Field(idx) => Expr::TupleField(Box::new(expr), *idx),
            Projection::Index(local) => {
                Expr::ArrayIndex(Box::new(expr), Box::new(Expr::Var(format!("_{}", local.0))))
            }
        };
    }
    expr
}

// =============================================================================
// Phase 9: Proof-Driven Optimization Infrastructure
// =============================================================================

/// Kind of safe operation that was proven safe during verification
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafeOperationKind {
    /// Overflow check for arithmetic operation is unnecessary
    OverflowCheck { op: BinOp, operand_type: MirType },
    /// Bounds check for array access is unnecessary
    BoundsCheck {
        /// Index expression (if available as constant)
        index_const: Option<usize>,
        /// Array length (if known)
        array_len: Option<usize>,
    },
    /// Division by zero check is unnecessary (divisor proven non-zero)
    DivisionByZero,
    /// Modulo by zero check is unnecessary (divisor proven non-zero)
    ModuloByZero,
    /// Unwrap check is unnecessary (Option/Result proven Some/Ok)
    UnwrapCheck,
    /// Branch condition proven to always be a specific value
    DeadBranch {
        /// The value the condition is proven to always equal
        proven_value: u128,
    },
    /// Refinement specialization: a generic parameter or value is proven to satisfy a refinement predicate
    /// at a specific call site. Enables specializing the callee based on proven properties.
    RefinementSpecialization {
        /// Name of the function being called
        callee: String,
        /// Parameter index (0-based) or None if referring to receiver (self)
        param_index: Option<usize>,
        /// The proven refinement predicate (SMT-LIB expression)
        predicate: String,
    },
}

/// A safe operation identified during verification
#[derive(Debug, Clone)]
pub struct SafeOperation {
    /// Unique identifier for this safe operation
    pub id: u64,
    /// Kind of safe operation
    pub kind: SafeOperationKind,
    /// Function containing the operation
    pub function: String,
    /// Location in the MIR (block index, statement/terminator)
    pub location: MirLocation,
    /// Source span for diagnostics
    pub span: SourceSpan,
    /// Reason the operation was proven safe
    pub reason: String,
}

/// Location within MIR
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MirLocation {
    /// Basic block index
    pub block: usize,
    /// Position within block: statement index or terminator
    pub position: MirPosition,
}

/// Position within a basic block
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MirPosition {
    /// Statement at given index
    Statement(usize),
    /// The block's terminator
    Terminator,
}

/// Result of applying an optimization
#[derive(Debug, Clone)]
pub struct OptimizationResult {
    /// Number of overflow checks eliminated
    pub overflow_checks_eliminated: usize,
    /// Number of bounds checks eliminated
    pub bounds_checks_eliminated: usize,
    /// Number of null/unwrap checks eliminated (Option/Result)
    pub null_checks_eliminated: usize,
    /// Number of dead branches eliminated (proven-false branches)
    pub dead_branches_eliminated: usize,
    /// Number of refinement specializations applied (generic parameters with proven predicates)
    pub refinements_specialized: usize,
    /// Number of other checks eliminated
    pub other_checks_eliminated: usize,
    /// Individual optimizations applied
    pub applied: Vec<AppliedOptimization>,
}

impl OptimizationResult {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            overflow_checks_eliminated: 0,
            bounds_checks_eliminated: 0,
            null_checks_eliminated: 0,
            dead_branches_eliminated: 0,
            refinements_specialized: 0,
            other_checks_eliminated: 0,
            applied: Vec::new(),
        }
    }

    #[must_use]
    pub const fn total_optimizations(&self) -> usize {
        self.overflow_checks_eliminated
            + self.bounds_checks_eliminated
            + self.null_checks_eliminated
            + self.dead_branches_eliminated
            + self.refinements_specialized
            + self.other_checks_eliminated
    }
}

impl Default for OptimizationResult {
    fn default() -> Self {
        Self::new()
    }
}

/// Record of a single optimization applied
#[derive(Debug, Clone)]
pub struct AppliedOptimization {
    /// The safe operation that enabled this optimization
    pub safe_op: SafeOperation,
    /// Description of what was changed
    pub description: String,
}

/// Trait for optimization passes that transform MIR based on proof results
pub trait OptimizationPass {
    /// Name of this optimization pass
    fn name(&self) -> &str;

    /// Apply this optimization to the MIR function
    /// Returns the optimized MIR and what optimizations were applied
    fn optimize(
        &self,
        func: MirFunction,
        safe_ops: &[SafeOperation],
    ) -> (MirFunction, OptimizationResult);
}

/// Overflow check elimination pass (Phase 9.3)
/// Converts CheckedBinaryOp to BinaryOp when overflow is proven impossible
pub struct OverflowCheckElimination;

impl OverflowCheckElimination {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    /// Check if a safe operation applies to a given statement
    fn applies_to_statement(safe_op: &SafeOperation, block_idx: usize, stmt_idx: usize) -> bool {
        if let SafeOperationKind::OverflowCheck { .. } = &safe_op.kind {
            safe_op.location.block == block_idx
                && safe_op.location.position == MirPosition::Statement(stmt_idx)
        } else {
            false
        }
    }
}

impl Default for OverflowCheckElimination {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for OverflowCheckElimination {
    fn name(&self) -> &str {
        "overflow_check_elimination"
    }

    fn optimize(
        &self,
        mut func: MirFunction,
        safe_ops: &[SafeOperation],
    ) -> (MirFunction, OptimizationResult) {
        let mut result = OptimizationResult::new();

        // Walk through all blocks and statements
        for (block_idx, block) in func.blocks.iter_mut().enumerate() {
            for (stmt_idx, stmt) in block.statements.iter_mut().enumerate() {
                // Find safe operations that apply to this statement
                let matching_safe_ops: Vec<_> = safe_ops
                    .iter()
                    .filter(|op| Self::applies_to_statement(op, block_idx, stmt_idx))
                    .collect();

                if matching_safe_ops.is_empty() {
                    continue;
                }

                // Check if this is a CheckedBinaryOp assignment
                if let Statement::Assign { rvalue, .. } = stmt {
                    if let Rvalue::CheckedBinaryOp(op, lhs, rhs) = rvalue {
                        // Convert to unchecked operation
                        let op_copy = *op;
                        let lhs_copy = lhs.clone();
                        let rhs_copy = rhs.clone();
                        *rvalue = Rvalue::BinaryOp(op_copy, lhs_copy, rhs_copy);

                        result.overflow_checks_eliminated += 1;
                        result.applied.push(AppliedOptimization {
                            safe_op: matching_safe_ops[0].clone(),
                            description: format!(
                                "Converted CheckedBinaryOp({op_copy:?}) to BinaryOp at block {block_idx} stmt {stmt_idx}"
                            ),
                        });
                    }
                }
            }
        }

        (func, result)
    }
}

/// Bounds check elimination pass (Phase 9.1)
/// Removes Assert terminators that check array bounds when proven in-bounds
pub struct BoundsCheckElimination;

impl BoundsCheckElimination {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    /// Check if a safe operation applies to a terminator
    fn applies_to_terminator(safe_op: &SafeOperation, block_idx: usize) -> bool {
        if let SafeOperationKind::BoundsCheck { .. } = &safe_op.kind {
            safe_op.location.block == block_idx
                && safe_op.location.position == MirPosition::Terminator
        } else {
            false
        }
    }
}

impl Default for BoundsCheckElimination {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for BoundsCheckElimination {
    fn name(&self) -> &str {
        "bounds_check_elimination"
    }

    fn optimize(
        &self,
        mut func: MirFunction,
        safe_ops: &[SafeOperation],
    ) -> (MirFunction, OptimizationResult) {
        let mut result = OptimizationResult::new();

        // Walk through all blocks looking for Assert terminators (bounds checks)
        for (block_idx, block) in func.blocks.iter_mut().enumerate() {
            // Find safe operations that apply to this terminator
            let matching_safe_ops: Vec<_> = safe_ops
                .iter()
                .filter(|op| Self::applies_to_terminator(op, block_idx))
                .collect();

            if matching_safe_ops.is_empty() {
                continue;
            }

            // Check if this is an Assert terminator (bounds check)
            if let Terminator::Assert { target, .. } = &block.terminator {
                let target_block = *target;
                // Replace Assert with unconditional Goto (the check always passes)
                block.terminator = Terminator::Goto {
                    target: target_block,
                };

                result.bounds_checks_eliminated += 1;
                result.applied.push(AppliedOptimization {
                    safe_op: matching_safe_ops[0].clone(),
                    description: format!(
                        "Eliminated bounds check Assert at block {block_idx}, now Goto block {target_block}"
                    ),
                });
            }
        }

        (func, result)
    }
}

/// Division/modulo by zero check elimination
/// Removes division/modulo checks when divisor proven non-zero
pub struct DivisionCheckElimination;

impl DivisionCheckElimination {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    fn applies_to_terminator(safe_op: &SafeOperation, block_idx: usize) -> bool {
        matches!(
            safe_op.kind,
            SafeOperationKind::DivisionByZero | SafeOperationKind::ModuloByZero
        ) && safe_op.location.block == block_idx
            && safe_op.location.position == MirPosition::Terminator
    }
}

impl Default for DivisionCheckElimination {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for DivisionCheckElimination {
    fn name(&self) -> &str {
        "division_check_elimination"
    }

    fn optimize(
        &self,
        mut func: MirFunction,
        safe_ops: &[SafeOperation],
    ) -> (MirFunction, OptimizationResult) {
        let mut result = OptimizationResult::new();

        for (block_idx, block) in func.blocks.iter_mut().enumerate() {
            let matching_safe_ops: Vec<_> = safe_ops
                .iter()
                .filter(|op| Self::applies_to_terminator(op, block_idx))
                .collect();

            if matching_safe_ops.is_empty() {
                continue;
            }

            // Check if this is an Assert terminator (division by zero check)
            if let Terminator::Assert { target, .. } = &block.terminator {
                let target_block = *target;
                block.terminator = Terminator::Goto {
                    target: target_block,
                };

                result.other_checks_eliminated += 1;
                result.applied.push(AppliedOptimization {
                    safe_op: matching_safe_ops[0].clone(),
                    description: format!(
                        "Eliminated division-by-zero check at block {block_idx}, now Goto block {target_block}"
                    ),
                });
            }
        }

        (func, result)
    }
}

/// Null check elimination pass (Phase 9.2)
/// Removes Option unwrap checks when Some proven, Result unwrap checks when Ok proven
pub struct NullCheckElimination;

impl NullCheckElimination {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    fn applies_to_terminator(safe_op: &SafeOperation, block_idx: usize) -> bool {
        matches!(safe_op.kind, SafeOperationKind::UnwrapCheck)
            && safe_op.location.block == block_idx
            && safe_op.location.position == MirPosition::Terminator
    }
}

impl Default for NullCheckElimination {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for NullCheckElimination {
    fn name(&self) -> &str {
        "null_check_elimination"
    }

    fn optimize(
        &self,
        mut func: MirFunction,
        safe_ops: &[SafeOperation],
    ) -> (MirFunction, OptimizationResult) {
        let mut result = OptimizationResult::new();

        for (block_idx, block) in func.blocks.iter_mut().enumerate() {
            let matching_safe_ops: Vec<_> = safe_ops
                .iter()
                .filter(|op| Self::applies_to_terminator(op, block_idx))
                .collect();

            if matching_safe_ops.is_empty() {
                continue;
            }

            // Check if this is an Assert terminator (Option/Result unwrap check)
            // Option::unwrap() generates: if discriminant == 0 { panic } else { value }
            // We convert Assert { cond, expected, target } to Goto { target }
            if let Terminator::Assert { target, .. } = &block.terminator {
                let target_block = *target;
                block.terminator = Terminator::Goto {
                    target: target_block,
                };

                result.null_checks_eliminated += 1;
                result.applied.push(AppliedOptimization {
                    safe_op: matching_safe_ops[0].clone(),
                    description: format!(
                        "Eliminated unwrap check at block {block_idx}, now Goto block {target_block}"
                    ),
                });
            }
        }

        (func, result)
    }
}

/// Dead branch elimination pass (Phase 9.4)
/// Converts SwitchInt to Goto when branch condition is proven to always be a specific value
pub struct DeadBranchElimination;

impl DeadBranchElimination {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    /// Check if a safe operation applies to a given terminator for dead branch elimination
    fn applies_to_terminator(safe_op: &SafeOperation, block_idx: usize) -> bool {
        matches!(safe_op.kind, SafeOperationKind::DeadBranch { .. })
            && safe_op.location.block == block_idx
            && safe_op.location.position == MirPosition::Terminator
    }
}

impl Default for DeadBranchElimination {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for DeadBranchElimination {
    fn name(&self) -> &str {
        "dead_branch_elimination"
    }

    fn optimize(
        &self,
        mut func: MirFunction,
        safe_ops: &[SafeOperation],
    ) -> (MirFunction, OptimizationResult) {
        let mut result = OptimizationResult::new();

        for (block_idx, block) in func.blocks.iter_mut().enumerate() {
            let matching_safe_ops: Vec<_> = safe_ops
                .iter()
                .filter(|op| Self::applies_to_terminator(op, block_idx))
                .collect();

            if matching_safe_ops.is_empty() {
                continue;
            }

            // Check if this is a SwitchInt terminator (branch)
            // When we've proven the discriminant is always a specific value,
            // we can replace the switch with an unconditional goto to the matching arm
            if let Terminator::SwitchInt {
                targets, otherwise, ..
            } = &block.terminator
            {
                // Get the proven value from the safe operation
                if let SafeOperationKind::DeadBranch { proven_value } = &matching_safe_ops[0].kind {
                    // Find the target for the proven value
                    let target_block = targets
                        .iter()
                        .find(|(val, _)| *val == *proven_value)
                        .map_or(*otherwise, |(_, target)| *target);

                    // Replace SwitchInt with Goto
                    block.terminator = Terminator::Goto {
                        target: target_block,
                    };

                    result.dead_branches_eliminated += 1;
                    result.applied.push(AppliedOptimization {
                        safe_op: matching_safe_ops[0].clone(),
                        description: format!(
                            "Eliminated dead branch at block {block_idx} (condition proven = {proven_value}), now Goto block {target_block}"
                        ),
                    });
                }
            }
        }

        (func, result)
    }
}

/// Refinement specialization pass (Phase 9.4)
/// Records call sites where parameters are proven to satisfy refinement predicates.
/// This information can be used to:
/// 1. Eliminate precondition checks within the callee
/// 2. Enable further optimizations that depend on the refinement
/// 3. Generate specialized versions of generic functions
pub struct RefinementSpecialization;

impl RefinementSpecialization {
    #[must_use]
    pub const fn new() -> Self {
        Self
    }

    /// Check if a safe operation applies to a given terminator for refinement specialization
    fn applies_to_terminator(safe_op: &SafeOperation, block_idx: usize) -> bool {
        matches!(
            safe_op.kind,
            SafeOperationKind::RefinementSpecialization { .. }
        ) && safe_op.location.block == block_idx
            && safe_op.location.position == MirPosition::Terminator
    }
}

impl Default for RefinementSpecialization {
    fn default() -> Self {
        Self::new()
    }
}

impl OptimizationPass for RefinementSpecialization {
    fn name(&self) -> &str {
        "refinement_specialization"
    }

    fn optimize(
        &self,
        mut func: MirFunction,
        safe_ops: &[SafeOperation],
    ) -> (MirFunction, OptimizationResult) {
        let mut result = OptimizationResult::new();

        for (block_idx, block) in func.blocks.iter_mut().enumerate() {
            let matching_safe_ops: Vec<_> = safe_ops
                .iter()
                .filter(|op| Self::applies_to_terminator(op, block_idx))
                .collect();

            if matching_safe_ops.is_empty() {
                continue;
            }

            // Check if this is a Call terminator
            // When we've proven a parameter satisfies a refinement predicate,
            // we can record this for potential specialization
            if let Terminator::Call {
                func: _,
                args: _,
                destination: _,
                target: _,
                span: _,
                ..
            } = &block.terminator
            {
                for safe_op in matching_safe_ops {
                    if let SafeOperationKind::RefinementSpecialization {
                        callee,
                        param_index,
                        predicate,
                    } = &safe_op.kind
                    {
                        // Record the specialization opportunity
                        // In a full implementation, this would:
                        // 1. Mark the call site for specialization
                        // 2. Potentially inline a specialized version of the callee
                        // 3. Eliminate redundant precondition checks
                        result.refinements_specialized += 1;
                        result.applied.push(AppliedOptimization {
                            safe_op: safe_op.clone(),
                            description: format!(
                                "Refinement specialization at block {}: call to {} with param {} satisfying predicate {}",
                                block_idx,
                                callee,
                                param_index.map(|i| i.to_string()).unwrap_or_else(|| "self".to_string()),
                                predicate
                            ),
                        });
                    }
                }
            }
        }

        (func, result)
    }
}

/// The MIR optimizer orchestrates optimization passes
pub struct MirOptimizer {
    passes: Vec<Box<dyn OptimizationPass>>,
}

impl MirOptimizer {
    /// Create a new optimizer with default passes
    #[must_use]
    pub fn new() -> Self {
        Self {
            passes: vec![
                Box::new(OverflowCheckElimination::new()),
                Box::new(BoundsCheckElimination::new()),
                Box::new(NullCheckElimination::new()),
                Box::new(DivisionCheckElimination::new()),
                Box::new(DeadBranchElimination::new()),
                Box::new(RefinementSpecialization::new()),
            ],
        }
    }

    /// Create an optimizer with no passes (for testing)
    #[must_use]
    pub fn empty() -> Self {
        Self { passes: vec![] }
    }

    /// Add an optimization pass
    pub fn add_pass(&mut self, pass: Box<dyn OptimizationPass>) {
        self.passes.push(pass);
    }

    /// Run all optimization passes on the function
    #[must_use]
    pub fn optimize(
        &self,
        mut func: MirFunction,
        safe_ops: &[SafeOperation],
    ) -> (MirFunction, OptimizationResult) {
        let mut combined_result = OptimizationResult::new();

        for pass in &self.passes {
            let (new_func, pass_result) = pass.optimize(func, safe_ops);
            func = new_func;

            // Accumulate results
            combined_result.overflow_checks_eliminated += pass_result.overflow_checks_eliminated;
            combined_result.bounds_checks_eliminated += pass_result.bounds_checks_eliminated;
            combined_result.null_checks_eliminated += pass_result.null_checks_eliminated;
            combined_result.dead_branches_eliminated += pass_result.dead_branches_eliminated;
            combined_result.refinements_specialized += pass_result.refinements_specialized;
            combined_result.other_checks_eliminated += pass_result.other_checks_eliminated;
            combined_result.applied.extend(pass_result.applied);
        }

        (func, combined_result)
    }

    /// Get the names of all registered passes
    #[must_use]
    pub fn pass_names(&self) -> Vec<&str> {
        self.passes.iter().map(|p| p.name()).collect()
    }
}

impl Default for MirOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper function to create a SafeOperation for an overflow check
#[must_use]
pub fn safe_overflow_check(
    id: u64,
    function: &str,
    block: usize,
    stmt: usize,
    op: BinOp,
    operand_type: MirType,
    reason: &str,
) -> SafeOperation {
    SafeOperation {
        id,
        kind: SafeOperationKind::OverflowCheck { op, operand_type },
        function: function.to_string(),
        location: MirLocation {
            block,
            position: MirPosition::Statement(stmt),
        },
        span: SourceSpan::default(),
        reason: reason.to_string(),
    }
}

/// Helper function to create a SafeOperation for a bounds check
#[must_use]
pub fn safe_bounds_check(
    id: u64,
    function: &str,
    block: usize,
    index_const: Option<usize>,
    array_len: Option<usize>,
    reason: &str,
) -> SafeOperation {
    SafeOperation {
        id,
        kind: SafeOperationKind::BoundsCheck {
            index_const,
            array_len,
        },
        function: function.to_string(),
        location: MirLocation {
            block,
            position: MirPosition::Terminator,
        },
        span: SourceSpan::default(),
        reason: reason.to_string(),
    }
}

/// Helper function to create a SafeOperation for division by zero
#[must_use]
pub fn safe_division_check(id: u64, function: &str, block: usize, reason: &str) -> SafeOperation {
    SafeOperation {
        id,
        kind: SafeOperationKind::DivisionByZero,
        function: function.to_string(),
        location: MirLocation {
            block,
            position: MirPosition::Terminator,
        },
        span: SourceSpan::default(),
        reason: reason.to_string(),
    }
}

/// Helper function to create a SafeOperation for an unwrap check (Option/Result)
#[must_use]
pub fn safe_unwrap_check(id: u64, function: &str, block: usize, reason: &str) -> SafeOperation {
    SafeOperation {
        id,
        kind: SafeOperationKind::UnwrapCheck,
        function: function.to_string(),
        location: MirLocation {
            block,
            position: MirPosition::Terminator,
        },
        span: SourceSpan::default(),
        reason: reason.to_string(),
    }
}

/// Helper function to create a SafeOperation for a dead branch (proven-false condition)
#[must_use]
pub fn safe_dead_branch(
    id: u64,
    function: &str,
    block: usize,
    proven_value: u128,
    reason: &str,
) -> SafeOperation {
    SafeOperation {
        id,
        kind: SafeOperationKind::DeadBranch { proven_value },
        function: function.to_string(),
        location: MirLocation {
            block,
            position: MirPosition::Terminator,
        },
        span: SourceSpan::default(),
        reason: reason.to_string(),
    }
}

/// Helper function to create a SafeOperation for refinement specialization
/// Used when a parameter at a call site is proven to satisfy a refinement predicate
#[must_use]
pub fn safe_refinement_specialization(
    id: u64,
    function: &str,
    block: usize,
    callee: &str,
    param_index: Option<usize>,
    predicate: &str,
    reason: &str,
) -> SafeOperation {
    SafeOperation {
        id,
        kind: SafeOperationKind::RefinementSpecialization {
            callee: callee.to_string(),
            param_index,
            predicate: predicate.to_string(),
        },
        function: function.to_string(),
        location: MirLocation {
            block,
            position: MirPosition::Terminator,
        },
        span: SourceSpan::default(),
        reason: reason.to_string(),
    }
}

// =============================================================================
// Unit tests for Phase 9 optimization infrastructure
// =============================================================================

#[cfg(test)]
mod optimization_tests {
    use super::*;

    fn create_test_function_with_checked_add() -> MirFunction {
        MirFunction {
            name: "test_add".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: false,
                        bits: 8,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: false,
                        bits: 8,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: false,
                bits: 8,
            },
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        }),
                        Operand::Copy(Place {
                            local: Local(2),
                            projections: vec![],
                        }),
                    ),
                }],
                terminator: Terminator::Return,
            }],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: false,
                        bits: 8,
                    },
                    name: Some("result".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: false,
                        bits: 8,
                    },
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: false,
                        bits: 8,
                    },
                    name: Some("b".to_string()),
                },
            ],
            span: SourceSpan::default(),
        }
    }

    fn create_test_function_with_bounds_check() -> MirFunction {
        MirFunction {
            name: "test_index".to_string(),
            params: vec![
                (
                    "arr".to_string(),
                    MirType::Array {
                        elem: Box::new(MirType::Int {
                            signed: false,
                            bits: 8,
                        }),
                        len: 10,
                    },
                ),
                (
                    "idx".to_string(),
                    MirType::Int {
                        signed: false,
                        bits: 64,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: false,
                bits: 8,
            },
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Constant(Constant::Bool(true)), // bounds check
                        expected: true,
                        target: 1,
                    },
                },
                BasicBlock {
                    statements: vec![Statement::Assign {
                        place: Place {
                            local: Local(0),
                            projections: vec![],
                        },
                        rvalue: Rvalue::Use(Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![Projection::Index(Local(2))],
                        })),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: false,
                        bits: 8,
                    },
                    name: Some("result".to_string()),
                },
                LocalDecl {
                    ty: MirType::Array {
                        elem: Box::new(MirType::Int {
                            signed: false,
                            bits: 8,
                        }),
                        len: 10,
                    },
                    name: Some("arr".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: false,
                        bits: 64,
                    },
                    name: Some("idx".to_string()),
                },
            ],
            span: SourceSpan::default(),
        }
    }

    #[test]
    fn test_overflow_check_elimination() {
        let func = create_test_function_with_checked_add();

        // Verify the function starts with CheckedBinaryOp
        if let Statement::Assign { rvalue, .. } = &func.blocks[0].statements[0] {
            assert!(matches!(rvalue, Rvalue::CheckedBinaryOp(BinOp::Add, _, _)));
        } else {
            panic!("Expected Assign statement");
        }

        // Create a safe operation that proves overflow is impossible
        let safe_ops = vec![safe_overflow_check(
            1,
            "test_add",
            0,
            0,
            BinOp::Add,
            MirType::Int {
                signed: false,
                bits: 8,
            },
            "precondition a <= 100 && b <= 100 proves no overflow",
        )];

        // Apply optimization
        let pass = OverflowCheckElimination::new();
        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Verify CheckedBinaryOp was converted to BinaryOp
        if let Statement::Assign { rvalue, .. } = &optimized_func.blocks[0].statements[0] {
            assert!(matches!(rvalue, Rvalue::BinaryOp(BinOp::Add, _, _)));
        } else {
            panic!("Expected Assign statement");
        }

        assert_eq!(result.overflow_checks_eliminated, 1);
        assert_eq!(result.applied.len(), 1);
    }

    #[test]
    fn test_overflow_check_not_eliminated_without_proof() {
        let func = create_test_function_with_checked_add();

        // No safe operations - should not optimize
        let safe_ops = vec![];

        let pass = OverflowCheckElimination::new();
        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Should still be CheckedBinaryOp
        if let Statement::Assign { rvalue, .. } = &optimized_func.blocks[0].statements[0] {
            assert!(matches!(rvalue, Rvalue::CheckedBinaryOp(BinOp::Add, _, _)));
        } else {
            panic!("Expected Assign statement");
        }

        assert_eq!(result.overflow_checks_eliminated, 0);
    }

    #[test]
    fn test_bounds_check_elimination() {
        let func = create_test_function_with_bounds_check();

        // Verify the function starts with Assert terminator
        assert!(matches!(
            func.blocks[0].terminator,
            Terminator::Assert { .. }
        ));

        // Create a safe operation that proves bounds are valid
        let safe_ops = vec![safe_bounds_check(
            1,
            "test_index",
            0,
            Some(5),
            Some(10),
            "precondition idx < 10 proves valid index",
        )];

        // Apply optimization
        let pass = BoundsCheckElimination::new();
        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Verify Assert was converted to Goto
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Goto { target: 1 }
        ));

        assert_eq!(result.bounds_checks_eliminated, 1);
        assert_eq!(result.applied.len(), 1);
    }

    #[test]
    fn test_bounds_check_not_eliminated_without_proof() {
        let func = create_test_function_with_bounds_check();

        // No safe operations - should not optimize
        let safe_ops = vec![];

        let pass = BoundsCheckElimination::new();
        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Should still be Assert
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Assert { .. }
        ));

        assert_eq!(result.bounds_checks_eliminated, 0);
    }

    #[test]
    fn test_mir_optimizer_runs_all_passes() {
        let optimizer = MirOptimizer::new();

        assert_eq!(optimizer.pass_names().len(), 6);
        assert!(optimizer
            .pass_names()
            .contains(&"overflow_check_elimination"));
        assert!(optimizer.pass_names().contains(&"bounds_check_elimination"));
        assert!(optimizer.pass_names().contains(&"null_check_elimination"));
        assert!(optimizer
            .pass_names()
            .contains(&"division_check_elimination"));
        assert!(optimizer.pass_names().contains(&"dead_branch_elimination"));
        assert!(optimizer
            .pass_names()
            .contains(&"refinement_specialization"));
    }

    #[test]
    fn test_mir_optimizer_combined_optimization() {
        // Create a function with both overflow and bounds checks
        let mut func = create_test_function_with_bounds_check();

        // Add a statement with CheckedBinaryOp to the second block
        func.blocks[1].statements.insert(
            0,
            Statement::Assign {
                place: Place {
                    local: Local(3),
                    projections: vec![],
                },
                rvalue: Rvalue::CheckedBinaryOp(
                    BinOp::Add,
                    Operand::Constant(Constant::Int(1)),
                    Operand::Constant(Constant::Int(2)),
                ),
            },
        );
        func.locals.push(LocalDecl {
            ty: MirType::Int {
                signed: true,
                bits: 32,
            },
            name: Some("temp".to_string()),
        });

        // Create safe operations for both
        let safe_ops = vec![
            safe_bounds_check(1, "test_index", 0, Some(5), Some(10), "bounds proven safe"),
            safe_overflow_check(
                2,
                "test_index",
                1,
                0,
                BinOp::Add,
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
                "overflow proven safe",
            ),
        ];

        let optimizer = MirOptimizer::new();
        let (optimized_func, result) = optimizer.optimize(func, &safe_ops);

        // Both optimizations should have been applied
        assert_eq!(result.bounds_checks_eliminated, 1);
        assert_eq!(result.overflow_checks_eliminated, 1);
        assert_eq!(result.total_optimizations(), 2);

        // Verify Assert became Goto
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Goto { target: 1 }
        ));

        // Verify CheckedBinaryOp became BinaryOp
        if let Statement::Assign { rvalue, .. } = &optimized_func.blocks[1].statements[0] {
            assert!(matches!(rvalue, Rvalue::BinaryOp(BinOp::Add, _, _)));
        } else {
            panic!("Expected Assign statement");
        }
    }

    #[test]
    fn test_safe_operation_kind_equality() {
        let kind1 = SafeOperationKind::OverflowCheck {
            op: BinOp::Add,
            operand_type: MirType::Int {
                signed: false,
                bits: 8,
            },
        };
        let kind2 = SafeOperationKind::OverflowCheck {
            op: BinOp::Add,
            operand_type: MirType::Int {
                signed: false,
                bits: 8,
            },
        };
        let kind3 = SafeOperationKind::BoundsCheck {
            index_const: Some(5),
            array_len: Some(10),
        };

        assert_eq!(kind1, kind2);
        assert_ne!(kind1, kind3);
    }

    #[test]
    fn test_mir_location_equality() {
        let loc1 = MirLocation {
            block: 0,
            position: MirPosition::Statement(1),
        };
        let loc2 = MirLocation {
            block: 0,
            position: MirPosition::Statement(1),
        };
        let loc3 = MirLocation {
            block: 0,
            position: MirPosition::Terminator,
        };

        assert_eq!(loc1, loc2);
        assert_ne!(loc1, loc3);
    }

    #[test]
    fn test_optimization_result_default() {
        let result = OptimizationResult::default();
        assert_eq!(result.overflow_checks_eliminated, 0);
        assert_eq!(result.bounds_checks_eliminated, 0);
        assert_eq!(result.other_checks_eliminated, 0);
        assert!(result.applied.is_empty());
        assert_eq!(result.total_optimizations(), 0);
    }

    #[test]
    fn test_empty_optimizer() {
        let optimizer = MirOptimizer::empty();
        assert!(optimizer.pass_names().is_empty());

        let func = create_test_function_with_checked_add();
        let safe_ops = vec![safe_overflow_check(
            1,
            "test_add",
            0,
            0,
            BinOp::Add,
            MirType::Int {
                signed: false,
                bits: 8,
            },
            "proven safe",
        )];

        let (_, result) = optimizer.optimize(func, &safe_ops);
        assert_eq!(result.total_optimizations(), 0);
    }

    #[test]
    fn test_division_check_elimination() {
        let func = MirFunction {
            name: "test_div".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: false,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: false,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: false,
                bits: 32,
            },
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Constant(Constant::Bool(true)), // div-by-zero check
                        expected: true,
                        target: 1,
                    },
                },
                BasicBlock {
                    statements: vec![Statement::Assign {
                        place: Place {
                            local: Local(0),
                            projections: vec![],
                        },
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place {
                                local: Local(1),
                                projections: vec![],
                            }),
                            Operand::Copy(Place {
                                local: Local(2),
                                projections: vec![],
                            }),
                        ),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: false,
                        bits: 32,
                    },
                    name: Some("result".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: false,
                        bits: 32,
                    },
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: false,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            span: SourceSpan::default(),
        };

        let safe_ops = vec![safe_division_check(
            1,
            "test_div",
            0,
            "precondition b > 0 proves non-zero divisor",
        )];

        let pass = DivisionCheckElimination::new();
        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Goto { target: 1 }
        ));
        assert_eq!(result.other_checks_eliminated, 1);
    }

    #[test]
    fn test_helper_function_safe_overflow_check() {
        let safe_op = safe_overflow_check(
            42,
            "my_func",
            1,
            2,
            BinOp::Mul,
            MirType::Int {
                signed: true,
                bits: 16,
            },
            "test reason",
        );

        assert_eq!(safe_op.id, 42);
        assert_eq!(safe_op.function, "my_func");
        assert_eq!(safe_op.location.block, 1);
        assert_eq!(safe_op.location.position, MirPosition::Statement(2));
        assert_eq!(safe_op.reason, "test reason");

        if let SafeOperationKind::OverflowCheck { op, operand_type } = &safe_op.kind {
            assert_eq!(*op, BinOp::Mul);
            assert!(matches!(
                operand_type,
                MirType::Int {
                    signed: true,
                    bits: 16
                }
            ));
        } else {
            panic!("Expected OverflowCheck kind");
        }
    }

    #[test]
    fn test_helper_function_safe_bounds_check() {
        let safe_op = safe_bounds_check(
            99,
            "array_access",
            3,
            Some(7),
            Some(100),
            "index proven valid",
        );

        assert_eq!(safe_op.id, 99);
        assert_eq!(safe_op.function, "array_access");
        assert_eq!(safe_op.location.block, 3);
        assert_eq!(safe_op.location.position, MirPosition::Terminator);

        if let SafeOperationKind::BoundsCheck {
            index_const,
            array_len,
        } = &safe_op.kind
        {
            assert_eq!(*index_const, Some(7));
            assert_eq!(*array_len, Some(100));
        } else {
            panic!("Expected BoundsCheck kind");
        }
    }

    // Phase 9.2: Null Check Elimination Tests

    fn create_test_function_with_option_unwrap() -> MirFunction {
        // Simulates: fn unwrap_option(opt: Option<i32>) -> i32 { opt.unwrap() }
        // MIR generates an Assert terminator for the Some check
        MirFunction {
            name: "unwrap_option".to_string(),
            params: vec![(
                "opt".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Constant(Constant::Bool(true)), // discriminant == 1 (Some)
                        expected: true,
                        target: 1,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("result".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("opt".to_string()),
                },
            ],
            span: SourceSpan::default(),
        }
    }

    fn create_test_function_with_result_unwrap() -> MirFunction {
        // Simulates: fn unwrap_result(res: Result<i32, E>) -> i32 { res.unwrap() }
        MirFunction {
            name: "unwrap_result".to_string(),
            params: vec![(
                "res".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Constant(Constant::Bool(true)), // discriminant == 0 (Ok)
                        expected: true,
                        target: 1,
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("result".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("res".to_string()),
                },
            ],
            span: SourceSpan::default(),
        }
    }

    #[test]
    fn test_null_check_elimination_with_option() {
        let func = create_test_function_with_option_unwrap();

        // Safe operation: precondition ensures opt.is_some()
        let safe_ops = vec![safe_unwrap_check(
            1,
            "unwrap_option",
            0,
            "precondition opt.is_some() proves Some variant",
        )];

        let pass = NullCheckElimination::new();
        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Assert was converted to Goto
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Goto { target: 1 }
        ));
        assert_eq!(result.null_checks_eliminated, 1);
        assert_eq!(result.applied.len(), 1);
        assert!(result.applied[0]
            .description
            .contains("Eliminated unwrap check"));
    }

    #[test]
    fn test_null_check_elimination_with_result() {
        let func = create_test_function_with_result_unwrap();

        // Safe operation: precondition ensures res.is_ok()
        let safe_ops = vec![safe_unwrap_check(
            1,
            "unwrap_result",
            0,
            "precondition res.is_ok() proves Ok variant",
        )];

        let pass = NullCheckElimination::new();
        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Assert was converted to Goto
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Goto { target: 1 }
        ));
        assert_eq!(result.null_checks_eliminated, 1);
    }

    #[test]
    fn test_null_check_elimination_no_safe_ops() {
        let func = create_test_function_with_option_unwrap();
        let safe_ops = vec![]; // No proof - should not optimize

        let pass = NullCheckElimination::new();
        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Assert should remain unchanged
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Assert { target: 1, .. }
        ));
        assert_eq!(result.null_checks_eliminated, 0);
    }

    #[test]
    fn test_null_check_elimination_wrong_block() {
        let func = create_test_function_with_option_unwrap();

        // Safe operation for wrong block (block 1, not block 0)
        let safe_ops = vec![safe_unwrap_check(
            1,
            "unwrap_option",
            1, // Wrong block!
            "precondition proves Some variant",
        )];

        let pass = NullCheckElimination::new();
        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Assert should remain unchanged since safe_op is for wrong block
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Assert { target: 1, .. }
        ));
        assert_eq!(result.null_checks_eliminated, 0);
    }

    #[test]
    fn test_helper_function_safe_unwrap_check() {
        let safe_op = safe_unwrap_check(55, "test_unwrap", 2, "option proven Some");

        assert_eq!(safe_op.id, 55);
        assert_eq!(safe_op.function, "test_unwrap");
        assert_eq!(safe_op.location.block, 2);
        assert_eq!(safe_op.location.position, MirPosition::Terminator);
        assert_eq!(safe_op.reason, "option proven Some");
        assert!(matches!(safe_op.kind, SafeOperationKind::UnwrapCheck));
    }

    #[test]
    fn test_mir_optimizer_includes_null_check_elimination() {
        let optimizer = MirOptimizer::new();

        // Verify NullCheckElimination is included in default passes
        let func = create_test_function_with_option_unwrap();
        let safe_ops = vec![safe_unwrap_check(
            1,
            "unwrap_option",
            0,
            "precondition proves Some variant",
        )];

        let (optimized_func, result) = optimizer.optimize(func, &safe_ops);

        // The optimizer should have applied null check elimination
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Goto { target: 1 }
        ));
        assert_eq!(result.null_checks_eliminated, 1);
    }

    #[test]
    fn test_optimization_result_total_includes_null_checks() {
        let mut result = OptimizationResult::new();
        result.overflow_checks_eliminated = 2;
        result.bounds_checks_eliminated = 3;
        result.null_checks_eliminated = 1;
        result.other_checks_eliminated = 4;

        assert_eq!(result.total_optimizations(), 10);
    }

    // =========================================================================
    // Dead Branch Elimination Tests (Phase 9.4)
    // =========================================================================

    fn create_test_function_with_switch() -> MirFunction {
        // Create a function with a SwitchInt terminator (boolean condition)
        // if (cond) { block1 } else { block2 }
        MirFunction {
            name: "test_branch".to_string(),
            params: vec![("cond".to_string(), MirType::Bool)],
            return_type: MirType::Int {
                signed: false,
                bits: 32,
            },
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: false,
                        bits: 32,
                    },
                    name: None,
                }, // return
                LocalDecl {
                    ty: MirType::Bool,
                    name: Some("cond".to_string()),
                }, // cond arg
            ],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        }),
                        targets: vec![(1, 1)], // if cond == 1 (true) goto block 1
                        otherwise: 2,          // else goto block 2
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            span: SourceSpan::default(),
        }
    }

    #[test]
    fn test_dead_branch_elimination_with_switch() {
        let func = create_test_function_with_switch();
        let pass = DeadBranchElimination::new();

        // Prove that the condition is always 1 (true)
        let safe_ops = vec![safe_dead_branch(
            1,
            "test_branch",
            0, // block 0 has the switch
            1, // proven value is 1 (true)
            "condition proven always true",
        )];

        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Should have eliminated one branch
        assert_eq!(result.dead_branches_eliminated, 1);
        assert_eq!(result.total_optimizations(), 1);

        // The terminator should now be Goto to block 1
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Goto { target: 1 }
        ));
    }

    #[test]
    fn test_dead_branch_elimination_to_otherwise() {
        let func = create_test_function_with_switch();
        let pass = DeadBranchElimination::new();

        // Prove that the condition is always 0 (false)
        // 0 is not in targets, so it goes to otherwise (block 2)
        let safe_ops = vec![safe_dead_branch(
            1,
            "test_branch",
            0, // block 0 has the switch
            0, // proven value is 0 (false)
            "condition proven always false",
        )];

        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Should have eliminated one branch
        assert_eq!(result.dead_branches_eliminated, 1);

        // The terminator should now be Goto to block 2 (otherwise)
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Goto { target: 2 }
        ));
    }

    #[test]
    fn test_dead_branch_elimination_no_safe_ops() {
        let func = create_test_function_with_switch();
        let pass = DeadBranchElimination::new();

        // No safe operations
        let (optimized_func, result) = pass.optimize(func, &[]);

        // Should not have eliminated anything
        assert_eq!(result.dead_branches_eliminated, 0);

        // The terminator should still be SwitchInt
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::SwitchInt { .. }
        ));
    }

    #[test]
    fn test_dead_branch_elimination_wrong_block() {
        let func = create_test_function_with_switch();
        let pass = DeadBranchElimination::new();

        // Safe operation for a different block
        let safe_ops = vec![safe_dead_branch(
            1,
            "test_branch",
            5, // wrong block
            1,
            "wrong block",
        )];

        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Should not have eliminated anything (block doesn't exist)
        assert_eq!(result.dead_branches_eliminated, 0);

        // The terminator should still be SwitchInt
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::SwitchInt { .. }
        ));
    }

    #[test]
    fn test_helper_function_safe_dead_branch() {
        let safe_op = safe_dead_branch(42, "my_function", 7, 99, "proven by SMT solver");

        assert_eq!(safe_op.id, 42);
        assert_eq!(safe_op.function, "my_function");
        assert_eq!(safe_op.location.block, 7);
        assert!(matches!(safe_op.location.position, MirPosition::Terminator));
        assert_eq!(safe_op.reason, "proven by SMT solver");

        if let SafeOperationKind::DeadBranch { proven_value } = safe_op.kind {
            assert_eq!(proven_value, 99);
        } else {
            panic!("Expected DeadBranch kind");
        }
    }

    #[test]
    fn test_mir_optimizer_includes_dead_branch_elimination() {
        let optimizer = MirOptimizer::new();

        // Verify DeadBranchElimination is included in default passes
        let func = create_test_function_with_switch();
        let safe_ops = vec![safe_dead_branch(
            1,
            "test_branch",
            0,
            1,
            "condition proven true",
        )];

        let (optimized_func, result) = optimizer.optimize(func, &safe_ops);

        // Dead branch elimination should have been applied
        assert_eq!(result.dead_branches_eliminated, 1);
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Goto { target: 1 }
        ));
    }

    #[test]
    fn test_optimization_result_total_includes_dead_branches() {
        let mut result = OptimizationResult::new();
        result.overflow_checks_eliminated = 2;
        result.bounds_checks_eliminated = 3;
        result.null_checks_eliminated = 1;
        result.dead_branches_eliminated = 5;
        result.other_checks_eliminated = 4;

        assert_eq!(result.total_optimizations(), 15);
    }

    // =========================================================================
    // Refinement Specialization Tests (Phase 9.4)
    // =========================================================================

    fn create_test_function_with_call() -> MirFunction {
        MirFunction {
            name: "caller_function".to_string(),
            params: vec![(
                "n".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "abs".to_string(),
                        args: vec![Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        })],
                        destination: Place {
                            local: Local(0),
                            projections: vec![],
                        },
                        target: 1,
                        span: SourceSpan::default(),
                        generic_args: vec![],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            locals: vec![
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("_0".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("n".to_string()),
                },
            ],
            span: SourceSpan::default(),
        }
    }

    #[test]
    fn test_refinement_specialization_with_call() {
        let func = create_test_function_with_call();
        let pass = RefinementSpecialization::new();

        // Prove that parameter 0 at the call site satisfies "n > 0"
        let safe_ops = vec![safe_refinement_specialization(
            1,
            "caller_function",
            0, // block index
            "abs",
            Some(0),   // parameter index
            "(> n 0)", // predicate in SMT-LIB format
            "proven by SMT solver",
        )];

        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Should have recorded one refinement specialization
        assert_eq!(result.refinements_specialized, 1);
        assert_eq!(result.total_optimizations(), 1);
        assert_eq!(result.applied.len(), 1);

        // The call should still be there (no transformation yet, just recording)
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Call { .. }
        ));

        // Check the applied optimization description
        assert!(result.applied[0].description.contains("abs"));
        assert!(result.applied[0].description.contains("param 0"));
        assert!(result.applied[0].description.contains("(> n 0)"));
    }

    #[test]
    fn test_refinement_specialization_no_safe_ops() {
        let func = create_test_function_with_call();
        let pass = RefinementSpecialization::new();

        // No safe operations
        let (optimized_func, result) = pass.optimize(func, &[]);

        // Should not have recorded any specialization
        assert_eq!(result.refinements_specialized, 0);
        assert_eq!(result.total_optimizations(), 0);

        // The call should still be there
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Call { .. }
        ));
    }

    #[test]
    fn test_refinement_specialization_wrong_block() {
        let func = create_test_function_with_call();
        let pass = RefinementSpecialization::new();

        // Safe operation for a different block
        let safe_ops = vec![safe_refinement_specialization(
            1,
            "caller_function",
            5, // wrong block
            "abs",
            Some(0),
            "(> n 0)",
            "wrong block",
        )];

        let (optimized_func, result) = pass.optimize(func, &safe_ops);

        // Should not have recorded any specialization
        assert_eq!(result.refinements_specialized, 0);

        // The call should still be there
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Call { .. }
        ));
    }

    #[test]
    fn test_refinement_specialization_self_parameter() {
        let func = create_test_function_with_call();
        let pass = RefinementSpecialization::new();

        // Prove that self (receiver) satisfies a predicate
        let safe_ops = vec![safe_refinement_specialization(
            1,
            "caller_function",
            0,
            "Vec::push",
            None, // None indicates self/receiver
            "(> len(self) 0)",
            "proven by SMT solver",
        )];

        let (_optimized_func, result) = pass.optimize(func, &safe_ops);

        // Should have recorded one refinement specialization
        assert_eq!(result.refinements_specialized, 1);

        // Check the applied optimization description uses "self" for None
        assert!(result.applied[0].description.contains("self"));
        assert!(result.applied[0].description.contains("Vec::push"));
    }

    #[test]
    fn test_helper_function_safe_refinement_specialization() {
        let safe_op = safe_refinement_specialization(
            42,
            "my_caller",
            7,
            "target_func",
            Some(2),
            "(>= x 0)",
            "proven by SMT",
        );

        assert_eq!(safe_op.id, 42);
        assert_eq!(safe_op.function, "my_caller");
        assert_eq!(safe_op.location.block, 7);
        assert!(matches!(safe_op.location.position, MirPosition::Terminator));
        assert_eq!(safe_op.reason, "proven by SMT");

        if let SafeOperationKind::RefinementSpecialization {
            callee,
            param_index,
            predicate,
        } = &safe_op.kind
        {
            assert_eq!(callee, "target_func");
            assert_eq!(*param_index, Some(2));
            assert_eq!(predicate, "(>= x 0)");
        } else {
            panic!("Expected RefinementSpecialization kind");
        }
    }

    #[test]
    fn test_mir_optimizer_includes_refinement_specialization() {
        let optimizer = MirOptimizer::new();

        // Verify RefinementSpecialization is included in default passes
        let func = create_test_function_with_call();
        let safe_ops = vec![safe_refinement_specialization(
            1,
            "caller_function",
            0,
            "abs",
            Some(0),
            "(> n 0)",
            "condition proven",
        )];

        let (optimized_func, result) = optimizer.optimize(func, &safe_ops);

        // Refinement specialization should have been recorded
        assert_eq!(result.refinements_specialized, 1);
        assert!(matches!(
            optimized_func.blocks[0].terminator,
            Terminator::Call { .. }
        ));
    }

    #[test]
    fn test_optimization_result_total_includes_refinements() {
        let mut result = OptimizationResult::new();
        result.overflow_checks_eliminated = 2;
        result.bounds_checks_eliminated = 3;
        result.null_checks_eliminated = 1;
        result.dead_branches_eliminated = 5;
        result.refinements_specialized = 7;
        result.other_checks_eliminated = 4;

        assert_eq!(result.total_optimizations(), 22);
    }

    // Tests for Phase 6.5.2: Monomorphized generics resolution

    #[test]
    fn test_mir_type_display_primitives() {
        assert_eq!(MirType::Bool.to_string(), "bool");
        assert_eq!(
            MirType::Int {
                signed: true,
                bits: 32
            }
            .to_string(),
            "i32"
        );
        assert_eq!(
            MirType::Int {
                signed: false,
                bits: 64
            }
            .to_string(),
            "u64"
        );
        assert_eq!(MirType::Float { bits: 64 }.to_string(), "f64");
    }

    #[test]
    fn test_mir_type_display_compound() {
        let int_type = MirType::Int {
            signed: true,
            bits: 32,
        };
        let ref_type = MirType::Ref {
            mutable: false,
            inner: Box::new(int_type.clone()),
        };
        assert_eq!(ref_type.to_string(), "&i32");

        let mut_ref = MirType::Ref {
            mutable: true,
            inner: Box::new(int_type.clone()),
        };
        assert_eq!(mut_ref.to_string(), "&mut i32");

        let array_type = MirType::Array {
            elem: Box::new(int_type.clone()),
            len: 10,
        };
        assert_eq!(array_type.to_string(), "[i32; 10]");

        let tuple_type = MirType::Tuple(vec![
            MirType::Int {
                signed: true,
                bits: 32,
            },
            MirType::Bool,
        ]);
        assert_eq!(tuple_type.to_string(), "(i32, bool)");
    }

    #[test]
    fn test_mir_type_display_adt() {
        let adt = MirType::Adt {
            name: "String".to_string(),
        };
        assert_eq!(adt.to_string(), "String");

        let fn_ptr = MirType::FnPtr {
            params: vec![MirType::Int {
                signed: true,
                bits: 32,
            }],
            ret: Box::new(MirType::Bool),
        };
        assert_eq!(fn_ptr.to_string(), "fn(i32) -> bool");
    }

    #[test]
    fn test_monomorphized_name_no_generics() {
        assert_eq!(monomorphized_name("foo", &[]), "foo");
        assert_eq!(monomorphized_name("Option::map", &[]), "Option::map");
    }

    #[test]
    fn test_monomorphized_name_with_generics() {
        let args = vec![MirType::Int {
            signed: true,
            bits: 32,
        }];
        assert_eq!(monomorphized_name("Vec::push", &args), "Vec::push<i32>");

        let args = vec![
            MirType::Int {
                signed: true,
                bits: 32,
            },
            MirType::Bool,
        ];
        assert_eq!(
            monomorphized_name("Option::map", &args),
            "Option::map<i32, bool>"
        );
    }

    #[test]
    fn test_monomorphized_name_complex_types() {
        let fn_arg = MirType::FnPtr {
            params: vec![MirType::Int {
                signed: true,
                bits: 32,
            }],
            ret: Box::new(MirType::Bool),
        };
        let args = vec![
            MirType::Adt {
                name: "String".to_string(),
            },
            fn_arg,
        ];
        assert_eq!(
            monomorphized_name("Iterator::map", &args),
            "Iterator::map<String, fn(i32) -> bool>"
        );
    }

    #[test]
    fn test_terminator_call_with_generic_args() {
        // Verify that Call terminator can carry generic args
        let terminator = Terminator::Call {
            func: "Option::map".to_string(),
            args: vec![],
            destination: Place {
                local: Local(0),
                projections: vec![],
            },
            target: 1,
            span: SourceSpan::default(),
            generic_args: vec![
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
                MirType::FnPtr {
                    params: vec![MirType::Int {
                        signed: true,
                        bits: 32,
                    }],
                    ret: Box::new(MirType::Bool),
                },
            ],
        };

        if let Terminator::Call {
            func, generic_args, ..
        } = &terminator
        {
            assert_eq!(func, "Option::map");
            assert_eq!(generic_args.len(), 2);
            let mono_name = monomorphized_name(func, generic_args);
            assert_eq!(mono_name, "Option::map<i32, fn(i32) -> bool>");
        }
    }
}
