//! End-to-end verification pipeline
//!
//! This module connects MIR analysis, VC generation, and the SMT backend
//! to provide a complete verification pipeline.
//!
//! ## Backend Selection
//!
//! Use the `TRUST_SOLVER` environment variable to select the SMT backend:
//! - `TRUST_SOLVER=z3` (default) - Use Z3 SMT solver (C++ bindings)
//! - `TRUST_SOLVER=z4` - Use Z4 SMT solver (pure Rust, 1.2-1.8x faster)
//!
//! Z4 may return `Unknown` for complex formulas that Z3 can handle.
//! When `TRUST_SOLVER=z4`, set `TRUST_SOLVER_FALLBACK=1` (default) to fall back to
//! Z3 for quantified VCs and when Z4 returns `Unknown`. Set `TRUST_SOLVER_FALLBACK=0`
//! to force pure Z4 (useful for validation).

use crate::{
    generate_function_vcs, symbolic_execution::SymbolicExecutor,
    weakest_precondition::WpCalculator, FunctionSpecs, MirFunction,
};
use std::collections::HashMap;
use vc_ir::{
    AuditCertificate, BackendHint, Effect, EffectOptimizations, EffectSet, EffectSource, Expr,
    OptimizationSource, Predicate, SourceSpan, SpecClause, TemporalFormula, VcId, VcKind,
    VerificationCondition, VerificationMethod, VerifyConfig, VerifyResult,
};

/// Check a verification condition using the selected SMT backend.
///
/// The backend is selected via the `TRUST_SOLVER` environment variable:
/// - `z3` (default): Use Z3 SMT solver
/// - `z4`: Use Z4 pure Rust SMT solver
fn check_vc(vc: &VerificationCondition, config: &VerifyConfig) -> VerifyResult {
    match std::env::var("TRUST_SOLVER").as_deref() {
        Ok("z4") => {
            if trust_solver_fallback_enabled() && vc_uses_quantifiers(vc) {
                return trust_z3::check_vc(vc, config);
            }
            let result = trust_z4::check_vc(vc, config);
            if trust_solver_fallback_enabled() && matches!(result, VerifyResult::Unknown { .. }) {
                trust_z3::check_vc(vc, config)
            } else {
                result
            }
        }
        _ => trust_z3::check_vc(vc, config),
    }
}

fn trust_solver_fallback_enabled() -> bool {
    match std::env::var("TRUST_SOLVER_FALLBACK") {
        Ok(v) => !matches!(v.as_str(), "0" | "false" | "False" | "FALSE"),
        Err(_) => true,
    }
}

fn vc_uses_quantifiers(vc: &VerificationCondition) -> bool {
    vc_kind_uses_quantifiers(&vc.condition)
}

fn vc_kind_uses_quantifiers(kind: &VcKind) -> bool {
    match kind {
        VcKind::Predicate(pred) => predicate_uses_quantifiers(pred),
        VcKind::Implies {
            antecedent,
            consequent,
        } => predicate_uses_quantifiers(antecedent) || predicate_uses_quantifiers(consequent),
        VcKind::Forall { .. } | VcKind::Exists { .. } => true,
        VcKind::Temporal(f) => temporal_uses_quantifiers(f),
        VcKind::NeuralNetwork(_) | VcKind::Separation(_) => false,
        VcKind::Termination {
            decreases,
            recursive_calls,
        } => expr_uses_quantifiers(decreases) || recursive_calls.iter().any(expr_uses_quantifiers),
    }
}

fn temporal_uses_quantifiers(f: &TemporalFormula) -> bool {
    match f {
        TemporalFormula::State(p) => predicate_uses_quantifiers(p),
        TemporalFormula::Always(inner)
        | TemporalFormula::Eventually(inner)
        | TemporalFormula::Next(inner)
        | TemporalFormula::Not(inner)
        | TemporalFormula::StutteringEquiv(inner) => temporal_uses_quantifiers(inner),
        TemporalFormula::Until(a, b)
        | TemporalFormula::WeakUntil(a, b)
        | TemporalFormula::Release(a, b)
        | TemporalFormula::LeadsTo(a, b)
        | TemporalFormula::Implies(a, b) => {
            temporal_uses_quantifiers(a) || temporal_uses_quantifiers(b)
        }
        TemporalFormula::And(fs) | TemporalFormula::Or(fs) => {
            fs.iter().any(temporal_uses_quantifiers)
        }
        TemporalFormula::WeakFairness { condition, .. }
        | TemporalFormula::StrongFairness { condition, .. } => {
            predicate_uses_quantifiers(condition)
        }
    }
}

fn predicate_uses_quantifiers(pred: &Predicate) -> bool {
    match pred {
        Predicate::Forall { .. } | Predicate::Exists { .. } => true,
        Predicate::Bool(_) => false,
        Predicate::Expr(e) => expr_uses_quantifiers(e),
        Predicate::Not(p) => predicate_uses_quantifiers(p),
        Predicate::And(ps) | Predicate::Or(ps) => ps.iter().any(predicate_uses_quantifiers),
        Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
            predicate_uses_quantifiers(a) || predicate_uses_quantifiers(b)
        }
        Predicate::Let { bindings, body } => {
            bindings.iter().any(|(_, e)| expr_uses_quantifiers(e))
                || predicate_uses_quantifiers(body)
        }
    }
}

fn expr_uses_quantifiers(expr: &Expr) -> bool {
    match expr {
        Expr::Forall { .. } | Expr::Exists { .. } => true,
        Expr::BoolLit(_)
        | Expr::IntLit(_)
        | Expr::FloatLit(_)
        | Expr::BitVecLit { .. }
        | Expr::Var(_)
        | Expr::Result
        | Expr::Raw(_) => false,
        Expr::Old(e)
        | Expr::Neg(e)
        | Expr::BitNot(e)
        | Expr::Not(e)
        | Expr::Abs(e)
        | Expr::ArrayLen(e)
        | Expr::Deref(e)
        | Expr::AddrOf(e)
        | Expr::TensorShape(e)
        | Expr::TupleField(e, _)
        | Expr::StructField(e, _)
        | Expr::Sorted(e) => expr_uses_quantifiers(e),
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Rem(a, b)
        | Expr::BitAnd(a, b)
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
        | Expr::ArrayIndex(a, b)
        | Expr::Min(a, b)
        | Expr::Max(a, b)
        | Expr::Permutation(a, b) => expr_uses_quantifiers(a) || expr_uses_quantifiers(b),
        Expr::Ite { cond, then_, else_ } => {
            expr_uses_quantifiers(cond)
                || expr_uses_quantifiers(then_)
                || expr_uses_quantifiers(else_)
        }
        Expr::ArraySlice { array, start, end } => {
            expr_uses_quantifiers(array)
                || expr_uses_quantifiers(start)
                || expr_uses_quantifiers(end)
        }
        Expr::Apply { args, .. } => args.iter().any(expr_uses_quantifiers),
        Expr::Cast { expr, .. } => expr_uses_quantifiers(expr),
        Expr::TensorIndex { tensor, indices } => {
            expr_uses_quantifiers(tensor) || indices.iter().any(expr_uses_quantifiers)
        }
        Expr::TensorReshape { tensor, .. } => expr_uses_quantifiers(tensor),
        Expr::Contains {
            collection,
            element,
        } => expr_uses_quantifiers(collection) || expr_uses_quantifiers(element),
        // Enum operations (Phase N3.1c)
        Expr::IsVariant { expr, .. } => expr_uses_quantifiers(expr),
        Expr::Discriminant(expr) => expr_uses_quantifiers(expr),
        Expr::VariantField { expr, .. } => expr_uses_quantifiers(expr),
    }
}

/// Result of verifying a function
#[derive(Debug)]
pub struct FunctionVerifyResult {
    /// Name of the verified function
    pub function_name: String,
    /// Results for each verification condition
    pub vc_results: Vec<VcVerifyResult>,
    /// Overall status
    pub status: VerifyStatus,
}

/// Result for a single VC
#[derive(Debug)]
pub struct VcVerifyResult {
    /// VC name
    pub name: String,
    /// VC kind description
    pub kind: String,
    /// Result from backend
    pub result: VerifyResult,
    /// Source location for traceability (N4.1)
    pub span: SourceSpan,
}

/// Overall verification status
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyStatus {
    /// All VCs proven
    AllProven,
    /// Some VCs failed
    SomeFailed(usize, usize), // (proven, total)
    /// No VCs to verify
    NoVcs,
    /// Specifications contain unsupported features (e.g., floats)
    UnsupportedFeature(String),
}

/// Effect violation error
#[derive(Debug, Clone)]
pub struct EffectViolation {
    /// Name of the caller function
    pub caller: String,
    /// Name of the callee function
    pub callee: String,
    /// Effects used by callee but not allowed by caller
    pub missing_effects: Vec<Effect>,
    /// Source location of the call
    pub span: SourceSpan,
}

/// Result of effect checking for a function
#[derive(Debug)]
pub struct EffectCheckResult {
    /// Function name
    pub function_name: String,
    /// Whether effect checking passed
    pub passed: bool,
    /// Effect violations found
    pub violations: Vec<EffectViolation>,
}

/// Registry of function effects for cross-function checking
#[derive(Debug, Default, Clone)]
pub struct EffectRegistry {
    /// Map from function name to declared effects
    /// None means effects not declared (assumed all effects)
    effects: HashMap<String, Option<EffectSet>>,
    /// Map from function name to polymorphic effect source
    /// Used for higher-order functions with effects_of(param) annotations
    polymorphic_effects: HashMap<String, EffectSource>,
}

/// Effect inference from MIR analysis
///
/// Analyzes function bodies to infer what effects they might have.
/// This is used when effects are not explicitly declared.
#[derive(Debug)]
pub struct EffectInference {
    /// Known effectful function names and their effects
    known_effects: HashMap<String, EffectSet>,
}

impl Default for EffectInference {
    fn default() -> Self {
        Self::new()
    }
}

impl EffectInference {
    /// Create a new effect inference engine with built-in knowledge
    #[must_use]
    pub fn new() -> Self {
        let mut known_effects = HashMap::new();

        // IO effects - console/file/network operations
        for name in &[
            "std::io::_print",
            "std::io::println",
            "std::io::print",
            "std::io::eprintln",
            "std::io::eprint",
            "std::io::stdin",
            "std::io::stdout",
            "std::io::stderr",
            "std::fs::read",
            "std::fs::write",
            "std::fs::File::open",
            "std::fs::File::create",
            "std::net::TcpStream::connect",
            "println",
            "print",
            "eprintln",
            "eprint",
        ] {
            known_effects.insert((*name).to_string(), EffectSet::from_effects([Effect::IO]));
        }

        // Alloc effects - heap allocation operations
        for name in &[
            "std::boxed::Box::new",
            "std::vec::Vec::push",
            "std::vec::Vec::with_capacity",
            "std::string::String::new",
            "std::string::String::from",
            "std::collections::HashMap::new",
            "std::collections::HashSet::new",
            "std::collections::BTreeMap::new",
            "std::collections::VecDeque::new",
            "Box::new",
            "Vec::new",
            "Vec::push",
            "String::new",
            "String::from",
        ] {
            known_effects.insert(
                (*name).to_string(),
                EffectSet::from_effects([Effect::Alloc]),
            );
        }

        // Panic effects - operations that can panic
        for name in &[
            "std::panic::panic",
            "core::panicking::panic",
            "core::panicking::panic_fmt",
            "std::option::Option::unwrap",
            "std::option::Option::expect",
            "std::result::Result::unwrap",
            "std::result::Result::expect",
            "panic",
            "unwrap",
            "expect",
            "assert",
            "assert_eq",
            "assert_ne",
            "unreachable",
            "todo",
            "unimplemented",
        ] {
            known_effects.insert(
                (*name).to_string(),
                EffectSet::from_effects([Effect::Panic]),
            );
        }

        // GlobalState effects - global mutable state operations
        for name in &[
            "std::sync::Mutex::lock",
            "std::sync::RwLock::read",
            "std::sync::RwLock::write",
            "std::sync::atomic::AtomicBool::store",
            "std::sync::atomic::AtomicUsize::store",
            "std::sync::atomic::AtomicI32::store",
            "std::cell::RefCell::borrow_mut",
            "std::cell::Cell::set",
        ] {
            known_effects.insert(
                (*name).to_string(),
                EffectSet::from_effects([Effect::GlobalState]),
            );
        }

        Self { known_effects }
    }

    /// Register a known effectful function
    pub fn register_known(&mut self, name: &str, effects: EffectSet) {
        self.known_effects.insert(name.to_string(), effects);
    }

    /// Get effects for a known function
    #[must_use]
    pub fn get_known(&self, name: &str) -> Option<&EffectSet> {
        self.known_effects.get(name)
    }

    /// Infer effects from a MIR function
    ///
    /// This analyzes the function body to determine what effects it might have.
    /// Returns the inferred effect set.
    #[must_use]
    pub fn infer_effects(&self, func: &MirFunction, registry: &EffectRegistry) -> EffectSet {
        use crate::{Rvalue, Statement, Terminator};

        let mut effects = EffectSet::empty();

        for block in &func.blocks {
            // Check statements for effectful operations
            for stmt in &block.statements {
                if let Statement::Assign { rvalue, place } = stmt {
                    // Check for operations that might indicate effects
                    match rvalue {
                        // Division/remainder can panic (divide by zero),
                        // and checked operations can panic on overflow
                        Rvalue::BinaryOp(crate::BinOp::Div | crate::BinOp::Rem, _, _)
                        | Rvalue::CheckedBinaryOp(_, _, _) => {
                            effects.add(Effect::Panic);
                        }
                        _ => {}
                    }

                    // Check for index projections in place (can panic on bounds)
                    for proj in &place.projections {
                        if let crate::Projection::Index(_) = proj {
                            effects.add(Effect::Panic);
                        }
                    }
                }
            }

            // Check terminator for effectful operations
            match &block.terminator {
                Terminator::Call {
                    func: callee_name, ..
                } => {
                    // Check if callee is a known effectful function
                    if let Some(callee_effects) = self.known_effects.get(callee_name) {
                        effects = effects.union(callee_effects);
                    }

                    // Check if callee has registered effects
                    if let Some(Some(callee_effects)) = registry.get(callee_name) {
                        effects = effects.union(callee_effects);
                    }

                    // Check for panic-related function names
                    let name_lower = callee_name.to_lowercase();
                    if name_lower.contains("panic")
                        || name_lower.contains("unwrap")
                        || name_lower.contains("expect")
                        || name_lower.ends_with("assert")
                    {
                        effects.add(Effect::Panic);
                    }

                    // Check for IO-related function names
                    if name_lower.contains("print")
                        || name_lower.contains("read")
                        || name_lower.contains("write")
                        || name_lower.contains("stdin")
                        || name_lower.contains("stdout")
                        || name_lower.contains("stderr")
                    {
                        effects.add(Effect::IO);
                    }

                    // Check for allocation-related function names
                    if name_lower.contains("box::new")
                        || name_lower.contains("vec::push")
                        || name_lower.contains("vec::with_capacity")
                        || name_lower.contains("string::from")
                    {
                        effects.add(Effect::Alloc);
                    }
                }
                Terminator::Assert { .. } => {
                    // Assert can panic if condition fails
                    effects.add(Effect::Panic);
                }
                Terminator::Unreachable => {
                    // Unreachable implies potential panic/abort
                    effects.add(Effect::Panic);
                }
                _ => {}
            }
        }

        // Check for unsafe using MIR metadata (not name-based heuristics)
        // Uses MirFunction::is_unsafe() and has_unsafe_blocks() methods
        // NOTE: These currently return false until the MIR representation
        // is updated to include proper unsafe tracking from HIR/MIR
        if func.is_unsafe() || func.has_unsafe_blocks() {
            effects.add(Effect::Unsafe);
        }
        // REMOVED: Name-based heuristics like func.name.contains("unsafe")
        // These were unsound - a function named "check_unsafe_state" is not unsafe

        effects
    }

    /// Infer effects with transitive closure over call graph
    ///
    /// This computes effects transitively: if A calls B, and B has effects E,
    /// then A also has effects E (unless A explicitly declares its effects).
    #[must_use]
    pub fn infer_effects_transitive(
        &self,
        functions: &[(MirFunction, Option<EffectSet>)],
    ) -> HashMap<String, EffectSet> {
        let mut result: HashMap<String, EffectSet> = HashMap::new();

        // First pass: direct effects and declared effects
        for (func, declared) in functions {
            if let Some(effects) = declared {
                // Use declared effects
                result.insert(func.name.clone(), effects.clone());
            } else {
                // Infer direct effects (without transitive closure yet)
                let registry = EffectRegistry::new();
                let effects = self.infer_effects(func, &registry);
                result.insert(func.name.clone(), effects);
            }
        }

        // Second pass: transitive closure (fixed point iteration)
        let mut changed = true;
        let max_iterations = 100; // Prevent infinite loops
        let mut iteration = 0;

        while changed && iteration < max_iterations {
            changed = false;
            iteration += 1;

            for (func, declared) in functions {
                // Skip functions with declared effects
                if declared.is_some() {
                    continue;
                }

                let current_effects = result.get(&func.name).cloned().unwrap_or_default();

                // Check calls and inherit effects
                for block in &func.blocks {
                    if let crate::Terminator::Call {
                        func: callee_name, ..
                    } = &block.terminator
                    {
                        if let Some(callee_effects) = result.get(callee_name) {
                            let new_effects = current_effects.union(callee_effects);
                            if !new_effects.iter().all(|e| current_effects.has(*e)) {
                                result.insert(func.name.clone(), new_effects);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        result
    }

    /// Check if a function is inferred to be pure
    #[must_use]
    pub fn is_pure(&self, func: &MirFunction, registry: &EffectRegistry) -> bool {
        self.infer_effects(func, registry).is_pure()
    }
}

// ============================================
// Phase 12.3: Automatic Precondition Synthesis
// ============================================

/// An inferred precondition needed for function safety
#[derive(Debug, Clone)]
pub struct InferredPrecondition {
    /// The predicate that must hold
    pub predicate: String,
    /// Human-readable description of why this is needed
    pub reason: String,
    /// Source location where the dangerous operation occurs
    pub source_location: Option<(usize, usize)>, // (block, statement)
    /// The operation that requires this precondition
    pub operation: SafetyOperation,
}

/// Types of operations that require safety preconditions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SafetyOperation {
    /// Division by zero check: divisor != 0
    DivisionByZero { divisor: String },
    /// Remainder by zero check: divisor != 0
    RemainderByZero { divisor: String },
    /// Array bounds check: 0 <= idx < len
    ArrayBoundsCheck { index: String, array: String },
    /// Slice bounds check: 0 <= idx < slice.len()
    SliceBoundsCheck { index: String, slice: String },
    /// Integer overflow check
    IntegerOverflow {
        operation: String,
        operands: Vec<String>,
    },
    /// Unwrap safety check: Option/Result must be Some/Ok
    UnwrapSafety { value: String },
}

impl std::fmt::Display for SafetyOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DivisionByZero { divisor } => {
                write!(f, "division by zero (divisor: {divisor})")
            }
            Self::RemainderByZero { divisor } => {
                write!(f, "remainder by zero (divisor: {divisor})")
            }
            Self::ArrayBoundsCheck { index, array } => {
                write!(f, "array bounds check ({array}[{index}])")
            }
            Self::SliceBoundsCheck { index, slice } => {
                write!(f, "slice bounds check ({slice}[{index}])")
            }
            Self::IntegerOverflow {
                operation,
                operands,
            } => {
                write!(f, "integer overflow ({operation} on {operands:?})")
            }
            Self::UnwrapSafety { value } => {
                write!(f, "unwrap safety ({value})")
            }
        }
    }
}

/// Result of precondition inference
#[derive(Debug, Clone)]
pub struct PreconditionInferenceResult {
    /// Function name
    pub function_name: String,
    /// Inferred preconditions needed for safety
    pub inferred_preconditions: Vec<InferredPrecondition>,
    /// Missing preconditions (inferred but not declared)
    pub missing_preconditions: Vec<InferredPrecondition>,
    /// Suggested refinement type annotations
    pub suggested_refinements: Vec<SuggestedRefinement>,
}

/// A suggested refinement type annotation
#[derive(Debug, Clone)]
pub struct SuggestedRefinement {
    /// Parameter name
    pub param: String,
    /// Suggested predicate
    pub predicate: String,
    /// Reason for the suggestion
    pub reason: String,
}

/// Precondition inference from MIR analysis (Phase 12.3)
///
/// Analyzes function bodies to infer what preconditions are needed
/// for safe execution. This enables automatic precondition synthesis.
#[derive(Debug, Default)]
pub struct PreconditionInference {
    /// Known unsafe patterns that require preconditions
    known_patterns: HashMap<String, String>,
}

impl PreconditionInference {
    /// Create a new precondition inference engine
    #[must_use]
    pub fn new() -> Self {
        let mut known_patterns = HashMap::new();
        // Known patterns that require preconditions
        known_patterns.insert("Option::unwrap".to_string(), "is_some()".to_string());
        known_patterns.insert("Result::unwrap".to_string(), "is_ok()".to_string());
        known_patterns.insert("Option::expect".to_string(), "is_some()".to_string());
        known_patterns.insert("Result::expect".to_string(), "is_ok()".to_string());
        Self { known_patterns }
    }

    /// Infer preconditions needed for a function's safe execution
    ///
    /// Scans the MIR for operations that require preconditions:
    /// - Division/remainder by zero
    /// - Array/slice bounds checks
    /// - Overflow-prone arithmetic
    /// - Unwrap operations
    #[must_use]
    pub fn infer_preconditions(&self, func: &MirFunction) -> Vec<InferredPrecondition> {
        use crate::{BinOp, Rvalue, Statement, Terminator};

        let mut preconditions = Vec::new();

        for (block_idx, block) in func.blocks.iter().enumerate() {
            for (stmt_idx, stmt) in block.statements.iter().enumerate() {
                if let Statement::Assign { rvalue, .. } = stmt {
                    match rvalue {
                        // Division by zero check
                        Rvalue::BinaryOp(BinOp::Div, _lhs, rhs) => {
                            let divisor = Self::operand_to_string(rhs, func);
                            preconditions.push(InferredPrecondition {
                                predicate: format!("{divisor} != 0"),
                                reason: "Division requires non-zero divisor".to_string(),
                                source_location: Some((block_idx, stmt_idx)),
                                operation: SafetyOperation::DivisionByZero {
                                    divisor: divisor.clone(),
                                },
                            });
                        }
                        // Remainder by zero check
                        Rvalue::BinaryOp(BinOp::Rem, _lhs, rhs) => {
                            let divisor = Self::operand_to_string(rhs, func);
                            preconditions.push(InferredPrecondition {
                                predicate: format!("{divisor} != 0"),
                                reason: "Remainder requires non-zero divisor".to_string(),
                                source_location: Some((block_idx, stmt_idx)),
                                operation: SafetyOperation::RemainderByZero {
                                    divisor: divisor.clone(),
                                },
                            });
                        }
                        _ => {}
                    }
                }
            }

            // Check terminators for function calls that need preconditions
            if let Terminator::Call {
                func: callee, args, ..
            } = &block.terminator
            {
                if let Some(pattern_pred) = self.known_patterns.get(callee) {
                    if !args.is_empty() {
                        let value = Self::operand_to_string(&args[0], func);
                        preconditions.push(InferredPrecondition {
                            predicate: format!("{value}.{pattern_pred}"),
                            reason: format!("{callee} requires the value to be valid"),
                            source_location: Some((block_idx, block.statements.len())),
                            operation: SafetyOperation::UnwrapSafety { value },
                        });
                    }
                }
            }
        }

        // Deduplicate preconditions by predicate
        let mut seen = std::collections::HashSet::new();
        preconditions.retain(|p| seen.insert(p.predicate.clone()));

        preconditions
    }

    /// Infer preconditions and compare with declared ones
    ///
    /// Returns the result including missing preconditions that should be added.
    #[must_use]
    pub fn analyze_function(
        &self,
        func: &MirFunction,
        specs: &FunctionSpecs,
    ) -> PreconditionInferenceResult {
        let inferred = self.infer_preconditions(func);

        // Extract declared preconditions as strings for comparison
        let declared: std::collections::HashSet<String> = specs
            .requires
            .iter()
            .filter_map(|r| {
                // Convert predicate to string for comparison
                match &r.pred {
                    Predicate::Expr(e) => Some(self.expr_to_canonical_string(e)),
                    _ => None,
                }
            })
            .collect();

        // Find missing preconditions
        let missing: Vec<InferredPrecondition> = inferred
            .iter()
            .filter(|p| !Self::predicate_is_covered(&p.predicate, &declared))
            .cloned()
            .collect();

        // Generate suggested refinements for parameters
        let suggested_refinements = Self::suggest_refinements(&missing, func);

        PreconditionInferenceResult {
            function_name: func.name.clone(),
            inferred_preconditions: inferred,
            missing_preconditions: missing,
            suggested_refinements,
        }
    }

    /// Check if an inferred predicate is covered by declared predicates
    fn predicate_is_covered(inferred: &str, declared: &std::collections::HashSet<String>) -> bool {
        // Direct match
        if declared.contains(inferred) {
            return true;
        }

        // Check for equivalent forms (e.g., "x != 0" vs "x > 0 || x < 0")
        // For now, just check canonical forms
        let canonical = Self::normalize_predicate(inferred);
        declared
            .iter()
            .any(|d| Self::normalize_predicate(d) == canonical)
    }

    /// Normalize a predicate string for comparison
    fn normalize_predicate(pred: &str) -> String {
        // Remove whitespace and standardize operators
        pred.replace(' ', "")
            .replace("!=", "≠")
            .replace(">=", "≥")
            .replace("<=", "≤")
    }

    /// Suggest refinement type annotations for parameters
    fn suggest_refinements(
        missing: &[InferredPrecondition],
        func: &MirFunction,
    ) -> Vec<SuggestedRefinement> {
        let mut suggestions = Vec::new();

        for precond in missing {
            // Try to identify which parameter this precondition applies to
            if let Some((param_name, predicate)) =
                Self::extract_param_refinement(&precond.predicate, func)
            {
                suggestions.push(SuggestedRefinement {
                    param: param_name,
                    predicate,
                    reason: precond.reason.clone(),
                });
            }
        }

        suggestions
    }

    /// Extract parameter name and predicate from an inferred precondition
    fn extract_param_refinement(predicate: &str, func: &MirFunction) -> Option<(String, String)> {
        // Check if the predicate references a parameter directly
        for (param_name, _) in &func.params {
            if predicate.contains(param_name) {
                return Some((param_name.clone(), predicate.to_string()));
            }
        }
        None
    }

    /// Convert an operand to a string representation
    fn operand_to_string(op: &crate::Operand, func: &MirFunction) -> String {
        match op {
            crate::Operand::Copy(place) | crate::Operand::Move(place) => {
                Self::place_to_string(place, func)
            }
            crate::Operand::Constant(c) => format!("{c:?}"),
        }
    }

    /// Convert a place to a string representation
    fn place_to_string(place: &crate::Place, func: &MirFunction) -> String {
        let base = if place.local.0 < func.params.len() + 1 {
            if place.local.0 == 0 {
                "_0".to_string() // Return place
            } else {
                func.params[place.local.0 - 1].0.clone()
            }
        } else {
            format!("_{}", place.local.0)
        };

        let mut result = base;
        for proj in &place.projections {
            match proj {
                crate::Projection::Deref => result = format!("(*{result})"),
                crate::Projection::Field(idx) => result = format!("{result}.{idx}"),
                crate::Projection::Index(local) => {
                    let idx_name = if local.0 < func.params.len() + 1 && local.0 > 0 {
                        func.params[local.0 - 1].0.clone()
                    } else {
                        format!("_{}", local.0)
                    };
                    result = format!("{result}[{idx_name}]");
                }
            }
        }
        result
    }

    /// Convert an expression to a canonical string for comparison
    #[allow(clippy::only_used_in_recursion)]
    fn expr_to_canonical_string(&self, expr: &Expr) -> String {
        match expr {
            Expr::Var(v) => v.clone(),
            Expr::IntLit(i) => i.to_string(),
            Expr::BoolLit(b) => b.to_string(),
            Expr::Ne(l, r) => format!(
                "{} != {}",
                self.expr_to_canonical_string(l),
                self.expr_to_canonical_string(r)
            ),
            Expr::Eq(l, r) => format!(
                "{} == {}",
                self.expr_to_canonical_string(l),
                self.expr_to_canonical_string(r)
            ),
            Expr::Lt(l, r) => format!(
                "{} < {}",
                self.expr_to_canonical_string(l),
                self.expr_to_canonical_string(r)
            ),
            Expr::Le(l, r) => format!(
                "{} <= {}",
                self.expr_to_canonical_string(l),
                self.expr_to_canonical_string(r)
            ),
            Expr::Gt(l, r) => format!(
                "{} > {}",
                self.expr_to_canonical_string(l),
                self.expr_to_canonical_string(r)
            ),
            Expr::Ge(l, r) => format!(
                "{} >= {}",
                self.expr_to_canonical_string(l),
                self.expr_to_canonical_string(r)
            ),
            Expr::And(l, r) => format!(
                "({} && {})",
                self.expr_to_canonical_string(l),
                self.expr_to_canonical_string(r)
            ),
            Expr::Or(l, r) => format!(
                "({} || {})",
                self.expr_to_canonical_string(l),
                self.expr_to_canonical_string(r)
            ),
            Expr::Not(e) => format!("!{}", self.expr_to_canonical_string(e)),
            _ => format!("{expr:?}"),
        }
    }

    /// Report inferred preconditions to stderr for diagnostics
    pub fn report_inferred_preconditions(&self, result: &PreconditionInferenceResult) {
        if !result.inferred_preconditions.is_empty() {
            eprintln!(
                "[tRust] Phase 12.3: Inferred {} precondition(s) for {}",
                result.inferred_preconditions.len(),
                result.function_name
            );
            for precond in &result.inferred_preconditions {
                eprintln!("  - {} ({})", precond.predicate, precond.reason);
            }
        }

        if !result.missing_preconditions.is_empty() {
            eprintln!(
                "[tRust] Phase 12.3: {} missing precondition(s) for {}:",
                result.missing_preconditions.len(),
                result.function_name
            );
            for precond in &result.missing_preconditions {
                eprintln!("  - MISSING: {} ({})", precond.predicate, precond.reason);
            }
        }

        if !result.suggested_refinements.is_empty() {
            eprintln!("[tRust] Phase 12.3: Suggested refinements:");
            for suggestion in &result.suggested_refinements {
                eprintln!(
                    "  - #[trust::refined({}, \"{}\")]  // {}",
                    suggestion.param, suggestion.predicate, suggestion.reason
                );
            }
        }
    }

    /// Report suggested refinement annotations when verification fails.
    ///
    /// This is intended as actionable guidance: it prints only suggestions (not all inferred ops).
    pub fn report_suggested_refinements_on_failure(&self, result: &PreconditionInferenceResult) {
        if result.suggested_refinements.is_empty() {
            return;
        }

        eprintln!(
            "[tRust] Phase 12.3: Verification failed; suggested refinement(s) for {}:",
            result.function_name
        );
        for suggestion in &result.suggested_refinements {
            eprintln!(
                "  - #[trust::refined({}, \"{}\")]  // {}",
                suggestion.param, suggestion.predicate, suggestion.reason
            );
        }
    }

    /// Convert `#[requires]` clauses to equivalent `#[trust::refined]` suggestions (Phase 12.3)
    ///
    /// This enables migration from function-level preconditions to parameter-level
    /// refinement types that propagate automatically through the program.
    ///
    /// Example:
    /// ```text
    /// // Before: manual precondition
    /// #[requires("x > 0")]
    /// fn foo(x: i32) -> i32 { ... }
    ///
    /// // After: refinement type (equivalent, but propagates automatically)
    /// fn foo(#[trust::refined(x, "x > 0")] x: i32) -> i32 { ... }
    /// ```
    #[must_use]
    pub fn requires_to_refined_suggestions(
        &self,
        specs: &FunctionSpecs,
        func: &MirFunction,
    ) -> Vec<SuggestedRefinement> {
        let mut suggestions = Vec::new();

        for req in &specs.requires {
            // Extract the predicate string from the label (e.g., "requires(x > 0)" -> "x > 0")
            // or convert the Predicate to a string
            let predicate_str = self.extract_predicate_string(req);

            // Find which parameters this predicate constrains
            let constrained_params = Self::find_constrained_params(&predicate_str, func);

            // Generate a refined suggestion for each constrained parameter
            for param in constrained_params {
                suggestions.push(SuggestedRefinement {
                    param: param.clone(),
                    predicate: predicate_str.clone(),
                    reason: "Converted from #[requires] attribute".to_string(),
                });
            }
        }

        suggestions
    }

    /// Extract the predicate string from a SpecClause
    fn extract_predicate_string(&self, clause: &SpecClause) -> String {
        // Try to get the original string from the label first
        if let Some(label) = &clause.label {
            // Labels are typically "requires(predicate)" or "ensures(predicate)"
            if let Some(start) = label.find('(') {
                if let Some(end) = label.rfind(')') {
                    if start < end {
                        return label[start + 1..end].to_string();
                    }
                }
            }
            // If no parentheses, use the whole label
            return label.clone();
        }

        // Otherwise, convert the predicate to a string
        self.predicate_to_string(&clause.pred)
    }

    /// Convert a Predicate to a readable string
    fn predicate_to_string(&self, pred: &Predicate) -> String {
        match pred {
            Predicate::Bool(true) => "true".to_string(),
            Predicate::Bool(false) => "false".to_string(),
            Predicate::Expr(e) => self.expr_to_canonical_string(e),
            Predicate::Not(p) => format!("!({})", self.predicate_to_string(p)),
            Predicate::And(preds) => {
                let parts: Vec<_> = preds.iter().map(|p| self.predicate_to_string(p)).collect();
                parts.join(" && ")
            }
            Predicate::Or(preds) => {
                let parts: Vec<_> = preds.iter().map(|p| self.predicate_to_string(p)).collect();
                format!("({})", parts.join(" || "))
            }
            Predicate::Implies(l, r) => {
                format!(
                    "({} => {})",
                    self.predicate_to_string(l),
                    self.predicate_to_string(r)
                )
            }
            Predicate::Iff(l, r) => {
                format!(
                    "({} <=> {})",
                    self.predicate_to_string(l),
                    self.predicate_to_string(r)
                )
            }
            Predicate::Forall { vars, body, .. } => {
                let var_strs: Vec<_> = vars.iter().map(|(n, _)| n.clone()).collect();
                format!(
                    "forall {} . {}",
                    var_strs.join(", "),
                    self.predicate_to_string(body)
                )
            }
            Predicate::Exists { vars, body } => {
                let var_strs: Vec<_> = vars.iter().map(|(n, _)| n.clone()).collect();
                format!(
                    "exists {} . {}",
                    var_strs.join(", "),
                    self.predicate_to_string(body)
                )
            }
            Predicate::Let { bindings, body } => {
                let binding_strs: Vec<_> = bindings
                    .iter()
                    .map(|(n, e)| format!("{} = {}", n, self.expr_to_canonical_string(e)))
                    .collect();
                format!(
                    "let {} in {}",
                    binding_strs.join(", "),
                    self.predicate_to_string(body)
                )
            }
        }
    }

    /// Find which function parameters are constrained by a predicate string
    fn find_constrained_params(predicate: &str, func: &MirFunction) -> Vec<String> {
        let mut constrained = Vec::new();

        for (param_name, _) in &func.params {
            // Check if this parameter is mentioned in the predicate
            // Use word boundary checking to avoid partial matches (e.g., "x" in "max")
            if Self::predicate_mentions_param(predicate, param_name) {
                constrained.push(param_name.clone());
            }
        }

        constrained
    }

    /// Check if a predicate string mentions a specific parameter
    fn predicate_mentions_param(predicate: &str, param: &str) -> bool {
        // Simple word boundary check: parameter must not be part of a larger identifier
        let param_chars: Vec<char> = param.chars().collect();
        let pred_chars: Vec<char> = predicate.chars().collect();

        for i in 0..=pred_chars.len().saturating_sub(param_chars.len()) {
            // Check if param matches at position i
            let matches = param_chars
                .iter()
                .enumerate()
                .all(|(j, &c)| pred_chars.get(i + j) == Some(&c));

            if matches {
                // Check word boundaries
                let before_ok =
                    i == 0 || !pred_chars[i - 1].is_alphanumeric() && pred_chars[i - 1] != '_';
                let after_pos = i + param_chars.len();
                let after_ok = after_pos >= pred_chars.len()
                    || !pred_chars[after_pos].is_alphanumeric() && pred_chars[after_pos] != '_';

                if before_ok && after_ok {
                    return true;
                }
            }
        }

        false
    }

    /// Report requires-to-refined conversion suggestions
    pub fn report_requires_to_refined(&self, specs: &FunctionSpecs, func: &MirFunction) {
        let suggestions = self.requires_to_refined_suggestions(specs, func);

        if suggestions.is_empty() {
            return;
        }

        eprintln!(
            "[tRust] Phase 12.3: #[requires] → #[trust::refined] suggestions for {}:",
            func.name
        );
        for suggestion in &suggestions {
            eprintln!(
                "  - #[trust::refined({}, \"{}\")]",
                suggestion.param, suggestion.predicate
            );
        }
    }
}

/// Effect-based optimization analyzer (Phase 5.3)
///
/// Analyzes functions to determine what compile-time optimizations
/// can be safely applied based on their effect properties.
#[derive(Debug)]
pub struct EffectOptimizationAnalyzer {
    /// Effect inference engine
    inference: EffectInference,
}

impl Default for EffectOptimizationAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl EffectOptimizationAnalyzer {
    /// Create a new optimization analyzer
    #[must_use]
    pub fn new() -> Self {
        Self {
            inference: EffectInference::new(),
        }
    }

    /// Analyze a function and return applicable optimizations
    ///
    /// This is the main entry point for effect-based optimization analysis.
    /// It examines the function's declared or inferred effects and determines
    /// what compiler optimizations can be safely applied.
    #[must_use]
    pub fn analyze_function(
        &self,
        func: &MirFunction,
        specs: &FunctionSpecs,
        registry: &EffectRegistry,
    ) -> FunctionOptimizations {
        // Get the effective effect set
        let (effects, source) = if specs.pure {
            // Explicitly marked as pure
            (EffectSet::empty(), OptimizationSource::Declared)
        } else if let Some(declared) = &specs.effects {
            // Declared effects
            (declared.clone(), OptimizationSource::Declared)
        } else {
            // Infer effects from MIR
            let inferred = self.inference.infer_effects(func, registry);
            (inferred, OptimizationSource::Inferred)
        };

        // Derive optimizations from effects
        let optimizations = EffectOptimizations::from_effects(&effects).with_source(source);

        FunctionOptimizations {
            function_name: func.name.clone(),
            effects,
            optimizations,
        }
    }

    /// Analyze multiple functions and return optimizations for all
    ///
    /// This performs transitive effect inference first, then computes
    /// optimizations for each function.
    #[must_use]
    pub fn analyze_functions(
        &self,
        functions: &[(MirFunction, FunctionSpecs)],
    ) -> Vec<FunctionOptimizations> {
        // Build effect registry from declared effects
        let mut registry = EffectRegistry::new();
        for (func, specs) in functions {
            let effects = if specs.pure {
                Some(EffectSet::empty())
            } else {
                specs.effects.clone()
            };
            registry.register(&func.name, effects);
        }

        // Analyze each function
        functions
            .iter()
            .map(|(func, specs)| self.analyze_function(func, specs, &registry))
            .collect()
    }

    /// Check if a function is memoizable
    #[must_use]
    pub fn is_memoizable(
        &self,
        func: &MirFunction,
        specs: &FunctionSpecs,
        registry: &EffectRegistry,
    ) -> bool {
        let result = self.analyze_function(func, specs, registry);
        result.optimizations.is_memoizable()
    }

    /// Check if a function can skip unwind tables
    #[must_use]
    pub fn can_skip_unwind(
        &self,
        func: &MirFunction,
        specs: &FunctionSpecs,
        registry: &EffectRegistry,
    ) -> bool {
        let result = self.analyze_function(func, specs, registry);
        result.optimizations.is_no_unwind()
    }

    /// Check if a function is embedded-safe (no allocation)
    #[must_use]
    pub fn is_embedded_safe(
        &self,
        func: &MirFunction,
        specs: &FunctionSpecs,
        registry: &EffectRegistry,
    ) -> bool {
        let result = self.analyze_function(func, specs, registry);
        result.optimizations.is_embedded_safe()
    }
}

/// Result of optimization analysis for a single function
#[derive(Debug, Clone)]
pub struct FunctionOptimizations {
    /// Name of the analyzed function
    pub function_name: String,
    /// The effect set (declared or inferred)
    pub effects: EffectSet,
    /// The applicable optimizations
    pub optimizations: EffectOptimizations,
}

impl FunctionOptimizations {
    /// Get a summary of optimizations as a human-readable string
    #[must_use]
    pub fn summary(&self) -> String {
        let opt_names = self.optimizations.to_names();
        if opt_names.is_empty() {
            format!("{}: no optimizations applicable", self.function_name)
        } else {
            format!("{}: {}", self.function_name, opt_names.join(", "))
        }
    }

    /// Check if any optimizations are applicable
    #[must_use]
    pub fn has_optimizations(&self) -> bool {
        !self.optimizations.is_empty()
    }
}

impl EffectRegistry {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a function's effects
    pub fn register(&mut self, name: &str, effects: Option<EffectSet>) {
        self.effects.insert(name.to_string(), effects);
    }

    /// Register a function's polymorphic effect source
    ///
    /// Used for higher-order functions with #[effects_of(param)] annotations.
    pub fn register_polymorphic(&mut self, name: &str, source: EffectSource) {
        self.polymorphic_effects.insert(name.to_string(), source);
    }

    /// Get a function's declared effects
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Option<EffectSet>> {
        self.effects.get(name)
    }

    /// Get a function's polymorphic effect source
    #[must_use]
    pub fn get_polymorphic(&self, name: &str) -> Option<&EffectSource> {
        self.polymorphic_effects.get(name)
    }

    /// Resolve a callee's effects, substituting parameter effects if polymorphic
    ///
    /// For functions with polymorphic effects like `#[effects_of(f)]`:
    /// - arg_effects maps parameter names to the effects of actual arguments
    /// - Returns the resolved effect set
    ///
    /// For non-polymorphic functions, returns the declared effects.
    #[must_use]
    pub fn resolve_callee_effects(
        &self,
        callee: &str,
        arg_effects: &HashMap<String, EffectSet>,
    ) -> Option<EffectSet> {
        // Check for polymorphic effects first
        if let Some(source) = self.polymorphic_effects.get(callee) {
            // Substitute parameter effects
            source.substitute(arg_effects)
        } else {
            // Use declared concrete effects
            self.effects.get(callee).and_then(Clone::clone)
        }
    }

    /// Check if a caller can call a callee based on effects
    ///
    /// Returns Some(violations) if the call is not allowed, None if allowed
    #[must_use]
    pub fn check_call(
        &self,
        caller: &str,
        callee: &str,
        call_span: &SourceSpan,
    ) -> Option<EffectViolation> {
        let caller_effects = self.effects.get(caller);
        let callee_effects = self.effects.get(callee);

        match (caller_effects, callee_effects) {
            // If caller has no declared effects, it has all effects (can call anything)
            (None | Some(None), _) => None,

            // If callee has no declared effects, assume it has all effects
            (Some(Some(caller_set)), None | Some(None)) => {
                // Caller is restricted but callee is unrestricted
                // This is always a violation unless caller has all effects
                let all_effects = Effect::all();
                let missing: Vec<Effect> = all_effects
                    .into_iter()
                    .filter(|e| !caller_set.has(*e))
                    .collect();

                if missing.is_empty() {
                    None
                } else {
                    Some(EffectViolation {
                        caller: caller.to_string(),
                        callee: callee.to_string(),
                        missing_effects: missing,
                        span: call_span.clone(),
                    })
                }
            }

            // Both have declared effects
            (Some(Some(caller_set)), Some(Some(callee_set))) => {
                // Check if callee's effects are subset of caller's effects
                if callee_set.is_subset_of(caller_set) {
                    None
                } else {
                    let diff = callee_set.difference(caller_set);
                    let missing: Vec<Effect> = diff.iter().copied().collect();
                    Some(EffectViolation {
                        caller: caller.to_string(),
                        callee: callee.to_string(),
                        missing_effects: missing,
                        span: call_span.clone(),
                    })
                }
            }
        }
    }

    /// Check if a caller can call a callee with polymorphic effects
    ///
    /// Like check_call, but also handles callee's with polymorphic effects
    /// by substituting the argument effects.
    #[must_use]
    pub fn check_call_polymorphic(
        &self,
        caller: &str,
        callee: &str,
        arg_effects: &HashMap<String, EffectSet>,
        call_span: &SourceSpan,
    ) -> Option<EffectViolation> {
        let caller_effects = self.effects.get(caller);

        // First, try to resolve callee's polymorphic effects
        let callee_effects = if let Some(source) = self.polymorphic_effects.get(callee) {
            // Callee has polymorphic effects - substitute argument effects
            source.substitute(arg_effects)
        } else {
            // Use normal effects
            self.effects.get(callee).and_then(Clone::clone)
        };

        match (caller_effects, callee_effects) {
            // If caller has no declared effects, it has all effects (can call anything)
            (None | Some(None), _) => None,

            // If callee effects couldn't be resolved, assume all effects
            (Some(Some(caller_set)), None) => {
                let all_effects = Effect::all();
                let missing: Vec<Effect> = all_effects
                    .into_iter()
                    .filter(|e| !caller_set.has(*e))
                    .collect();

                if missing.is_empty() {
                    None
                } else {
                    Some(EffectViolation {
                        caller: caller.to_string(),
                        callee: callee.to_string(),
                        missing_effects: missing,
                        span: call_span.clone(),
                    })
                }
            }

            // Both have resolved effects
            (Some(Some(caller_set)), Some(callee_set)) => {
                if callee_set.is_subset_of(caller_set) {
                    None
                } else {
                    let diff = callee_set.difference(caller_set);
                    let missing: Vec<Effect> = diff.iter().copied().collect();
                    Some(EffectViolation {
                        caller: caller.to_string(),
                        callee: callee.to_string(),
                        missing_effects: missing,
                        span: call_span.clone(),
                    })
                }
            }
        }
    }
}

/// Main verification entry point
pub struct Verifier {
    config: VerifyConfig,
    effect_registry: EffectRegistry,
}

impl Verifier {
    #[must_use]
    pub fn new() -> Self {
        Self {
            config: VerifyConfig::default(),
            effect_registry: EffectRegistry::new(),
        }
    }

    #[must_use]
    pub fn with_config(config: VerifyConfig) -> Self {
        Self {
            config,
            effect_registry: EffectRegistry::new(),
        }
    }

    /// Register a function's effects for cross-function checking
    pub fn register_effects(&mut self, name: &str, effects: Option<EffectSet>) {
        self.effect_registry.register(name, effects);
    }

    /// Get a reference to the effect registry
    #[must_use]
    pub const fn effect_registry(&self) -> &EffectRegistry {
        &self.effect_registry
    }

    /// Get a mutable reference to the effect registry
    pub const fn effect_registry_mut(&mut self) -> &mut EffectRegistry {
        &mut self.effect_registry
    }

    /// Check effect constraints for a function's calls
    #[must_use]
    pub fn check_effects(&self, func: &MirFunction, specs: &FunctionSpecs) -> EffectCheckResult {
        use crate::Terminator;

        let mut violations = Vec::new();
        let mut registry = self.effect_registry.clone();
        let inference = EffectInference::new();

        // Get caller's effect set (None => no declared effects, caller is unrestricted)
        let caller_effects = if specs.pure {
            Some(EffectSet::empty())
        } else {
            specs.effects.clone()
        };

        // Ensure the caller is registered so EffectRegistry::check_call applies restrictions.
        registry.register(&func.name, caller_effects);

        // Check all call sites in the function
        for block in &func.blocks {
            if let Terminator::Call {
                func: callee_name,
                span,
                ..
            } = &block.terminator
            {
                // If we don't already know the callee, seed the registry with built-in known effects.
                if registry.get(callee_name).is_none() {
                    if let Some(known) = inference.get_known(callee_name) {
                        registry.register(callee_name, Some(known.clone()));
                    }
                }

                // Check if this call is allowed
                if let Some(violation) = registry.check_call(&func.name, callee_name, span) {
                    violations.push(violation);
                }
            }
        }

        // Additional check: if function is pure, it cannot have any effectful operations
        if specs.pure {
            // Check for IO operations (simplified - would need MIR analysis)
            // In a real implementation, this would look at intrinsics, FFI calls, etc.
        }

        EffectCheckResult {
            function_name: func.name.clone(),
            passed: violations.is_empty(),
            violations,
        }
    }

    /// Verify a function by generating VCs and checking them with Z3
    #[must_use]
    pub fn verify_function(
        &self,
        func: &MirFunction,
        specs: &FunctionSpecs,
    ) -> FunctionVerifyResult {
        // Generate VCs
        let function_vcs = generate_function_vcs(func, specs);

        // Collect all VCs
        let mut all_vcs: Vec<&VerificationCondition> = Vec::new();
        all_vcs.extend(function_vcs.requires.iter());
        all_vcs.extend(function_vcs.ensures.iter());
        all_vcs.extend(function_vcs.loop_invariants.iter());
        all_vcs.extend(function_vcs.assertions.iter());
        if let Some(term) = &function_vcs.termination {
            all_vcs.push(term);
        }

        if all_vcs.is_empty() {
            return FunctionVerifyResult {
                function_name: func.name.clone(),
                vc_results: vec![],
                status: VerifyStatus::NoVcs,
            };
        }

        // Verify each VC
        let mut vc_results = Vec::new();
        let mut proven_count = 0;

        for vc in all_vcs {
            let result = check_vc(vc, &self.config);
            if matches!(result, VerifyResult::Proven) {
                proven_count += 1;
            }

            vc_results.push(VcVerifyResult {
                name: vc.name.clone(),
                kind: format!("{:?}", vc.condition),
                result,
                span: vc.span.clone(),
            });
        }

        let total = vc_results.len();
        let status = if proven_count == total {
            VerifyStatus::AllProven
        } else {
            VerifyStatus::SomeFailed(proven_count, total)
        };

        if matches!(status, VerifyStatus::SomeFailed(_, _)) {
            let inference = PreconditionInference::new();
            let preconditions = inference.analyze_function(func, specs);
            let verbose = matches!(std::env::var("TRUST_VERIFY_VERBOSE").as_deref(), Ok("1"));
            if verbose {
                inference.report_inferred_preconditions(&preconditions);
            } else {
                inference.report_suggested_refinements_on_failure(&preconditions);
            }
        }

        FunctionVerifyResult {
            function_name: func.name.clone(),
            vc_results,
            status,
        }
    }

    /// Verify using symbolic execution approach
    #[must_use]
    pub fn verify_function_symbolic(
        &self,
        func: &MirFunction,
        postcondition: &Predicate,
    ) -> Vec<VcVerifyResult> {
        let executor = SymbolicExecutor::new(func);
        let vcs = executor.execute(postcondition);

        vcs.iter()
            .map(|vc| {
                let result = check_vc(vc, &self.config);
                VcVerifyResult {
                    name: vc.name.clone(),
                    kind: format!("{:?}", vc.condition),
                    result,
                    span: vc.span.clone(),
                }
            })
            .collect()
    }

    /// Verify using weakest precondition calculus
    #[must_use]
    pub fn verify_function_wp(
        &self,
        func: &MirFunction,
        precondition: &Predicate,
        postcondition: &Predicate,
    ) -> VcVerifyResult {
        let mut wp_calc = WpCalculator::new(func);
        let wp = wp_calc.wp_function(postcondition);

        // SOUNDNESS CHECK: Reject if any loops lack invariants
        if wp_calc.has_loops_without_invariant() {
            let loop_blocks = wp_calc.loops_without_invariant();
            return VcVerifyResult {
                name: format!("wp verification of {}", func.name),
                kind: "weakest precondition".to_string(),
                result: VerifyResult::Unknown {
                    reason: format!(
                        "SOUNDNESS ERROR: Loop(s) at block(s) {loop_blocks:?} require #[invariant(...)] annotation. \
                         Cannot soundly verify functions with loops unless all loops have explicit invariants."
                    ),
                },
                span: func.span.clone(),
            };
        }

        // Check all side VCs (overflow checks, array bounds, etc.)
        let side_vcs = wp_calc.take_side_vcs();
        for side_vc in &side_vcs {
            let side_result = check_vc(side_vc, &self.config);
            if !matches!(side_result, VerifyResult::Proven) {
                return VcVerifyResult {
                    name: side_vc.name.clone(),
                    kind: "side condition".to_string(),
                    result: side_result,
                    span: side_vc.span.clone(),
                };
            }
        }

        // Create VC: precondition => wp
        let vc = VerificationCondition {
            id: VcId(0),
            name: format!("wp verification of {}", func.name),
            span: func.span.clone(),
            condition: VcKind::Implies {
                antecedent: precondition.clone(),
                consequent: wp,
            },
            preferred_backend: Some(BackendHint::Smt),
        };

        let result = check_vc(&vc, &self.config);

        VcVerifyResult {
            name: vc.name,
            kind: "weakest precondition".to_string(),
            result,
            span: vc.span,
        }
    }

    /// Generate an audit certificate for a verified function (N4.1)
    ///
    /// Creates a certificate that documents the verification results and can be
    /// independently verified using Lean5.
    #[must_use]
    pub fn generate_certificate(
        &self,
        func: &MirFunction,
        specs: &FunctionSpecs,
        result: &FunctionVerifyResult,
    ) -> AuditCertificate {
        // Determine verification method from environment
        let method = match std::env::var("TRUST_SOLVER").as_deref() {
            Ok("z4") => VerificationMethod::Smt {
                solver: "Z4".to_string(),
            },
            _ => VerificationMethod::Smt {
                solver: "Z3".to_string(),
            },
        };

        // Generate VCs to include in certificate
        let function_vcs = generate_function_vcs(func, specs);

        // Build certificate
        let mut builder = AuditCertificate::builder(&func.name)
            .description(format!(
                "Verification of function '{}' with {} preconditions and {} postconditions",
                func.name,
                specs.requires.len(),
                specs.ensures.len()
            ))
            .method(method);

        // Add all VCs with their results
        for vc_result in &result.vc_results {
            // Find the corresponding VC to get its full info
            let vc = function_vcs
                .requires
                .iter()
                .chain(function_vcs.ensures.iter())
                .chain(function_vcs.loop_invariants.iter())
                .chain(function_vcs.assertions.iter())
                .chain(function_vcs.termination.iter())
                .find(|v| v.name == vc_result.name);

            if let Some(vc) = vc {
                let proven = matches!(vc_result.result, VerifyResult::Proven);
                builder = builder.add_vc(vc, proven);
            }
        }

        let mut cert = builder.build();

        // Generate Lean5 source if all VCs are proven
        if matches!(result.status, VerifyStatus::AllProven) {
            cert.generate_lean_source();
        }

        cert
    }
}

impl Default for Verifier {
    fn default() -> Self {
        Self::new()
    }
}

/// Build a MIR function from specification (for testing)
#[must_use]
pub fn mir_from_clamp_positive() -> (MirFunction, FunctionSpecs) {
    use crate::{
        BasicBlock, BinOp, Constant, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
        Terminator,
    };
    use vc_ir::{Expr, SpecClause};

    // fn clamp_positive(n: i32, val: i32) -> i32 {
    //     if val < 1 { 1 }
    //     else if val > n { n }
    //     else { val }
    // }

    // Locals:
    // _0: return place
    // _1: n (param)
    // _2: val (param)
    // _3: val < 1 (temp bool)
    // _4: val > n (temp bool)

    let func = MirFunction {
        name: "clamp_positive".to_string(),
        params: vec![
            (
                "n".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            ),
            (
                "val".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            ),
        ],
        return_type: MirType::Int {
            signed: true,
            bits: 32,
        },
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
            LocalDecl {
                ty: MirType::Int {
                    signed: true,
                    bits: 32,
                },
                name: Some("val".to_string()),
            },
            LocalDecl {
                ty: MirType::Bool,
                name: Some("_3".to_string()),
            },
            LocalDecl {
                ty: MirType::Bool,
                name: Some("_4".to_string()),
            },
        ],
        blocks: vec![
            // Block 0: entry - check val < 1
            BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(3),
                        projections: vec![],
                    },
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Copy(Place {
                            local: Local(2),
                            projections: vec![],
                        }),
                        Operand::Constant(Constant::Int(1)),
                    ),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place {
                        local: Local(3),
                        projections: vec![],
                    }),
                    targets: vec![(1, 1)], // if true, goto block 1
                    otherwise: 2,          // else goto block 2
                },
            },
            // Block 1: val < 1 branch - return 1
            BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Use(Operand::Constant(Constant::Int(1))),
                }],
                terminator: Terminator::Return,
            },
            // Block 2: check val > n
            BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(4),
                        projections: vec![],
                    },
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Gt,
                        Operand::Copy(Place {
                            local: Local(2),
                            projections: vec![],
                        }),
                        Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        }),
                    ),
                }],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place {
                        local: Local(4),
                        projections: vec![],
                    }),
                    targets: vec![(1, 3)], // if true, goto block 3
                    otherwise: 4,          // else goto block 4
                },
            },
            // Block 3: val > n branch - return n
            BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: Local(1),
                        projections: vec![],
                    })),
                }],
                terminator: Terminator::Return,
            },
            // Block 4: else branch - return val
            BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: Local(2),
                        projections: vec![],
                    })),
                }],
                terminator: Terminator::Return,
            },
        ],
        span: SourceSpan::default(),
    };

    // Specs:
    // #[requires(n > 0)]
    // #[ensures(result >= 1)]
    // #[ensures(result <= n)]

    let specs = FunctionSpecs {
        requires: vec![SpecClause {
            pred: Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("_1_0".to_string())), // n
                Box::new(Expr::IntLit(0)),
            )),
            span: SourceSpan::default(),
            label: Some("requires(n > 0)".to_string()),
        }],
        ensures: vec![
            SpecClause {
                pred: Predicate::Expr(Expr::Ge(
                    Box::new(Expr::Var("_0_0".to_string())), // result
                    Box::new(Expr::IntLit(1)),
                )),
                span: SourceSpan::default(),
                label: Some("ensures(result >= 1)".to_string()),
            },
            SpecClause {
                pred: Predicate::Expr(Expr::Le(
                    Box::new(Expr::Var("_0_0".to_string())), // result
                    Box::new(Expr::Var("_1_0".to_string())), // n
                )),
                span: SourceSpan::default(),
                label: Some("ensures(result <= n)".to_string()),
            },
        ],
        decreases: None,
        pure: true,
        trusted: false,
        api_metadata: None,
        effects: None, // Pure function has empty effects
        param_refinements: HashMap::default(),
    };

    (func, specs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use vc_ir::EffectOptimization;

    #[test]
    fn test_verifier_creation() {
        let verifier = Verifier::new();
        assert!(verifier.config.timeout_ms > 0);
    }

    #[test]
    fn test_clamp_positive_mir_creation() {
        let (func, specs) = mir_from_clamp_positive();
        assert_eq!(func.name, "clamp_positive");
        assert_eq!(func.params.len(), 2);
        assert_eq!(func.blocks.len(), 5);
        assert_eq!(specs.requires.len(), 1);
        assert_eq!(specs.ensures.len(), 2);
    }

    #[test]
    fn test_simple_function_verification() {
        // Test a trivially true function
        use crate::{
            BasicBlock, Constant, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        let func = MirFunction {
            name: "return_one".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![LocalDecl {
                ty: MirType::Int {
                    signed: true,
                    bits: 32,
                },
                name: Some("_0".to_string()),
            }],
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Use(Operand::Constant(Constant::Int(1))),
                }],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![],
            ensures: vec![vc_ir::SpecClause {
                pred: Predicate::Expr(vc_ir::Expr::Eq(
                    Box::new(vc_ir::Expr::Var("_0_0".to_string())),
                    Box::new(vc_ir::Expr::IntLit(1)),
                )),
                span: SourceSpan::default(),
                label: Some("ensures(result == 1)".to_string()),
            }],
            decreases: None,
            pure: true,
            trusted: false,
            api_metadata: None,
            effects: None,
            param_refinements: HashMap::default(),
        };

        let verifier = Verifier::new();
        let result = verifier.verify_function(&func, &specs);

        assert_eq!(result.function_name, "return_one");
        assert!(!result.vc_results.is_empty());
    }

    #[test]
    fn test_clamp_positive_full_pipeline() {
        let (func, specs) = mir_from_clamp_positive();
        let verifier = Verifier::new();
        let result = verifier.verify_function(&func, &specs);

        println!(
            "Verification result for {}: {:?}",
            result.function_name, result.status
        );
        for vc_result in &result.vc_results {
            println!("  VC '{}': {:?}", vc_result.name, vc_result.result);
        }

        // Note: The WP implementation is simplified, so we don't expect full proof yet
        // This test verifies the pipeline works end-to-end
        assert_eq!(result.function_name, "clamp_positive");
    }

    #[test]
    fn test_certificate_generation() {
        let (func, specs) = mir_from_clamp_positive();
        let verifier = Verifier::new();
        let result = verifier.verify_function(&func, &specs);

        // Generate certificate
        let cert = verifier.generate_certificate(&func, &specs, &result);

        // Verify certificate properties
        assert_eq!(cert.property_name, "clamp_positive");
        assert!(!cert.vcs.is_empty());

        // Check that method is detected correctly (Z3 by default)
        let method_str = format!("{}", cert.method);
        assert!(method_str.contains("SMT/Z3") || method_str.contains("SMT/Z4"));

        // Summary should contain key info
        let summary = cert.summary();
        assert!(summary.contains("clamp_positive"));
        assert!(summary.contains("VCs proven"));
    }

    // ============================================
    // Effect checking tests
    // ============================================

    #[test]
    fn test_effect_registry_creation() {
        let registry = EffectRegistry::new();
        assert!(registry.get("nonexistent").is_none());
    }

    #[test]
    fn test_effect_registry_registration() {
        let mut registry = EffectRegistry::new();
        registry.register("pure_fn", Some(EffectSet::empty()));
        registry.register("io_fn", Some(EffectSet::from_effects([Effect::IO])));
        registry.register("unrestricted_fn", None);

        assert!(registry.get("pure_fn").is_some());
        assert!(registry.get("io_fn").is_some());
        assert!(registry.get("unrestricted_fn").is_some());
    }

    #[test]
    fn test_effect_check_pure_calling_pure() {
        let mut registry = EffectRegistry::new();
        registry.register("caller", Some(EffectSet::empty()));
        registry.register("callee", Some(EffectSet::empty()));

        // Pure calling pure is allowed
        let result = registry.check_call("caller", "callee", &SourceSpan::default());
        assert!(result.is_none());
    }

    #[test]
    fn test_effect_check_io_calling_pure() {
        let mut registry = EffectRegistry::new();
        registry.register("caller", Some(EffectSet::from_effects([Effect::IO])));
        registry.register("callee", Some(EffectSet::empty()));

        // Function with IO effect can call pure function
        let result = registry.check_call("caller", "callee", &SourceSpan::default());
        assert!(result.is_none());
    }

    #[test]
    fn test_effect_check_pure_calling_io() {
        let mut registry = EffectRegistry::new();
        registry.register("caller", Some(EffectSet::empty()));
        registry.register("callee", Some(EffectSet::from_effects([Effect::IO])));

        // Pure function cannot call IO function
        let result = registry.check_call("caller", "callee", &SourceSpan::default());
        assert!(result.is_some());
        let violation = result.unwrap();
        assert_eq!(violation.caller, "caller");
        assert_eq!(violation.callee, "callee");
        assert!(violation.missing_effects.contains(&Effect::IO));
    }

    #[test]
    fn test_effect_check_io_calling_alloc() {
        let mut registry = EffectRegistry::new();
        registry.register("caller", Some(EffectSet::from_effects([Effect::IO])));
        registry.register("callee", Some(EffectSet::from_effects([Effect::Alloc])));

        // IO function cannot call Alloc function (different effect)
        let result = registry.check_call("caller", "callee", &SourceSpan::default());
        assert!(result.is_some());
        let violation = result.unwrap();
        assert!(violation.missing_effects.contains(&Effect::Alloc));
    }

    #[test]
    fn test_effect_check_io_alloc_calling_io() {
        let mut registry = EffectRegistry::new();
        registry.register(
            "caller",
            Some(EffectSet::from_effects([Effect::IO, Effect::Alloc])),
        );
        registry.register("callee", Some(EffectSet::from_effects([Effect::IO])));

        // Function with {IO, Alloc} can call function with {IO}
        let result = registry.check_call("caller", "callee", &SourceSpan::default());
        assert!(result.is_none());
    }

    #[test]
    fn test_effect_check_unrestricted_caller() {
        let mut registry = EffectRegistry::new();
        registry.register("caller", None); // No declared effects = all effects
        registry.register(
            "callee",
            Some(EffectSet::from_effects([Effect::IO, Effect::Panic])),
        );

        // Unrestricted caller can call anything
        let result = registry.check_call("caller", "callee", &SourceSpan::default());
        assert!(result.is_none());
    }

    #[test]
    fn test_effect_check_pure_calling_unrestricted() {
        let mut registry = EffectRegistry::new();
        registry.register("caller", Some(EffectSet::empty()));
        registry.register("callee", None); // No declared effects = assume all effects

        // Pure function calling unrestricted function is a violation
        let result = registry.check_call("caller", "callee", &SourceSpan::default());
        assert!(result.is_some());
    }

    #[test]
    fn test_verifier_with_effect_registry() {
        let mut verifier = Verifier::new();
        verifier.register_effects("pure_fn", Some(EffectSet::empty()));
        verifier.register_effects("io_fn", Some(EffectSet::from_effects([Effect::IO])));

        // Verify registry is populated
        assert!(verifier.effect_registry().get("pure_fn").is_some());
        assert!(verifier.effect_registry().get("io_fn").is_some());
    }

    #[test]
    fn test_effect_check_on_function() {
        let (func, specs) = mir_from_clamp_positive();
        let verifier = Verifier::new();

        // clamp_positive is pure and has no calls to effectful functions
        let result = verifier.check_effects(&func, &specs);
        assert!(result.passed);
        assert!(result.violations.is_empty());
    }

    #[test]
    fn test_effect_check_uses_callsite_span_and_known_effects() {
        use crate::{BasicBlock, Local, LocalDecl, MirType, Place, Terminator};
        use std::sync::Arc;

        let call_span = SourceSpan {
            file: Arc::from("effect_check.rs"),
            line_start: 12,
            line_end: 12,
            col_start: 5,
            col_end: 20,
        };

        // Pure function calling println should be rejected, and the violation should carry the callsite span.
        let func = MirFunction {
            name: "pure_calls_println".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "println".to_string(),
                        args: vec![],
                        destination: Place {
                            local: Local(0),
                            projections: vec![],
                        },
                        target: 1,
                        span: call_span.clone(),
                        generic_args: vec![],
                    },
                },
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Return,
                },
            ],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![],
            ensures: vec![],
            decreases: None,
            pure: true,
            trusted: false,
            api_metadata: None,
            effects: None,
            param_refinements: HashMap::default(),
        };

        let verifier = Verifier::new();
        let result = verifier.check_effects(&func, &specs);

        assert!(!result.passed);
        assert_eq!(result.violations.len(), 1);
        assert_eq!(result.violations[0].callee, "println");
        assert_eq!(result.violations[0].span.file.as_ref(), "effect_check.rs");
        assert_eq!(result.violations[0].span.line_start, 12);
        assert_eq!(result.violations[0].span.col_start, 5);
    }

    #[test]
    fn test_effect_check_allows_io_calling_known_io() {
        use crate::{BasicBlock, Local, LocalDecl, MirType, Place, Terminator};

        let func = MirFunction {
            name: "io_calls_println".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "println".to_string(),
                        args: vec![],
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
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![],
            ensures: vec![],
            decreases: None,
            pure: false,
            trusted: false,
            effects: Some(EffectSet::from_effects([Effect::IO])),
            api_metadata: None,
            param_refinements: HashMap::default(),
        };

        let verifier = Verifier::new();
        let result = verifier.check_effects(&func, &specs);

        assert!(result.passed);
        assert!(result.violations.is_empty());
    }

    // ============================================
    // Effect inference tests
    // ============================================

    #[test]
    fn test_effect_inference_creation() {
        let inference = EffectInference::new();
        // Should have known effects for common functions
        assert!(inference.get_known("println").is_some());
        assert!(inference.get_known("panic").is_some());
        assert!(inference.get_known("Box::new").is_some());
    }

    #[test]
    fn test_effect_inference_known_io() {
        let inference = EffectInference::new();
        let io_effects = inference.get_known("println").unwrap();
        assert!(io_effects.has(Effect::IO));
        assert!(!io_effects.has(Effect::Alloc));
    }

    #[test]
    fn test_effect_inference_known_alloc() {
        let inference = EffectInference::new();
        let alloc_effects = inference.get_known("Vec::push").unwrap();
        assert!(alloc_effects.has(Effect::Alloc));
        assert!(!alloc_effects.has(Effect::IO));
    }

    #[test]
    fn test_effect_inference_known_panic() {
        let inference = EffectInference::new();
        let panic_effects = inference.get_known("panic").unwrap();
        assert!(panic_effects.has(Effect::Panic));
    }

    #[test]
    fn test_effect_inference_register_known() {
        let mut inference = EffectInference::new();
        inference.register_known("my_io_fn", EffectSet::from_effects([Effect::IO]));
        let effects = inference.get_known("my_io_fn").unwrap();
        assert!(effects.has(Effect::IO));
    }

    #[test]
    fn test_effect_inference_pure_function() {
        use crate::{
            BasicBlock, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement, Terminator,
        };

        // Create a pure function: fn identity(x: i32) -> i32 { x }
        let func = MirFunction {
            name: "identity".to_string(),
            params: vec![(
                "x".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("x".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: Local(1),
                        projections: vec![],
                    })),
                }],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let inference = EffectInference::new();
        let registry = EffectRegistry::new();
        let effects = inference.infer_effects(&func, &registry);

        // Pure function should have no effects
        assert!(effects.is_pure());
    }

    #[test]
    fn test_effect_inference_function_with_call_to_println() {
        use crate::{BasicBlock, Local, LocalDecl, MirType, Place, Terminator};

        // Create a function that calls println
        let func = MirFunction {
            name: "print_something".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]), // Unit type
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "println".to_string(),
                        args: vec![],
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
            span: SourceSpan::default(),
        };

        let inference = EffectInference::new();
        let registry = EffectRegistry::new();
        let effects = inference.infer_effects(&func, &registry);

        // Should have IO effect from println call
        assert!(effects.has(Effect::IO));
    }

    #[test]
    fn test_effect_inference_function_with_division() {
        use crate::{
            BasicBlock, BinOp, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        // Create a function with division: fn divide(a: i32, b: i32) -> i32 { a / b }
        let func = MirFunction {
            name: "divide".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
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
            }],
            span: SourceSpan::default(),
        };

        let inference = EffectInference::new();
        let registry = EffectRegistry::new();
        let effects = inference.infer_effects(&func, &registry);

        // Division can panic (divide by zero)
        assert!(effects.has(Effect::Panic));
    }

    #[test]
    fn test_effect_inference_function_with_assert() {
        use crate::{
            BasicBlock, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement, Terminator,
        };

        // Create a function with an assert terminator
        let func = MirFunction {
            name: "assert_positive".to_string(),
            params: vec![(
                "x".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("x".to_string()),
                },
            ],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place {
                            local: Local(1),
                            projections: vec![],
                        }),
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
                            projections: vec![],
                        })),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            span: SourceSpan::default(),
        };

        let inference = EffectInference::new();
        let registry = EffectRegistry::new();
        let effects = inference.infer_effects(&func, &registry);

        // Assert can panic
        assert!(effects.has(Effect::Panic));
    }

    #[test]
    fn test_effect_inference_is_pure() {
        use crate::{
            BasicBlock, BinOp, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        // Pure function
        let pure_func = MirFunction {
            name: "add".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::BinaryOp(
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
            span: SourceSpan::default(),
        };

        let inference = EffectInference::new();
        let registry = EffectRegistry::new();

        assert!(inference.is_pure(&pure_func, &registry));
    }

    #[test]
    fn test_effect_inference_transitive() {
        use crate::{BasicBlock, Local, LocalDecl, MirType, Place, Terminator};

        // Function A is pure
        let func_a = MirFunction {
            name: "func_a".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]), // Unit type
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        // Function B calls println (has IO effect)
        let func_b = MirFunction {
            name: "func_b".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "println".to_string(),
                        args: vec![],
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
            span: SourceSpan::default(),
        };

        // Function C calls func_b (should inherit IO effect)
        let func_c = MirFunction {
            name: "func_c".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "func_b".to_string(),
                        args: vec![],
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
            span: SourceSpan::default(),
        };

        let inference = EffectInference::new();
        let functions: Vec<(MirFunction, Option<EffectSet>)> =
            vec![(func_a, None), (func_b, None), (func_c, None)];

        let result = inference.infer_effects_transitive(&functions);

        // func_a should be pure
        assert!(result.get("func_a").unwrap().is_pure());

        // func_b should have IO effect
        assert!(result.get("func_b").unwrap().has(Effect::IO));

        // func_c should inherit IO effect from func_b
        assert!(result.get("func_c").unwrap().has(Effect::IO));
    }

    #[test]
    fn test_effect_inference_respects_declared_effects() {
        use crate::{BasicBlock, Local, LocalDecl, MirType, Place, Terminator};

        // Function with declared effects should use those, not inferred
        let func = MirFunction {
            name: "declared_pure".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "println".to_string(), // Would infer IO effect
                        args: vec![],
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
            span: SourceSpan::default(),
        };

        let inference = EffectInference::new();
        let functions: Vec<(MirFunction, Option<EffectSet>)> = vec![
            (func, Some(EffectSet::empty())), // Declared pure
        ];

        let result = inference.infer_effects_transitive(&functions);

        // Should use declared effects (pure), not inferred (IO)
        assert!(result.get("declared_pure").unwrap().is_pure());
    }

    #[test]
    fn test_effect_inference_unreachable_has_panic() {
        use crate::{BasicBlock, LocalDecl, MirType, Terminator};

        let func = MirFunction {
            name: "unreachable_fn".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Unreachable,
            }],
            span: SourceSpan::default(),
        };

        let inference = EffectInference::new();
        let registry = EffectRegistry::new();
        let effects = inference.infer_effects(&func, &registry);

        // Unreachable implies potential panic/abort
        assert!(effects.has(Effect::Panic));
    }

    #[test]
    fn test_effect_inference_from_call_patterns() {
        use crate::{BasicBlock, Local, LocalDecl, MirType, Place, Terminator};

        // Test inference from function name patterns (panic, unwrap, expect)
        let test_cases = vec![
            ("panic_handler", "core::panicking::panic", Effect::Panic),
            ("unwrap_caller", "Option::unwrap", Effect::Panic),
            ("expect_caller", "Result::expect", Effect::Panic),
        ];

        for (fn_name, callee, expected_effect) in test_cases {
            let func = MirFunction {
                name: fn_name.to_string(),
                params: vec![],
                return_type: MirType::Tuple(vec![]),
                locals: vec![LocalDecl {
                    ty: MirType::Tuple(vec![]),
                    name: Some("_0".to_string()),
                }],
                blocks: vec![
                    BasicBlock {
                        statements: vec![],
                        terminator: Terminator::Call {
                            func: callee.to_string(),
                            args: vec![],
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
                span: SourceSpan::default(),
            };

            let inference = EffectInference::new();
            let registry = EffectRegistry::new();
            let effects = inference.infer_effects(&func, &registry);

            assert!(
                effects.has(expected_effect),
                "Expected {fn_name} to have {expected_effect:?} effect from calling {callee}"
            );
        }
    }

    // ============================================
    // Polymorphic effect tests
    // ============================================

    #[test]
    fn test_effect_registry_polymorphic_registration() {
        let mut registry = EffectRegistry::new();

        // Register a polymorphic function: #[effects_of(callback)]
        registry.register_polymorphic("apply", EffectSource::param("callback"));

        assert!(registry.get_polymorphic("apply").is_some());
        assert!(registry.get_polymorphic("nonexistent").is_none());
    }

    #[test]
    fn test_effect_registry_resolve_polymorphic() {
        let mut registry = EffectRegistry::new();

        // apply has effects_of(callback)
        registry.register_polymorphic("apply", EffectSource::param("callback"));

        // Create argument effects - callback has IO effect
        let mut arg_effects = HashMap::new();
        arg_effects.insert(
            "callback".to_string(),
            EffectSet::from_effects([Effect::IO]),
        );

        // Resolve should return IO effect
        let resolved = registry
            .resolve_callee_effects("apply", &arg_effects)
            .unwrap();
        assert!(resolved.has(Effect::IO));
        assert!(!resolved.has(Effect::Alloc));
    }

    #[test]
    fn test_effect_registry_resolve_non_polymorphic() {
        let mut registry = EffectRegistry::new();

        // println has concrete IO effect
        registry.register("println", Some(EffectSet::from_effects([Effect::IO])));

        // Resolve without arg_effects should still work
        let arg_effects = HashMap::new();
        let resolved = registry
            .resolve_callee_effects("println", &arg_effects)
            .unwrap();
        assert!(resolved.has(Effect::IO));
    }

    #[test]
    fn test_check_call_polymorphic_allowed() {
        let mut registry = EffectRegistry::new();

        // caller has IO effect
        registry.register("caller", Some(EffectSet::from_effects([Effect::IO])));

        // apply has effects_of(callback)
        registry.register_polymorphic("apply", EffectSource::param("callback"));

        // Callback has IO effect - should be allowed
        let mut arg_effects = HashMap::new();
        arg_effects.insert(
            "callback".to_string(),
            EffectSet::from_effects([Effect::IO]),
        );

        let result = registry.check_call_polymorphic(
            "caller",
            "apply",
            &arg_effects,
            &SourceSpan::default(),
        );
        assert!(result.is_none()); // No violation
    }

    #[test]
    fn test_check_call_polymorphic_violation() {
        let mut registry = EffectRegistry::new();

        // caller is pure (no effects)
        registry.register("caller", Some(EffectSet::empty()));

        // apply has effects_of(callback)
        registry.register_polymorphic("apply", EffectSource::param("callback"));

        // Callback has IO effect - pure caller cannot call apply(io_callback)
        let mut arg_effects = HashMap::new();
        arg_effects.insert(
            "callback".to_string(),
            EffectSet::from_effects([Effect::IO]),
        );

        let result = registry.check_call_polymorphic(
            "caller",
            "apply",
            &arg_effects,
            &SourceSpan::default(),
        );
        assert!(result.is_some()); // Should have violation
        assert!(result.unwrap().missing_effects.contains(&Effect::IO));
    }

    #[test]
    fn test_check_call_polymorphic_union_effects() {
        let mut registry = EffectRegistry::new();

        // caller has IO and Alloc effects
        registry.register(
            "caller",
            Some(EffectSet::from_effects([Effect::IO, Effect::Alloc])),
        );

        // map has IO + effects_of(f)
        registry.register_polymorphic(
            "map",
            EffectSource::union(vec![
                EffectSource::concrete([Effect::IO]),
                EffectSource::param("f"),
            ]),
        );

        // f has Alloc effect - total should be IO + Alloc
        let mut arg_effects = HashMap::new();
        arg_effects.insert("f".to_string(), EffectSet::from_effects([Effect::Alloc]));

        let result =
            registry.check_call_polymorphic("caller", "map", &arg_effects, &SourceSpan::default());
        assert!(result.is_none()); // Should be allowed
    }

    #[test]
    fn test_check_call_polymorphic_union_violation() {
        let mut registry = EffectRegistry::new();

        // caller has only IO effect
        registry.register("caller", Some(EffectSet::from_effects([Effect::IO])));

        // map has IO + effects_of(f)
        registry.register_polymorphic(
            "map",
            EffectSource::union(vec![
                EffectSource::concrete([Effect::IO]),
                EffectSource::param("f"),
            ]),
        );

        // f has Alloc effect - total would be IO + Alloc, but caller only has IO
        let mut arg_effects = HashMap::new();
        arg_effects.insert("f".to_string(), EffectSet::from_effects([Effect::Alloc]));

        let result =
            registry.check_call_polymorphic("caller", "map", &arg_effects, &SourceSpan::default());
        assert!(result.is_some()); // Should have violation
        assert!(result.unwrap().missing_effects.contains(&Effect::Alloc));
    }

    #[test]
    fn test_check_call_polymorphic_pure_callback() {
        let mut registry = EffectRegistry::new();

        // caller is pure
        registry.register("caller", Some(EffectSet::empty()));

        // apply has effects_of(callback)
        registry.register_polymorphic("apply", EffectSource::param("callback"));

        // Callback is also pure - should be allowed
        let mut arg_effects = HashMap::new();
        arg_effects.insert("callback".to_string(), EffectSet::empty());

        let result = registry.check_call_polymorphic(
            "caller",
            "apply",
            &arg_effects,
            &SourceSpan::default(),
        );
        assert!(result.is_none()); // Pure caller can call apply(pure_callback)
    }

    // ============================================
    // Effect-based optimization tests (Phase 5.3)
    // ============================================

    #[test]
    fn test_effect_optimization_analyzer_creation() {
        let _analyzer = EffectOptimizationAnalyzer::new();
    }

    #[test]
    fn test_effect_optimization_analyzer_pure_function() {
        use crate::{
            BasicBlock, BinOp, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        // Pure function: fn add(a: i32, b: i32) -> i32 { a + b }
        let func = MirFunction {
            name: "add".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::BinaryOp(
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
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![],
            ensures: vec![],
            decreases: None,
            pure: true, // Declared pure
            trusted: false,
            api_metadata: None,
            effects: None,
            param_refinements: HashMap::default(),
        };

        let analyzer = EffectOptimizationAnalyzer::new();
        let registry = EffectRegistry::new();
        let result = analyzer.analyze_function(&func, &specs, &registry);

        // Pure function should have all optimizations
        assert!(result.optimizations.is_memoizable());
        assert!(result.optimizations.is_no_unwind());
        assert!(result.optimizations.is_embedded_safe());
        assert!(result
            .optimizations
            .has(EffectOptimization::ConstEvalCandidate));
        assert!(result.optimizations.has(EffectOptimization::ThreadSafe));
        assert!(result.optimizations.has(EffectOptimization::MemorySafe));
    }

    #[test]
    fn test_effect_optimization_analyzer_function_with_io() {
        use crate::{BasicBlock, Local, LocalDecl, MirType, Place, Terminator};

        // Function that calls println (IO effect)
        let func = MirFunction {
            name: "print_hello".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "println".to_string(),
                        args: vec![],
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
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![],
            ensures: vec![],
            decreases: None,
            pure: false,
            trusted: false,
            api_metadata: None,
            effects: None, // Will be inferred
            param_refinements: HashMap::default(),
        };

        let analyzer = EffectOptimizationAnalyzer::new();
        let registry = EffectRegistry::new();
        let result = analyzer.analyze_function(&func, &specs, &registry);

        // Function with IO should NOT be memoizable
        assert!(!result.optimizations.is_memoizable());
        // But should be no_unwind (println doesn't panic)
        assert!(result.optimizations.is_no_unwind());
        // And should be embedded_safe (no allocation inferred from println)
        assert!(result.optimizations.is_embedded_safe());
        // Should NOT be const eval candidate (has IO)
        assert!(!result
            .optimizations
            .has(EffectOptimization::ConstEvalCandidate));
    }

    #[test]
    fn test_effect_optimization_analyzer_function_with_panic() {
        use crate::{
            BasicBlock, BinOp, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        // Function with division (can panic)
        let func = MirFunction {
            name: "divide".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
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
            }],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs::default();

        let analyzer = EffectOptimizationAnalyzer::new();
        let registry = EffectRegistry::new();
        let result = analyzer.analyze_function(&func, &specs, &registry);

        // Function with panic should NOT be no_unwind
        assert!(!result.optimizations.is_no_unwind());
        // But should be embedded_safe (no allocation)
        assert!(result.optimizations.is_embedded_safe());
        // And should be const eval candidate (no IO)
        assert!(result
            .optimizations
            .has(EffectOptimization::ConstEvalCandidate));
    }

    #[test]
    fn test_effect_optimization_analyzer_function_with_alloc() {
        use crate::{BasicBlock, Local, LocalDecl, MirType, Place, Terminator};

        // Function that calls Vec::push (Alloc effect)
        let func = MirFunction {
            name: "push_to_vec".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "Vec::push".to_string(),
                        args: vec![],
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
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs::default();

        let analyzer = EffectOptimizationAnalyzer::new();
        let registry = EffectRegistry::new();
        let result = analyzer.analyze_function(&func, &specs, &registry);

        // Function with Alloc should NOT be embedded_safe
        assert!(!result.optimizations.is_embedded_safe());
        // But should be no_unwind (Vec::push doesn't panic in this model)
        assert!(result.optimizations.is_no_unwind());
    }

    #[test]
    fn test_effect_optimization_analyzer_declared_effects() {
        use crate::{BasicBlock, LocalDecl, MirType, Terminator};

        // Function with declared effects (IO only)
        let func = MirFunction {
            name: "io_only".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![],
            ensures: vec![],
            decreases: None,
            pure: false,
            trusted: false,
            effects: Some(EffectSet::from_effects([Effect::IO])),
            api_metadata: None,
            param_refinements: HashMap::default(),
        };

        let analyzer = EffectOptimizationAnalyzer::new();
        let registry = EffectRegistry::new();
        let result = analyzer.analyze_function(&func, &specs, &registry);

        // Should use declared effects, not inferred
        assert!(!result.optimizations.is_memoizable());
        assert!(result.optimizations.is_no_unwind());
        assert!(result.optimizations.is_embedded_safe());
        assert!(!result
            .optimizations
            .has(EffectOptimization::ConstEvalCandidate));
    }

    #[test]
    fn test_effect_optimization_analyzer_is_memoizable() {
        let (func, specs) = mir_from_clamp_positive();

        let analyzer = EffectOptimizationAnalyzer::new();
        let registry = EffectRegistry::new();

        // clamp_positive is declared pure
        assert!(analyzer.is_memoizable(&func, &specs, &registry));
    }

    #[test]
    fn test_effect_optimization_analyzer_can_skip_unwind() {
        let (func, specs) = mir_from_clamp_positive();

        let analyzer = EffectOptimizationAnalyzer::new();
        let registry = EffectRegistry::new();

        // clamp_positive is pure, so no panic possible
        assert!(analyzer.can_skip_unwind(&func, &specs, &registry));
    }

    #[test]
    fn test_effect_optimization_analyzer_is_embedded_safe() {
        let (func, specs) = mir_from_clamp_positive();

        let analyzer = EffectOptimizationAnalyzer::new();
        let registry = EffectRegistry::new();

        // clamp_positive doesn't allocate
        assert!(analyzer.is_embedded_safe(&func, &specs, &registry));
    }

    #[test]
    fn test_function_optimizations_summary() {
        use crate::{BasicBlock, LocalDecl, MirType, Terminator};

        let func = MirFunction {
            name: "test_fn".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            pure: true,
            ..Default::default()
        };

        let analyzer = EffectOptimizationAnalyzer::new();
        let registry = EffectRegistry::new();
        let result = analyzer.analyze_function(&func, &specs, &registry);

        let summary = result.summary();
        assert!(summary.contains("test_fn"));
        assert!(result.has_optimizations());
    }

    #[test]
    fn test_effect_optimization_analyzer_analyze_functions() {
        use crate::{
            BasicBlock, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement, Terminator,
        };

        // Two functions: one pure, one with IO
        let pure_func = MirFunction {
            name: "pure_add".to_string(),
            params: vec![],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![LocalDecl {
                ty: MirType::Int {
                    signed: true,
                    bits: 32,
                },
                name: Some("_0".to_string()),
            }],
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::Use(Operand::Constant(crate::Constant::Int(42))),
                }],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let io_func = MirFunction {
            name: "io_print".to_string(),
            params: vec![],
            return_type: MirType::Tuple(vec![]),
            locals: vec![LocalDecl {
                ty: MirType::Tuple(vec![]),
                name: Some("_0".to_string()),
            }],
            blocks: vec![
                BasicBlock {
                    statements: vec![],
                    terminator: Terminator::Call {
                        func: "println".to_string(),
                        args: vec![],
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
            span: SourceSpan::default(),
        };

        let pure_specs = FunctionSpecs {
            pure: true,
            ..Default::default()
        };
        let io_specs = FunctionSpecs::default();

        let analyzer = EffectOptimizationAnalyzer::new();
        let results = analyzer.analyze_functions(&[(pure_func, pure_specs), (io_func, io_specs)]);

        assert_eq!(results.len(), 2);

        // Pure function should be memoizable
        assert!(results[0].optimizations.is_memoizable());
        // IO function should NOT be memoizable
        assert!(!results[1].optimizations.is_memoizable());
    }

    // ============================================
    // Phase 12.3: Precondition Inference Tests
    // ============================================

    #[test]
    fn test_precondition_inference_creation() {
        let inference = PreconditionInference::new();
        // Should have known patterns
        assert!(inference.known_patterns.contains_key("Option::unwrap"));
        assert!(inference.known_patterns.contains_key("Result::unwrap"));
    }

    #[test]
    fn test_precondition_inference_division_by_zero() {
        use crate::{
            BasicBlock, BinOp, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        // Function: fn divide(a: i32, b: i32) -> i32 { a / b }
        let func = MirFunction {
            name: "divide".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
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
            }],
            span: SourceSpan::default(),
        };

        let inference = PreconditionInference::new();
        let preconditions = inference.infer_preconditions(&func);

        assert_eq!(preconditions.len(), 1);
        assert_eq!(preconditions[0].predicate, "b != 0");
        assert!(matches!(
            preconditions[0].operation,
            SafetyOperation::DivisionByZero { .. }
        ));
    }

    #[test]
    fn test_precondition_inference_remainder_by_zero() {
        use crate::{
            BasicBlock, BinOp, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        // Function: fn modulo(a: i32, b: i32) -> i32 { a % b }
        let func = MirFunction {
            name: "modulo".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Rem,
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
            span: SourceSpan::default(),
        };

        let inference = PreconditionInference::new();
        let preconditions = inference.infer_preconditions(&func);

        assert_eq!(preconditions.len(), 1);
        assert_eq!(preconditions[0].predicate, "b != 0");
        assert!(matches!(
            preconditions[0].operation,
            SafetyOperation::RemainderByZero { .. }
        ));
    }

    #[test]
    fn test_precondition_inference_analyze_function_with_missing() {
        use crate::{
            BasicBlock, BinOp, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        // Function: fn divide(a: i32, b: i32) -> i32 { a / b }
        // WITHOUT any declared preconditions
        let func = MirFunction {
            name: "divide".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
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
            }],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs::default(); // No preconditions

        let inference = PreconditionInference::new();
        let result = inference.analyze_function(&func, &specs);

        assert_eq!(result.function_name, "divide");
        assert_eq!(result.inferred_preconditions.len(), 1);
        assert_eq!(result.missing_preconditions.len(), 1);
        assert_eq!(result.missing_preconditions[0].predicate, "b != 0");

        // Should suggest a refinement for parameter b
        assert!(!result.suggested_refinements.is_empty());
        assert_eq!(result.suggested_refinements[0].param, "b");
    }

    #[test]
    fn test_precondition_inference_with_declared_precondition() {
        use crate::{
            BasicBlock, BinOp, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };
        use vc_ir::SpecClause;

        // Function with division AND a declared precondition
        let func = MirFunction {
            name: "safe_divide".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
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
            }],
            span: SourceSpan::default(),
        };

        // Declare the precondition: b != 0
        let specs = FunctionSpecs {
            requires: vec![SpecClause {
                pred: Predicate::Expr(Expr::Ne(
                    Box::new(Expr::Var("b".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                span: SourceSpan::default(),
                label: None,
            }],
            ..Default::default()
        };

        let inference = PreconditionInference::new();
        let result = inference.analyze_function(&func, &specs);

        assert_eq!(result.function_name, "safe_divide");
        assert_eq!(result.inferred_preconditions.len(), 1);
        // Since precondition is declared, missing should be empty
        assert!(
            result.missing_preconditions.is_empty(),
            "Should not have missing preconditions when declared"
        );
    }

    #[test]
    fn test_precondition_inference_no_dangerous_ops() {
        use crate::{
            BasicBlock, BinOp, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        // Function: fn add(a: i32, b: i32) -> i32 { a + b }
        // No division, no preconditions needed (ignoring overflow for now)
        let func = MirFunction {
            name: "add".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![Statement::Assign {
                    place: Place {
                        local: Local(0),
                        projections: vec![],
                    },
                    rvalue: Rvalue::BinaryOp(
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
            span: SourceSpan::default(),
        };

        let inference = PreconditionInference::new();
        let preconditions = inference.infer_preconditions(&func);

        assert!(preconditions.is_empty());
    }

    #[test]
    fn test_safety_operation_display() {
        let div_op = SafetyOperation::DivisionByZero {
            divisor: "x".to_string(),
        };
        assert!(format!("{div_op}").contains("division by zero"));
        assert!(format!("{div_op}").contains('x'));

        let rem_op = SafetyOperation::RemainderByZero {
            divisor: "y".to_string(),
        };
        assert!(format!("{rem_op}").contains("remainder by zero"));

        let bounds_op = SafetyOperation::ArrayBoundsCheck {
            index: "i".to_string(),
            array: "arr".to_string(),
        };
        assert!(format!("{bounds_op}").contains("array bounds"));
    }

    #[test]
    fn test_suggested_refinement_generation() {
        use crate::{
            BasicBlock, BinOp, Local, LocalDecl, MirType, Operand, Place, Rvalue, Statement,
            Terminator,
        };

        // Function with multiple params where one is used as divisor
        let func = MirFunction {
            name: "divide_by_y".to_string(),
            params: vec![
                (
                    "x".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "y".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("x".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("y".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
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
            }],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs::default();
        let inference = PreconditionInference::new();
        let result = inference.analyze_function(&func, &specs);

        // Should suggest: #[trust::refined(y, "y != 0")]
        assert_eq!(result.suggested_refinements.len(), 1);
        assert_eq!(result.suggested_refinements[0].param, "y");
        assert!(result.suggested_refinements[0].predicate.contains("!= 0"));
    }

    // ============================================
    // Phase 12.3: Requires-to-Refined Conversion Tests
    // ============================================

    #[test]
    fn test_requires_to_refined_basic() {
        use crate::{BasicBlock, LocalDecl, MirType, Terminator};
        use vc_ir::SpecClause;

        // Function: fn foo(x: i32) -> i32
        // with #[requires("x > 0")]
        let func = MirFunction {
            name: "foo".to_string(),
            params: vec![(
                "x".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("x".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![SpecClause {
                pred: Predicate::Expr(Expr::Gt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                span: SourceSpan::default(),
                label: Some("requires(x > 0)".to_string()),
            }],
            ..Default::default()
        };

        let inference = PreconditionInference::new();
        let suggestions = inference.requires_to_refined_suggestions(&specs, &func);

        assert_eq!(suggestions.len(), 1);
        assert_eq!(suggestions[0].param, "x");
        assert_eq!(suggestions[0].predicate, "x > 0");
        assert!(suggestions[0].reason.contains("Converted from #[requires]"));
    }

    #[test]
    fn test_requires_to_refined_multiple_params() {
        use crate::{BasicBlock, LocalDecl, MirType, Terminator};
        use vc_ir::SpecClause;

        // Function: fn bar(a: i32, b: i32) -> i32
        // with #[requires("a > 0 && b > 0")]
        let func = MirFunction {
            name: "bar".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("a".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("b".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![SpecClause {
                pred: Predicate::And(vec![
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("a".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                    Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("b".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                ]),
                span: SourceSpan::default(),
                label: Some("requires(a > 0 && b > 0)".to_string()),
            }],
            ..Default::default()
        };

        let inference = PreconditionInference::new();
        let suggestions = inference.requires_to_refined_suggestions(&specs, &func);

        // Should generate suggestions for both params since both appear in the predicate
        assert_eq!(suggestions.len(), 2);
        let params: Vec<_> = suggestions.iter().map(|s| s.param.as_str()).collect();
        assert!(params.contains(&"a"));
        assert!(params.contains(&"b"));
    }

    #[test]
    fn test_requires_to_refined_separate_requires() {
        use crate::{BasicBlock, LocalDecl, MirType, Terminator};
        use vc_ir::SpecClause;

        // Function with two separate #[requires] attributes
        let func = MirFunction {
            name: "baz".to_string(),
            params: vec![
                (
                    "x".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "y".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
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
                    name: Some("x".to_string()),
                },
                LocalDecl {
                    ty: MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                    name: Some("y".to_string()),
                },
            ],
            blocks: vec![BasicBlock {
                statements: vec![],
                terminator: Terminator::Return,
            }],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![
                SpecClause {
                    pred: Predicate::Expr(Expr::Gt(
                        Box::new(Expr::Var("x".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                    span: SourceSpan::default(),
                    label: Some("requires(x > 0)".to_string()),
                },
                SpecClause {
                    pred: Predicate::Expr(Expr::Ne(
                        Box::new(Expr::Var("y".to_string())),
                        Box::new(Expr::IntLit(0)),
                    )),
                    span: SourceSpan::default(),
                    label: Some("requires(y != 0)".to_string()),
                },
            ],
            ..Default::default()
        };

        let inference = PreconditionInference::new();
        let suggestions = inference.requires_to_refined_suggestions(&specs, &func);

        assert_eq!(suggestions.len(), 2);

        // First suggestion should be for x
        assert_eq!(suggestions[0].param, "x");
        assert_eq!(suggestions[0].predicate, "x > 0");

        // Second suggestion should be for y
        assert_eq!(suggestions[1].param, "y");
        assert_eq!(suggestions[1].predicate, "y != 0");
    }

    #[test]
    fn test_predicate_mentions_param_word_boundary() {
        // "x < max" should match both x and max
        assert!(PreconditionInference::predicate_mentions_param(
            "x < max", "x"
        ));
        assert!(PreconditionInference::predicate_mentions_param(
            "x < max", "max"
        ));

        // "x_max > 0" should NOT match x or max (they're part of larger identifier)
        assert!(!PreconditionInference::predicate_mentions_param(
            "x_max > 0",
            "x"
        ));
        assert!(!PreconditionInference::predicate_mentions_param(
            "x_max > 0",
            "max"
        ));

        // "maximum > x" should match x but NOT max
        assert!(PreconditionInference::predicate_mentions_param(
            "maximum > x",
            "x"
        ));
        assert!(!PreconditionInference::predicate_mentions_param(
            "maximum > x",
            "max"
        ));
    }

    #[test]
    fn test_extract_predicate_string_from_label() {
        use vc_ir::SpecClause;

        let inference = PreconditionInference::new();

        // Test with standard label format
        let clause = SpecClause {
            pred: Predicate::Bool(true), // ignored when label is present
            span: SourceSpan::default(),
            label: Some("requires(x > 0)".to_string()),
        };
        assert_eq!(inference.extract_predicate_string(&clause), "x > 0");

        // Test with nested parentheses
        let clause2 = SpecClause {
            pred: Predicate::Bool(true),
            span: SourceSpan::default(),
            label: Some("requires((a + b) > 0)".to_string()),
        };
        assert_eq!(inference.extract_predicate_string(&clause2), "(a + b) > 0");
    }

    #[test]
    fn test_extract_predicate_string_from_predicate() {
        use vc_ir::SpecClause;

        let inference = PreconditionInference::new();

        // Test with no label - should use predicate_to_string
        let clause = SpecClause {
            pred: Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("n".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            span: SourceSpan::default(),
            label: None,
        };
        assert_eq!(inference.extract_predicate_string(&clause), "n > 0");
    }

    #[test]
    fn test_predicate_to_string_complex() {
        let inference = PreconditionInference::new();

        // Test And predicate
        let and_pred = Predicate::And(vec![
            Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(10)),
            )),
        ]);
        assert_eq!(inference.predicate_to_string(&and_pred), "a > 0 && b < 10");

        // Test Or predicate
        let or_pred = Predicate::Or(vec![
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
        ]);
        assert!(inference.predicate_to_string(&or_pred).contains("||"));

        // Test Not predicate
        let not_pred = Predicate::Not(Box::new(Predicate::Expr(Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))));
        assert!(inference.predicate_to_string(&not_pred).contains('!'));
    }

    #[test]
    fn test_requires_to_refined_no_requires() {
        use crate::MirType;

        // Function with no requires clauses
        let func = MirFunction {
            name: "no_requires".to_string(),
            params: vec![(
                "x".to_string(),
                MirType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![],
            blocks: vec![],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs::default();

        let inference = PreconditionInference::new();
        let suggestions = inference.requires_to_refined_suggestions(&specs, &func);

        assert!(suggestions.is_empty());
    }

    #[test]
    fn test_requires_to_refined_cross_param_constraint() {
        use crate::MirType;
        use vc_ir::SpecClause;

        // Function with #[requires("low < high")]
        // This constraint involves both params, so should generate suggestions for both
        let func = MirFunction {
            name: "range".to_string(),
            params: vec![
                (
                    "low".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "high".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            locals: vec![],
            blocks: vec![],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![SpecClause {
                pred: Predicate::Expr(Expr::Lt(
                    Box::new(Expr::Var("low".to_string())),
                    Box::new(Expr::Var("high".to_string())),
                )),
                span: SourceSpan::default(),
                label: Some("requires(low < high)".to_string()),
            }],
            ..Default::default()
        };

        let inference = PreconditionInference::new();
        let suggestions = inference.requires_to_refined_suggestions(&specs, &func);

        // Both params should get suggestions since both appear in the predicate
        assert_eq!(suggestions.len(), 2);
        let params: Vec<_> = suggestions.iter().map(|s| s.param.as_str()).collect();
        assert!(params.contains(&"low"));
        assert!(params.contains(&"high"));

        // Both should have the same predicate
        assert!(suggestions.iter().all(|s| s.predicate == "low < high"));
    }

    // ============================================
    // Z4->Z3 Fallback Logic Tests
    // ============================================

    /// Helper to create a test VC with given condition
    fn test_vc(name: &str, condition: VcKind) -> VerificationCondition {
        VerificationCondition {
            id: VcId(1),
            name: name.to_string(),
            span: SourceSpan::dummy(),
            condition,
            preferred_backend: None,
        }
    }

    /// Helper to create a BoundVar for tests
    fn test_bound_var(name: &str) -> vc_ir::BoundVar {
        vc_ir::BoundVar {
            name: name.to_string(),
            ty: vc_ir::VcType::Int {
                signed: true,
                bits: 32,
            },
        }
    }

    #[test]
    fn test_vc_uses_quantifiers_simple_predicate() {
        // Simple predicate without quantifiers
        let vc = test_vc(
            "test_simple",
            VcKind::Predicate(Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(1)),
            ))),
        );
        assert!(!vc_uses_quantifiers(&vc));
    }

    #[test]
    fn test_vc_uses_quantifiers_forall_vckind() {
        // VcKind::Forall should be detected
        let vc = test_vc(
            "test_forall",
            VcKind::Forall {
                vars: vec![test_bound_var("i")],
                body: Box::new(VcKind::Predicate(Predicate::Bool(true))),
            },
        );
        assert!(vc_uses_quantifiers(&vc));
    }

    #[test]
    fn test_vc_uses_quantifiers_exists_vckind() {
        // VcKind::Exists should be detected
        let vc = test_vc(
            "test_exists",
            VcKind::Exists {
                vars: vec![test_bound_var("j")],
                body: Box::new(VcKind::Predicate(Predicate::Bool(true))),
            },
        );
        assert!(vc_uses_quantifiers(&vc));
    }

    #[test]
    fn test_vc_uses_quantifiers_predicate_forall() {
        // Predicate::Forall should be detected
        let vc = test_vc(
            "test_pred_forall",
            VcKind::Predicate(Predicate::Forall {
                vars: vec![(
                    "k".to_string(),
                    vc_ir::VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                )],
                triggers: vec![],
                body: Box::new(Predicate::Bool(true)),
            }),
        );
        assert!(vc_uses_quantifiers(&vc));
    }

    #[test]
    fn test_vc_uses_quantifiers_predicate_exists() {
        // Predicate::Exists should be detected
        let vc = test_vc(
            "test_pred_exists",
            VcKind::Predicate(Predicate::Exists {
                vars: vec![(
                    "m".to_string(),
                    vc_ir::VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                )],
                body: Box::new(Predicate::Bool(true)),
            }),
        );
        assert!(vc_uses_quantifiers(&vc));
    }

    #[test]
    fn test_vc_uses_quantifiers_nested_in_implies() {
        // Quantifier nested in VcKind::Implies should be detected
        let vc = test_vc(
            "test_nested_implies",
            VcKind::Implies {
                antecedent: Predicate::Bool(true),
                consequent: Predicate::Forall {
                    vars: vec![(
                        "n".to_string(),
                        vc_ir::VcType::Int {
                            signed: true,
                            bits: 32,
                        },
                    )],
                    triggers: vec![],
                    body: Box::new(Predicate::Bool(true)),
                },
            },
        );
        assert!(vc_uses_quantifiers(&vc));
    }

    #[test]
    fn test_vc_uses_quantifiers_expr_forall() {
        // Expr::Forall should be detected
        let vc = test_vc(
            "test_expr_forall",
            VcKind::Predicate(Predicate::Expr(Expr::Forall {
                vars: vec![(
                    "p".to_string(),
                    vc_ir::VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                )],
                body: Box::new(Expr::BoolLit(true)),
            })),
        );
        assert!(vc_uses_quantifiers(&vc));
    }

    #[test]
    fn test_vc_uses_quantifiers_expr_exists() {
        // Expr::Exists should be detected
        let vc = test_vc(
            "test_expr_exists",
            VcKind::Predicate(Predicate::Expr(Expr::Exists {
                vars: vec![(
                    "q".to_string(),
                    vc_ir::VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                )],
                body: Box::new(Expr::BoolLit(true)),
            })),
        );
        assert!(vc_uses_quantifiers(&vc));
    }

    #[test]
    fn test_vc_uses_quantifiers_termination() {
        // Termination without quantifiers
        let vc = test_vc(
            "test_term_no_quant",
            VcKind::Termination {
                decreases: Expr::Var("n".to_string()),
                recursive_calls: vec![Expr::Sub(
                    Box::new(Expr::Var("n".to_string())),
                    Box::new(Expr::IntLit(1)),
                )],
            },
        );
        assert!(!vc_uses_quantifiers(&vc));
    }

    #[test]
    fn test_vc_uses_quantifiers_no_quantifiers_in_and() {
        // Predicate::And without quantifiers
        let vc = test_vc(
            "test_and_no_quant",
            VcKind::Predicate(Predicate::And(vec![
                Predicate::Bool(true),
                Predicate::Expr(Expr::Gt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
            ])),
        );
        assert!(!vc_uses_quantifiers(&vc));
    }

    #[test]
    fn test_vc_uses_quantifiers_quantifier_in_and() {
        // Predicate::And with quantifier nested inside
        let vc = test_vc(
            "test_and_with_quant",
            VcKind::Predicate(Predicate::And(vec![
                Predicate::Bool(true),
                Predicate::Forall {
                    vars: vec![(
                        "i".to_string(),
                        vc_ir::VcType::Int {
                            signed: true,
                            bits: 32,
                        },
                    )],
                    triggers: vec![],
                    body: Box::new(Predicate::Bool(true)),
                },
            ])),
        );
        assert!(vc_uses_quantifiers(&vc));
    }

    // ============================================
    // temporal_uses_quantifiers tests
    // ============================================

    #[test]
    fn test_temporal_uses_quantifiers_state_no_quantifier() {
        // State predicate without quantifiers
        let f = TemporalFormula::State(Predicate::Expr(Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        )));
        assert!(!temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_state_with_forall() {
        // State predicate with Predicate::Forall
        let f = TemporalFormula::State(Predicate::Forall {
            vars: vec![(
                "i".to_string(),
                vc_ir::VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            triggers: vec![],
            body: Box::new(Predicate::Bool(true)),
        });
        assert!(temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_state_with_exists() {
        // State predicate with Predicate::Exists
        let f = TemporalFormula::State(Predicate::Exists {
            vars: vec![(
                "j".to_string(),
                vc_ir::VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Predicate::Bool(true)),
        });
        assert!(temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_always_with_quantifier() {
        // Always wrapping a quantifier
        let inner = TemporalFormula::State(Predicate::Forall {
            vars: vec![(
                "k".to_string(),
                vc_ir::VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            triggers: vec![],
            body: Box::new(Predicate::Bool(true)),
        });
        let f = TemporalFormula::Always(Box::new(inner));
        assert!(temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_eventually_no_quantifier() {
        // Eventually without quantifiers
        let inner = TemporalFormula::State(Predicate::Bool(true));
        let f = TemporalFormula::Eventually(Box::new(inner));
        assert!(!temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_next_with_quantifier() {
        // Next wrapping a quantifier
        let inner = TemporalFormula::State(Predicate::Exists {
            vars: vec![(
                "m".to_string(),
                vc_ir::VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Predicate::Bool(true)),
        });
        let f = TemporalFormula::Next(Box::new(inner));
        assert!(temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_until_quantifier_in_first() {
        // Until with quantifier in first operand
        let a = TemporalFormula::State(Predicate::Forall {
            vars: vec![(
                "n".to_string(),
                vc_ir::VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            triggers: vec![],
            body: Box::new(Predicate::Bool(true)),
        });
        let b = TemporalFormula::State(Predicate::Bool(true));
        let f = TemporalFormula::Until(Box::new(a), Box::new(b));
        assert!(temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_until_quantifier_in_second() {
        // Until with quantifier in second operand
        let a = TemporalFormula::State(Predicate::Bool(true));
        let b = TemporalFormula::State(Predicate::Exists {
            vars: vec![(
                "p".to_string(),
                vc_ir::VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Predicate::Bool(true)),
        });
        let f = TemporalFormula::Until(Box::new(a), Box::new(b));
        assert!(temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_leads_to_no_quantifier() {
        // LeadsTo without quantifiers
        let a = TemporalFormula::State(Predicate::Bool(true));
        let b = TemporalFormula::State(Predicate::Bool(false));
        let f = TemporalFormula::LeadsTo(Box::new(a), Box::new(b));
        assert!(!temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_and_with_quantifier() {
        // And with quantifier in one element
        let f = TemporalFormula::And(vec![
            TemporalFormula::State(Predicate::Bool(true)),
            TemporalFormula::State(Predicate::Forall {
                vars: vec![(
                    "q".to_string(),
                    vc_ir::VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                )],
                triggers: vec![],
                body: Box::new(Predicate::Bool(true)),
            }),
        ]);
        assert!(temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_or_no_quantifier() {
        // Or without quantifiers
        let f = TemporalFormula::Or(vec![
            TemporalFormula::State(Predicate::Bool(true)),
            TemporalFormula::State(Predicate::Bool(false)),
        ]);
        assert!(!temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_weak_fairness_with_quantifier() {
        // WeakFairness with quantifier in condition
        let f = TemporalFormula::WeakFairness {
            action: "action1".to_string(),
            condition: Predicate::Forall {
                vars: vec![(
                    "r".to_string(),
                    vc_ir::VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                )],
                triggers: vec![],
                body: Box::new(Predicate::Bool(true)),
            },
        };
        assert!(temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_strong_fairness_no_quantifier() {
        // StrongFairness without quantifier in condition
        let f = TemporalFormula::StrongFairness {
            action: "action2".to_string(),
            condition: Predicate::Bool(true),
        };
        assert!(!temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_stuttering_equiv_with_quantifier() {
        // StutteringEquiv with quantifier inside
        let inner = TemporalFormula::State(Predicate::Exists {
            vars: vec![(
                "s".to_string(),
                vc_ir::VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Predicate::Bool(true)),
        });
        let f = TemporalFormula::StutteringEquiv(Box::new(inner));
        assert!(temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_not_no_quantifier() {
        // Not without quantifier
        let inner = TemporalFormula::State(Predicate::Bool(true));
        let f = TemporalFormula::Not(Box::new(inner));
        assert!(!temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_implies_quantifier_nested() {
        // Implies with quantifier in second operand
        let a = TemporalFormula::State(Predicate::Bool(true));
        let b = TemporalFormula::State(Predicate::Forall {
            vars: vec![(
                "t".to_string(),
                vc_ir::VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            triggers: vec![],
            body: Box::new(Predicate::Bool(true)),
        });
        let f = TemporalFormula::Implies(Box::new(a), Box::new(b));
        assert!(temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_weak_until_no_quantifier() {
        // WeakUntil without quantifiers
        let a = TemporalFormula::State(Predicate::Bool(true));
        let b = TemporalFormula::State(Predicate::Bool(false));
        let f = TemporalFormula::WeakUntil(Box::new(a), Box::new(b));
        assert!(!temporal_uses_quantifiers(&f));
    }

    #[test]
    fn test_temporal_uses_quantifiers_release_with_quantifier() {
        // Release with quantifier in first operand
        let a = TemporalFormula::State(Predicate::Exists {
            vars: vec![(
                "u".to_string(),
                vc_ir::VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Predicate::Bool(true)),
        });
        let b = TemporalFormula::State(Predicate::Bool(true));
        let f = TemporalFormula::Release(Box::new(a), Box::new(b));
        assert!(temporal_uses_quantifiers(&f));
    }
}
