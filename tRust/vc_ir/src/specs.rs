//! Specification types parsed from Rust attributes
//!
//! These represent the source-level specifications before they're
//! lowered to verification conditions.

use crate::{Expr, Predicate, SourceSpan, TemporalFormula};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;

/// Effect variable for effect polymorphism
///
/// Represents a named effect parameter that can be bound to the effects
/// of a function parameter (for higher-order functions).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EffectVar(pub String);

impl EffectVar {
    #[must_use]
    pub fn new(name: &str) -> Self {
        Self(name.to_string())
    }

    #[must_use]
    pub fn name(&self) -> &str {
        &self.0
    }
}

/// Source of effects for polymorphic effect tracking
///
/// Allows effects to come from concrete sets, effect variables, or
/// the effects of function parameters (for higher-order functions).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum EffectSource {
    /// Concrete effect set
    Concrete(Vec<Effect>),
    /// Effect variable (bound elsewhere)
    Variable(EffectVar),
    /// Effects of a named function parameter (for closures/callbacks)
    ParameterEffects(String),
    /// Union of multiple effect sources
    Union(Vec<EffectSource>),
}

impl Default for EffectSource {
    fn default() -> Self {
        Self::Concrete(vec![])
    }
}

impl EffectSource {
    /// Create a concrete effect source from a set
    pub fn concrete(effects: impl IntoIterator<Item = Effect>) -> Self {
        Self::Concrete(effects.into_iter().collect())
    }

    /// Create an effect variable reference
    #[must_use]
    pub fn var(name: &str) -> Self {
        Self::Variable(EffectVar::new(name))
    }

    /// Create a parameter effects reference
    #[must_use]
    pub fn param(name: &str) -> Self {
        Self::ParameterEffects(name.to_string())
    }

    /// Create a union of effect sources
    #[must_use]
    pub fn union(sources: Vec<Self>) -> Self {
        // Flatten nested unions
        let mut flattened = Vec::new();
        for source in sources {
            match source {
                Self::Union(inner) => flattened.extend(inner),
                other => flattened.push(other),
            }
        }
        // Simplify single-element unions
        if flattened.len() == 1 {
            flattened.pop().expect("len()==1 guarantees element exists")
        } else {
            Self::Union(flattened)
        }
    }

    /// Check if this is a pure (empty concrete) effect source
    #[must_use]
    pub const fn is_pure(&self) -> bool {
        matches!(self, Self::Concrete(effects) if effects.is_empty())
    }

    /// Check if this source is fully concrete (no variables or parameters)
    pub fn is_concrete(&self) -> bool {
        match self {
            Self::Concrete(_) => true,
            Self::Variable(_) | Self::ParameterEffects(_) => false,
            Self::Union(sources) => sources.iter().all(Self::is_concrete),
        }
    }

    /// Get all effect variables referenced by this source
    #[must_use]
    pub fn effect_vars(&self) -> Vec<&EffectVar> {
        match self {
            Self::Concrete(_) | Self::ParameterEffects(_) => vec![],
            Self::Variable(v) => vec![v],
            Self::Union(sources) => sources.iter().flat_map(|s| s.effect_vars()).collect(),
        }
    }

    /// Get all parameter names whose effects are referenced
    #[must_use]
    pub fn param_refs(&self) -> Vec<&str> {
        match self {
            Self::Concrete(_) | Self::Variable(_) => vec![],
            Self::ParameterEffects(p) => vec![p.as_str()],
            Self::Union(sources) => sources.iter().flat_map(|s| s.param_refs()).collect(),
        }
    }

    /// Convert to concrete EffectSet if fully concrete
    #[must_use]
    pub fn to_effect_set(&self) -> Option<EffectSet> {
        match self {
            Self::Concrete(effects) => Some(EffectSet::from_effects(effects.iter().copied())),
            Self::Union(sources) => {
                let mut result = EffectSet::empty();
                for source in sources {
                    result = result.union(&source.to_effect_set()?);
                }
                Some(result)
            }
            Self::Variable(_) | Self::ParameterEffects(_) => None,
        }
    }

    /// Substitute parameter effects with concrete effect sets
    ///
    /// Given a mapping from parameter names to their effect sets,
    /// replaces ParameterEffects references with concrete effects.
    /// Returns None if any referenced parameter is not in the substitution.
    #[must_use]
    pub fn substitute(
        &self,
        param_effects: &std::collections::HashMap<String, EffectSet>,
    ) -> Option<EffectSet> {
        match self {
            Self::Concrete(effects) => Some(EffectSet::from_effects(effects.iter().copied())),
            Self::Variable(_) => {
                // Effect variables need to be resolved separately
                // For now, we can't substitute them with just param effects
                None
            }
            Self::ParameterEffects(param_name) => param_effects.get(param_name).cloned(),
            Self::Union(sources) => {
                let mut result = EffectSet::empty();
                for source in sources {
                    result = result.union(&source.substitute(param_effects)?);
                }
                Some(result)
            }
        }
    }

    /// Substitute with a fallback for unknown parameters
    ///
    /// Like substitute, but uses a fallback effect set for any
    /// unresolved parameters (e.g., assume all effects for unknown callees).
    #[must_use]
    pub fn substitute_with_fallback(
        &self,
        param_effects: &std::collections::HashMap<String, EffectSet>,
        fallback: &EffectSet,
    ) -> EffectSet {
        match self {
            Self::Concrete(effects) => EffectSet::from_effects(effects.iter().copied()),
            Self::Variable(_) => {
                // Unknown variable gets fallback
                fallback.clone()
            }
            Self::ParameterEffects(param_name) => param_effects
                .get(param_name)
                .cloned()
                .unwrap_or_else(|| fallback.clone()),
            Self::Union(sources) => {
                let mut result = EffectSet::empty();
                for source in sources {
                    result =
                        result.union(&source.substitute_with_fallback(param_effects, fallback));
                }
                result
            }
        }
    }
}

// ============================================
// Effect-Based Optimization (Phase 5.3)
// ============================================

/// Effect-based optimization hint
///
/// These hints are derived from effect analysis and enable
/// compiler optimizations based on proven effect properties.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EffectOptimization {
    /// Function is pure (no effects) - results can be memoized/cached
    ///
    /// When a function has no effects, calling it multiple times with
    /// the same arguments will always produce the same result. The
    /// compiler can safely cache results and reuse them.
    Memoizable,

    /// Function cannot panic - unwind tables not needed
    ///
    /// When a function is proven to never panic, the compiler can
    /// skip generating unwind tables and landing pads, reducing
    /// code size and improving performance.
    NoUnwind,

    /// Function doesn't allocate - safe for embedded/no_std contexts
    ///
    /// When a function never allocates heap memory, it can be used
    /// in embedded systems, kernel code, and other environments
    /// where dynamic allocation is not available.
    EmbeddedSafe,

    /// Function has no I/O - safe for const evaluation
    ///
    /// When a function performs no I/O operations, it may be
    /// eligible for compile-time evaluation (const fn candidate).
    ConstEvalCandidate,

    /// Function has no global state mutation - thread-safe
    ///
    /// When a function doesn't mutate global state, it can be
    /// safely called from multiple threads without synchronization.
    ThreadSafe,

    /// Function has no unsafe operations - memory safe
    ///
    /// When a function uses no unsafe operations, the compiler
    /// has full visibility into memory safety properties.
    MemorySafe,
}

impl EffectOptimization {
    /// Get a human-readable description of this optimization
    #[must_use]
    pub const fn description(&self) -> &'static str {
        match self {
            Self::Memoizable => "function is pure - results can be cached",
            Self::NoUnwind => "function cannot panic - unwind tables not needed",
            Self::EmbeddedSafe => "function doesn't allocate - safe for embedded/no_std",
            Self::ConstEvalCandidate => "function has no I/O - const eval candidate",
            Self::ThreadSafe => "function has no global state mutation - thread-safe",
            Self::MemorySafe => "function has no unsafe operations - memory safe",
        }
    }

    /// Get a short name for this optimization
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            Self::Memoizable => "memoizable",
            Self::NoUnwind => "no_unwind",
            Self::EmbeddedSafe => "embedded_safe",
            Self::ConstEvalCandidate => "const_eval",
            Self::ThreadSafe => "thread_safe",
            Self::MemorySafe => "memory_safe",
        }
    }
}

/// Set of effect-based optimizations for a function
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct EffectOptimizations {
    /// The optimizations enabled for this function
    optimizations: HashSet<EffectOptimization>,
    /// The source of the optimization (inferred, declared, or both)
    source: OptimizationSource,
}

/// Source of effect optimization determination
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum OptimizationSource {
    /// Optimizations were inferred from code analysis
    #[default]
    Inferred,
    /// Optimizations were declared via attributes
    Declared,
    /// Both declared and verified by inference
    Verified,
}

impl EffectOptimizations {
    /// Create empty optimization set
    #[must_use]
    pub fn empty() -> Self {
        Self {
            optimizations: HashSet::new(),
            source: OptimizationSource::Inferred,
        }
    }

    /// Create from a set of optimizations
    pub fn from_optimizations(opts: impl IntoIterator<Item = EffectOptimization>) -> Self {
        Self {
            optimizations: opts.into_iter().collect(),
            source: OptimizationSource::Inferred,
        }
    }

    /// Add an optimization
    pub fn add(&mut self, opt: EffectOptimization) {
        self.optimizations.insert(opt);
    }

    /// Check if an optimization is enabled
    #[must_use]
    pub fn has(&self, opt: EffectOptimization) -> bool {
        self.optimizations.contains(&opt)
    }

    /// Check if the function is memoizable
    #[must_use]
    pub fn is_memoizable(&self) -> bool {
        self.has(EffectOptimization::Memoizable)
    }

    /// Check if the function needs no unwind tables
    #[must_use]
    pub fn is_no_unwind(&self) -> bool {
        self.has(EffectOptimization::NoUnwind)
    }

    /// Check if the function is embedded-safe (no allocation)
    #[must_use]
    pub fn is_embedded_safe(&self) -> bool {
        self.has(EffectOptimization::EmbeddedSafe)
    }

    /// Get all optimizations
    pub fn iter(&self) -> impl Iterator<Item = &EffectOptimization> {
        self.optimizations.iter()
    }

    /// Get the number of optimizations
    #[must_use]
    pub fn len(&self) -> usize {
        self.optimizations.len()
    }

    /// Check if no optimizations are enabled
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.optimizations.is_empty()
    }

    /// Set the source of these optimizations
    #[must_use]
    pub const fn with_source(mut self, source: OptimizationSource) -> Self {
        self.source = source;
        self
    }

    /// Get the source of these optimizations
    #[must_use]
    pub const fn source(&self) -> OptimizationSource {
        self.source
    }

    /// Derive optimizations from an effect set
    ///
    /// This is the core function that maps effect analysis to
    /// optimization opportunities.
    #[must_use]
    pub fn from_effects(effects: &EffectSet) -> Self {
        let mut opts = Self::empty();

        // Pure function (no effects) -> memoizable
        if effects.is_pure() {
            opts.add(EffectOptimization::Memoizable);
            opts.add(EffectOptimization::NoUnwind);
            opts.add(EffectOptimization::EmbeddedSafe);
            opts.add(EffectOptimization::ConstEvalCandidate);
            opts.add(EffectOptimization::ThreadSafe);
            opts.add(EffectOptimization::MemorySafe);
        } else {
            // No Panic -> no unwind tables needed
            if !effects.has(Effect::Panic) {
                opts.add(EffectOptimization::NoUnwind);
            }

            // No Alloc -> embedded-safe
            if !effects.has(Effect::Alloc) {
                opts.add(EffectOptimization::EmbeddedSafe);
            }

            // No IO -> const eval candidate
            if !effects.has(Effect::IO) {
                opts.add(EffectOptimization::ConstEvalCandidate);
            }

            // No GlobalState -> thread-safe
            if !effects.has(Effect::GlobalState) {
                opts.add(EffectOptimization::ThreadSafe);
            }

            // No Unsafe -> memory safe
            if !effects.has(Effect::Unsafe) {
                opts.add(EffectOptimization::MemorySafe);
            }
        }

        opts
    }

    /// Convert to a list of optimization names (for display)
    pub fn to_names(&self) -> Vec<&'static str> {
        self.optimizations
            .iter()
            .map(EffectOptimization::name)
            .collect()
    }
}

/// Computational effect that a function may have
///
/// Effects track what kind of side effects a function can produce.
/// Pure functions have no effects (empty set).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Effect {
    /// I/O operations (file, network, console)
    IO,
    /// Heap allocation
    Alloc,
    /// May panic/abort
    Panic,
    /// May diverge (non-termination)
    Diverge,
    /// Unsafe operations (raw pointers, FFI)
    Unsafe,
    /// Global state mutation
    GlobalState,
}

impl Effect {
    /// Parse effect from string (case-insensitive)
    #[must_use]
    pub fn parse(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "io" => Some(Self::IO),
            "alloc" => Some(Self::Alloc),
            "panic" => Some(Self::Panic),
            "diverge" => Some(Self::Diverge),
            "unsafe" => Some(Self::Unsafe),
            "globalstate" | "global_state" => Some(Self::GlobalState),
            _ => None,
        }
    }

    /// Return the string representation
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::IO => "IO",
            Self::Alloc => "Alloc",
            Self::Panic => "Panic",
            Self::Diverge => "Diverge",
            Self::Unsafe => "Unsafe",
            Self::GlobalState => "GlobalState",
        }
    }

    /// All possible effects
    #[must_use]
    pub fn all() -> HashSet<Self> {
        let mut set = HashSet::new();
        set.insert(Self::IO);
        set.insert(Self::Alloc);
        set.insert(Self::Panic);
        set.insert(Self::Diverge);
        set.insert(Self::Unsafe);
        set.insert(Self::GlobalState);
        set
    }
}

/// A set of effects for a function
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct EffectSet {
    effects: HashSet<Effect>,
}

impl EffectSet {
    /// Create an empty effect set (pure)
    #[must_use]
    pub fn empty() -> Self {
        Self {
            effects: HashSet::new(),
        }
    }

    /// Create an effect set from a list of effects
    pub fn from_effects(effects: impl IntoIterator<Item = Effect>) -> Self {
        Self {
            effects: effects.into_iter().collect(),
        }
    }

    /// Check if this is a pure (no effects) set
    #[must_use]
    pub fn is_pure(&self) -> bool {
        self.effects.is_empty()
    }

    /// Check if this set contains a specific effect
    #[must_use]
    pub fn has(&self, effect: Effect) -> bool {
        self.effects.contains(&effect)
    }

    /// Add an effect to the set
    pub fn add(&mut self, effect: Effect) {
        self.effects.insert(effect);
    }

    /// Get all effects in the set
    pub fn iter(&self) -> impl Iterator<Item = &Effect> {
        self.effects.iter()
    }

    /// Check if this effect set is a subset of another (for effect checking)
    ///
    /// A function with effects E1 can call functions with effects E2 only if E2 ⊆ E1
    #[must_use]
    pub fn is_subset_of(&self, other: &Self) -> bool {
        self.effects.is_subset(&other.effects)
    }

    /// Union of two effect sets
    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        Self {
            effects: self.effects.union(&other.effects).copied().collect(),
        }
    }

    /// Effects that are in self but not in other
    #[must_use]
    pub fn difference(&self, other: &Self) -> Self {
        Self {
            effects: self.effects.difference(&other.effects).copied().collect(),
        }
    }

    /// Parse from comma-separated string
    #[must_use]
    pub fn parse(s: &str) -> Self {
        let effects = s
            .split(',')
            .filter_map(|part| Effect::parse(part.trim()))
            .collect();
        Self { effects }
    }

    /// Convert to comma-separated string
    #[allow(clippy::inherent_to_string)]
    pub fn to_string(&self) -> String {
        self.effects
            .iter()
            .map(Effect::as_str)
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// A complete specification for a function
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct FunctionSpec {
    /// Preconditions: #[requires(...)]
    pub requires: Vec<SpecClause>,
    /// Postconditions: #[ensures(...)]
    pub ensures: Vec<SpecClause>,
    /// Termination measure: #[decreases(...)]
    pub decreases: Option<DecreasesClause>,
    /// Temporal properties: #[temporal(...)]
    pub temporal: Vec<TemporalClause>,
    /// Purity annotation: `#[pure]`
    /// When true, the function is pure (no effects), equivalent to effects = {}
    pub pure: bool,
    /// Declared effects: `#[effects(IO, Alloc, ...)]`
    /// If None, effects are inferred or assumed to be all effects
    pub effects: Option<EffectSet>,
    /// Polymorphic effect source: `#[effects_of(f)]` or `#[effects(IO, effects_of(f))]`
    /// Allows effects to depend on parameter effects (for higher-order functions)
    pub effect_source: Option<EffectSource>,
    /// May diverge annotation: `#[may_diverge]`
    pub may_diverge: bool,
    /// Trusted (no verification): `#[trusted]`
    pub trusted: bool,
}

impl FunctionSpec {
    /// Get the effective effect set for this function
    ///
    /// - If `pure` is true, returns empty effect set
    /// - If `effects` is Some, returns those effects
    /// - Otherwise, returns None (effects not declared)
    #[must_use]
    pub fn effective_effects(&self) -> Option<EffectSet> {
        if self.pure {
            Some(EffectSet::empty())
        } else {
            self.effects.clone()
        }
    }

    /// Get the polymorphic effect source
    ///
    /// Returns the effect source which may include parameter effects.
    /// For non-polymorphic functions, converts concrete effects to EffectSource.
    #[must_use]
    pub fn effect_source(&self) -> Option<EffectSource> {
        if self.pure {
            Some(EffectSource::Concrete(vec![]))
        } else if let Some(source) = &self.effect_source {
            Some(source.clone())
        } else {
            self.effects
                .as_ref()
                .map(|effects| EffectSource::Concrete(effects.iter().copied().collect()))
        }
    }

    /// Check if this function has polymorphic effects (depends on parameter effects)
    #[must_use]
    pub fn has_polymorphic_effects(&self) -> bool {
        self.effect_source
            .as_ref()
            .is_some_and(|s| !s.is_concrete())
    }

    /// Check if this function is explicitly marked as pure
    #[must_use]
    pub const fn is_pure(&self) -> bool {
        self.pure
    }

    /// Check if this function has declared effects (including pure or polymorphic)
    #[must_use]
    pub const fn has_declared_effects(&self) -> bool {
        self.pure || self.effects.is_some() || self.effect_source.is_some()
    }
}

/// A single specification clause
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpecClause {
    pub pred: Predicate,
    pub span: SourceSpan,
    /// Optional label for error messages
    pub label: Option<String>,
}

/// Termination measure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecreasesClause {
    /// The expression that must decrease
    pub measure: Expr,
    /// Optional: explicit well-founded relation
    pub relation: Option<WellFoundedRelation>,
    pub span: SourceSpan,
}

/// Well-founded relation for termination proofs
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WellFoundedRelation {
    /// Natural number ordering (default for unsigned integers)
    Nat,
    /// Lexicographic ordering on tuples
    Lex,
    /// Custom relation (must prove well-foundedness)
    Custom(String),
}

/// Temporal specification clause
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TemporalClause {
    pub formula: TemporalFormula,
    pub span: SourceSpan,
}

/// A complete specification for a type (struct/enum)
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TypeSpec {
    /// Type invariants: #[invariant(...)]
    pub invariants: Vec<SpecClause>,
    /// Representation invariants (for unsafe code)
    pub rep_invariants: Vec<SpecClause>,
}

/// A complete specification for a trait
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TraitSpec {
    /// Trait-level invariants
    pub invariants: Vec<SpecClause>,
    /// Method specifications
    pub methods: Vec<(String, FunctionSpec)>,
}

/// Loop specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoopSpec {
    /// Loop invariants: #[invariant(...)]
    pub invariants: Vec<SpecClause>,
    /// Loop variant (for termination): #[decreases(...)]
    pub variant: Option<DecreasesClause>,
}

/// Ghost code block (exists only for proofs, compiles away)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GhostBlock {
    /// The ghost statements
    pub stmts: Vec<GhostStmt>,
    pub span: SourceSpan,
}

/// Ghost statement (proof-only code)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum GhostStmt {
    /// Ghost variable declaration
    Let { name: String, value: Expr },
    /// Assert for proof structure
    Assert(Predicate),
    /// Assume (dangerous! creates proof obligation elsewhere)
    Assume(Predicate),
    /// Unfold a recursive predicate
    Unfold { pred: String, args: Vec<Expr> },
    /// Fold a recursive predicate
    Fold { pred: String, args: Vec<Expr> },
    /// Lemma invocation
    Lemma { name: String, args: Vec<Expr> },
}

// ============================================
// Lemma Definitions (Phase 8.2)
// ============================================

/// A lemma definition - a proven property that can be used in other proofs
///
/// Lemmas are auxiliary theorems that help prove the main verification goals.
/// When a proof fails, users can define lemmas to provide intermediate facts
/// that the SMT solver can use.
///
/// # Example
/// ```ignore
/// #[lemma]
/// #[requires("n >= 0")]
/// #[ensures("sum(n) == n * (n + 1) / 2")]
/// fn sum_formula(n: i32) {}
///
/// // Later, at a use site:
/// proof! { apply sum_formula(k); }
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LemmaDefinition {
    /// Lemma name (must be unique within crate)
    pub name: String,
    /// Parameters with their types
    pub params: Vec<LemmaParam>,
    /// Preconditions that must hold when applying the lemma (as SMT expressions)
    pub requires: Vec<String>,
    /// Conclusions that can be assumed after applying the lemma (as SMT expressions)
    pub ensures: Vec<String>,
    /// Source location
    pub span: SourceSpan,
    /// Whether this is a built-in lemma (from the standard library)
    pub is_builtin: bool,
}

/// Parameter to a lemma
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LemmaParam {
    /// Parameter name
    pub name: String,
    /// Parameter type (as string for SMT compatibility)
    pub ty: String,
}

impl LemmaDefinition {
    /// Create a new lemma definition
    pub fn new(name: impl Into<String>, span: SourceSpan) -> Self {
        Self {
            name: name.into(),
            params: Vec::new(),
            requires: Vec::new(),
            ensures: Vec::new(),
            span,
            is_builtin: false,
        }
    }

    /// Create a builtin lemma (with placeholder span)
    pub fn builtin(name: impl Into<String>) -> Self {
        use std::sync::Arc;
        Self {
            name: name.into(),
            params: Vec::new(),
            requires: Vec::new(),
            ensures: Vec::new(),
            span: SourceSpan {
                file: Arc::from("<builtin>"),
                line_start: 0,
                line_end: 0,
                col_start: 0,
                col_end: 0,
            },
            is_builtin: true,
        }
    }

    /// Add a parameter
    #[must_use]
    pub fn with_param(mut self, name: impl Into<String>, ty: impl Into<String>) -> Self {
        self.params.push(LemmaParam {
            name: name.into(),
            ty: ty.into(),
        });
        self
    }

    /// Add a precondition (SMT expression string)
    #[must_use]
    pub fn with_requires(mut self, expr: impl Into<String>) -> Self {
        self.requires.push(expr.into());
        self
    }

    /// Add a postcondition/conclusion (SMT expression string)
    #[must_use]
    pub fn with_ensures(mut self, expr: impl Into<String>) -> Self {
        self.ensures.push(expr.into());
        self
    }

    /// Generate SMT-LIB for the lemma as an assertion
    ///
    /// A lemma (forall params. requires => ensures) becomes an SMT assertion
    /// that can be used by the solver.
    #[must_use]
    pub fn to_smt_assertion(&self) -> String {
        let requires = if self.requires.is_empty() {
            "true".to_string()
        } else if self.requires.len() == 1 {
            self.requires[0].clone()
        } else {
            format!("(and {})", self.requires.join(" "))
        };

        let ensures = if self.ensures.is_empty() {
            "true".to_string()
        } else if self.ensures.len() == 1 {
            self.ensures[0].clone()
        } else {
            format!("(and {})", self.ensures.join(" "))
        };

        if self.params.is_empty() {
            // No parameters: simple implication
            format!("(assert (=> {requires} {ensures}))")
        } else {
            // With parameters: quantified formula
            let params: Vec<_> = self
                .params
                .iter()
                .map(|p| format!("({} {})", p.name, smt_type(&p.ty)))
                .collect();

            format!(
                "(assert (forall ({}) (=> {} {})))",
                params.join(" "),
                requires,
                ensures
            )
        }
    }
}

/// Convert a type name to SMT-LIB type
fn smt_type(ty: &str) -> &str {
    match ty {
        "bool" => "Bool",
        // All integer types (i8-i128, u8-u128, isize, usize) and unknowns map to Int
        _ => "Int",
    }
}

/// Result of requesting a lemma when proof fails
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LemmaRequest {
    /// What the proof was trying to establish
    pub goal: String,
    /// Variables in scope at the failure point
    pub variables: Vec<(String, String)>, // (name, type)
    /// Suggested lemma patterns that might help
    pub suggested_patterns: Vec<LemmaSuggestion>,
    /// Source location of the failure
    pub span: SourceSpan,
}

/// A suggestion for a lemma that might help
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LemmaSuggestion {
    /// Human-readable description
    pub description: String,
    /// Suggested lemma skeleton
    pub skeleton: String,
    /// Confidence (0.0 to 1.0) that this lemma would help
    pub confidence: f64,
}

impl LemmaRequest {
    /// Create a new lemma request
    pub fn new(goal: impl Into<String>, span: SourceSpan) -> Self {
        Self {
            goal: goal.into(),
            variables: Vec::new(),
            suggested_patterns: Vec::new(),
            span,
        }
    }

    /// Add a variable in scope
    #[must_use]
    pub fn with_variable(mut self, name: impl Into<String>, ty: impl Into<String>) -> Self {
        self.variables.push((name.into(), ty.into()));
        self
    }

    /// Add a suggestion
    #[must_use]
    pub fn with_suggestion(mut self, suggestion: LemmaSuggestion) -> Self {
        self.suggested_patterns.push(suggestion);
        self
    }
}

impl LemmaSuggestion {
    /// Create a new suggestion
    pub fn new(
        description: impl Into<String>,
        skeleton: impl Into<String>,
        confidence: f64,
    ) -> Self {
        Self {
            description: description.into(),
            skeleton: skeleton.into(),
            confidence: confidence.clamp(0.0, 1.0),
        }
    }
}

// ============================================
// Proof Tactics (Phase 8.3)
// ============================================

/// Kind of proof tactic to apply
///
/// Tactics guide the verifier on how to prove a property when
/// automatic proof fails or is inefficient.
///
/// # Example
/// ```ignore
/// #[tactic(induction(n))]
/// fn sum(n: u32) -> u32 { ... }
///
/// #[tactic(case_split(x >= 0))]
/// fn abs(x: i32) -> i32 { ... }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TacticKind {
    /// Proof by induction on a variable or expression
    ///
    /// Generates base case and inductive step verification conditions.
    /// The induction variable must be well-founded (typically integers or
    /// recursively defined types).
    Induction(InductionTarget),

    /// Proof by case split on a condition
    ///
    /// Splits the proof into two cases: when the condition holds and
    /// when it doesn't. Useful for functions with different behavior
    /// based on conditions.
    CaseSplit(CaseSplitCondition),

    /// Custom tactic by name
    ///
    /// Allows users to register and use custom tactics. The verifier
    /// looks up the tactic in a registry and applies it.
    Custom(String),
}

impl TacticKind {
    /// Create an induction tactic on a named variable
    pub fn induction(var: impl Into<String>) -> Self {
        Self::Induction(InductionTarget::Variable(var.into()))
    }

    /// Create an induction tactic on a parameter by index
    #[must_use]
    pub const fn induction_param(index: usize) -> Self {
        Self::Induction(InductionTarget::Parameter(index))
    }

    /// Create a case split tactic on a condition expression
    pub fn case_split(condition: impl Into<String>) -> Self {
        Self::CaseSplit(CaseSplitCondition::Expression(condition.into()))
    }

    /// Create a case split tactic on the sign of a variable
    pub fn case_split_sign(var: impl Into<String>) -> Self {
        Self::CaseSplit(CaseSplitCondition::Sign(var.into()))
    }

    /// Create a custom tactic
    pub fn custom(name: impl Into<String>) -> Self {
        Self::Custom(name.into())
    }

    /// Get a human-readable description of the tactic
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::Induction(target) => format!("induction on {}", target.description()),
            Self::CaseSplit(cond) => format!("case split on {}", cond.description()),
            Self::Custom(name) => format!("custom tactic '{name}'"),
        }
    }
}

/// Target for induction proofs
///
/// Specifies what to induct on: a named variable, a function parameter,
/// or a tuple of variables for structural induction on multiple values.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum InductionTarget {
    /// Induct on a named variable in scope
    Variable(String),
    /// Induct on a function parameter by index (0-based)
    Parameter(usize),
    /// Simultaneous induction on multiple variables (structural induction)
    Tuple(Vec<String>),
    /// Induct on the structure of a recursive type
    Structural(String),
}

impl InductionTarget {
    /// Create a variable target
    pub fn var(name: impl Into<String>) -> Self {
        Self::Variable(name.into())
    }

    /// Create a parameter target
    #[must_use]
    pub const fn param(index: usize) -> Self {
        Self::Parameter(index)
    }

    /// Create a tuple target
    pub fn tuple(vars: impl IntoIterator<Item = impl Into<String>>) -> Self {
        Self::Tuple(vars.into_iter().map(std::convert::Into::into).collect())
    }

    /// Create a structural target
    pub fn structural(ty: impl Into<String>) -> Self {
        Self::Structural(ty.into())
    }

    /// Get a human-readable description
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::Variable(v) => v.clone(),
            Self::Parameter(i) => format!("parameter {i}"),
            Self::Tuple(vars) => format!("({})", vars.join(", ")),
            Self::Structural(ty) => format!("structure of {ty}"),
        }
    }
}

/// Condition for case split proofs
///
/// Specifies how to split the proof into cases.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CaseSplitCondition {
    /// Split on an arbitrary boolean expression
    Expression(String),
    /// Split on the sign of a variable (x >= 0 vs x < 0)
    Sign(String),
    /// Split on enumeration variants
    Enum { var: String, variants: Vec<String> },
    /// Split on Option (Some vs None)
    Option(String),
    /// Split on Result (Ok vs Err)
    Result(String),
}

impl CaseSplitCondition {
    /// Create an expression condition
    pub fn expr(e: impl Into<String>) -> Self {
        Self::Expression(e.into())
    }

    /// Create a sign condition
    pub fn sign(var: impl Into<String>) -> Self {
        Self::Sign(var.into())
    }

    /// Create an enum condition
    pub fn enum_split(var: impl Into<String>, variants: Vec<String>) -> Self {
        Self::Enum {
            var: var.into(),
            variants,
        }
    }

    /// Create an Option condition
    pub fn option(var: impl Into<String>) -> Self {
        Self::Option(var.into())
    }

    /// Create a Result condition
    pub fn result(var: impl Into<String>) -> Self {
        Self::Result(var.into())
    }

    /// Get a human-readable description
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::Expression(e) => e.clone(),
            Self::Sign(v) => format!("{v} >= 0"),
            Self::Enum { var, variants } => {
                format!("{} ∈ {{{}}}", var, variants.join(", "))
            }
            Self::Option(v) => format!("{v}.is_some()"),
            Self::Result(v) => format!("{v}.is_ok()"),
        }
    }

    /// Get the cases as condition strings for verification
    #[must_use]
    pub fn get_cases(&self) -> Vec<(String, String)> {
        match self {
            Self::Expression(e) => vec![
                (format!("case: {e}"), e.clone()),
                (format!("case: ¬({e})"), format!("(not {e})")),
            ],
            Self::Sign(v) => vec![
                (format!("case: {v} >= 0"), format!("(>= {v} 0)")),
                (format!("case: {v} < 0"), format!("(< {v} 0)")),
            ],
            Self::Enum { var, variants } => variants
                .iter()
                .map(|variant| {
                    (
                        format!("case: {var} is {variant}"),
                        format!("(is-{variant} {var})"),
                    )
                })
                .collect(),
            Self::Option(v) => vec![
                (format!("case: {v}.is_some()"), format!("(is-Some {v})")),
                (format!("case: {v}.is_none()"), format!("(is-None {v})")),
            ],
            Self::Result(v) => vec![
                (format!("case: {v}.is_ok()"), format!("(is-Ok {v})")),
                (format!("case: {v}.is_err()"), format!("(is-Err {v})")),
            ],
        }
    }
}

/// Complete tactic annotation from source
///
/// Contains the tactic kind plus metadata about where it appears and
/// any additional hints.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TacticAnnotation {
    /// The kind of tactic
    pub kind: TacticKind,
    /// Source location of the annotation
    pub span: SourceSpan,
    /// Optional label for error messages
    pub label: Option<String>,
    /// Additional hints for the verifier (tactic-specific)
    pub hints: Vec<TacticHint>,
}

impl TacticAnnotation {
    /// Create a new tactic annotation
    #[must_use]
    pub const fn new(kind: TacticKind, span: SourceSpan) -> Self {
        Self {
            kind,
            span,
            label: None,
            hints: Vec::new(),
        }
    }

    /// Add a label
    #[must_use]
    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.label = Some(label.into());
        self
    }

    /// Add a hint
    #[must_use]
    pub fn with_hint(mut self, hint: TacticHint) -> Self {
        self.hints.push(hint);
        self
    }

    /// Generate a description for error messages
    #[must_use]
    pub fn format_description(&self) -> String {
        let base = self.kind.description();
        match &self.label {
            Some(l) => format!("{base} ({l})"),
            None => base,
        }
    }
}

/// Additional hints for tactics
///
/// These provide extra guidance to the verifier beyond the basic
/// tactic specification.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TacticHint {
    /// Base case value for induction (default: 0 for integers)
    BaseCase(String),
    /// Step size for induction (default: 1)
    StepSize(i64),
    /// Lemmas to use in the proof
    UseLemmas(Vec<String>),
    /// Maximum recursion depth for structural induction
    MaxDepth(usize),
    /// Timeout hint for this particular tactic (milliseconds)
    Timeout(u64),
}

impl TacticHint {
    /// Create a base case hint
    pub fn base_case(expr: impl Into<String>) -> Self {
        Self::BaseCase(expr.into())
    }

    /// Create a step size hint
    #[must_use]
    pub const fn step(n: i64) -> Self {
        Self::StepSize(n)
    }

    /// Create a lemma usage hint
    #[must_use]
    pub const fn use_lemmas(lemmas: Vec<String>) -> Self {
        Self::UseLemmas(lemmas)
    }

    /// Create a max depth hint
    #[must_use]
    pub const fn max_depth(depth: usize) -> Self {
        Self::MaxDepth(depth)
    }

    /// Create a timeout hint
    #[must_use]
    pub const fn timeout(ms: u64) -> Self {
        Self::Timeout(ms)
    }
}

/// Registry for custom tactics
///
/// Allows users to register custom tactics that the verifier can apply.
/// Each custom tactic defines how to transform verification conditions.
#[derive(Debug, Clone, Default)]
pub struct TacticRegistry {
    /// Registered custom tactics
    tactics: std::collections::HashMap<String, CustomTactic>,
}

/// A custom user-defined tactic
#[derive(Debug, Clone)]
pub struct CustomTactic {
    /// Tactic name
    pub name: String,
    /// Human-readable description
    pub description: String,
    /// How the tactic transforms verification conditions
    pub transform: TacticTransform,
}

/// How a tactic transforms verification conditions
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TacticTransform {
    /// Split into multiple subgoals
    Split { subgoals: Vec<String> },
    /// Add assumptions (lemmas)
    Assume { assumptions: Vec<String> },
    /// Unfold a definition
    Unfold { name: String },
    /// Apply simplification rules
    Simplify,
    /// Combine multiple transforms
    Sequence(Vec<TacticTransform>),
}

impl TacticRegistry {
    /// Create an empty registry
    #[must_use]
    pub fn new() -> Self {
        Self {
            tactics: std::collections::HashMap::new(),
        }
    }

    /// Register a custom tactic
    pub fn register(&mut self, tactic: CustomTactic) {
        self.tactics.insert(tactic.name.clone(), tactic);
    }

    /// Look up a tactic by name
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&CustomTactic> {
        self.tactics.get(name)
    }

    /// Check if a tactic is registered
    #[must_use]
    pub fn contains(&self, name: &str) -> bool {
        self.tactics.contains_key(name)
    }

    /// Get all registered tactic names
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.tactics.keys().map(std::string::String::as_str)
    }
}

impl CustomTactic {
    /// Create a new custom tactic
    pub fn new(
        name: impl Into<String>,
        description: impl Into<String>,
        transform: TacticTransform,
    ) -> Self {
        Self {
            name: name.into(),
            description: description.into(),
            transform,
        }
    }
}

/// Refinement type definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RefinementType {
    /// Base type
    pub base: String,
    /// Refinement predicate (self refers to the value)
    pub refinement: Predicate,
    pub span: SourceSpan,
}

// ============================================
// Common Lemma Library (Phase 8.2)
// ============================================

/// Library of common lemmas for frequently-needed properties
///
/// These built-in lemmas cover arithmetic properties, bounds, and
/// common patterns that are often needed when proofs fail.
pub mod builtin_lemmas {
    use super::LemmaDefinition;

    /// Get all built-in arithmetic lemmas
    #[must_use]
    pub fn arithmetic_lemmas() -> Vec<LemmaDefinition> {
        vec![
            // Addition is commutative: a + b = b + a
            LemmaDefinition::builtin("add_commutative")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_ensures("(= (+ a b) (+ b a))"),
            // Addition is associative: (a + b) + c = a + (b + c)
            LemmaDefinition::builtin("add_associative")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_param("c", "i32")
                .with_ensures("(= (+ (+ a b) c) (+ a (+ b c)))"),
            // Addition identity: a + 0 = a
            LemmaDefinition::builtin("add_identity")
                .with_param("a", "i32")
                .with_ensures("(= (+ a 0) a)"),
            // Multiplication is commutative: a * b = b * a
            LemmaDefinition::builtin("mul_commutative")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_ensures("(= (* a b) (* b a))"),
            // Multiplication is associative
            LemmaDefinition::builtin("mul_associative")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_param("c", "i32")
                .with_ensures("(= (* (* a b) c) (* a (* b c)))"),
            // Multiplication identity: a * 1 = a
            LemmaDefinition::builtin("mul_identity")
                .with_param("a", "i32")
                .with_ensures("(= (* a 1) a)"),
            // Multiplication by zero: a * 0 = 0
            LemmaDefinition::builtin("mul_zero")
                .with_param("a", "i32")
                .with_ensures("(= (* a 0) 0)"),
            // Distributivity: a * (b + c) = a * b + a * c
            LemmaDefinition::builtin("distributive")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_param("c", "i32")
                .with_ensures("(= (* a (+ b c)) (+ (* a b) (* a c)))"),
        ]
    }

    /// Get lemmas for non-negativity and sign properties
    #[must_use]
    pub fn sign_lemmas() -> Vec<LemmaDefinition> {
        vec![
            // Square is non-negative: a^2 >= 0
            LemmaDefinition::builtin("square_nonneg")
                .with_param("a", "i32")
                .with_ensures("(>= (* a a) 0)"),
            // Product of non-negatives is non-negative
            LemmaDefinition::builtin("mul_nonneg")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_requires("(>= a 0)")
                .with_requires("(>= b 0)")
                .with_ensures("(>= (* a b) 0)"),
            // Sum of non-negatives is non-negative
            LemmaDefinition::builtin("add_nonneg")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_requires("(>= a 0)")
                .with_requires("(>= b 0)")
                .with_ensures("(>= (+ a b) 0)"),
            // Absolute value is non-negative (definitional)
            LemmaDefinition::builtin("abs_nonneg")
                .with_param("a", "i32")
                .with_ensures("(>= (ite (>= a 0) a (- a)) 0)"),
        ]
    }

    /// Get lemmas for ordering and bounds
    #[must_use]
    pub fn ordering_lemmas() -> Vec<LemmaDefinition> {
        vec![
            // Transitivity of less-than-or-equal
            LemmaDefinition::builtin("le_transitive")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_param("c", "i32")
                .with_requires("(<= a b)")
                .with_requires("(<= b c)")
                .with_ensures("(<= a c)"),
            // Antisymmetry: a <= b && b <= a => a = b
            LemmaDefinition::builtin("le_antisymmetric")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_requires("(<= a b)")
                .with_requires("(<= b a)")
                .with_ensures("(= a b)"),
            // Trichotomy: a < b or a = b or a > b
            LemmaDefinition::builtin("trichotomy")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_ensures("(or (< a b) (= a b) (> a b))"),
            // Min is less than or equal to both arguments
            LemmaDefinition::builtin("min_le")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_ensures("(and (<= (ite (<= a b) a b) a) (<= (ite (<= a b) a b) b))"),
            // Max is greater than or equal to both arguments
            LemmaDefinition::builtin("max_ge")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_ensures("(and (>= (ite (>= a b) a b) a) (>= (ite (>= a b) a b) b))"),
        ]
    }

    /// Get lemmas for division and modulo
    #[must_use]
    pub fn division_lemmas() -> Vec<LemmaDefinition> {
        vec![
            // Division: a = (a / b) * b + (a % b) when b != 0
            LemmaDefinition::builtin("div_mod_identity")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_requires("(not (= b 0))")
                .with_ensures("(= a (+ (* (div a b) b) (mod a b)))"),
            // Modulo bounds: 0 <= a % b < |b| for positive a
            LemmaDefinition::builtin("mod_bounds")
                .with_param("a", "i32")
                .with_param("b", "i32")
                .with_requires("(> b 0)")
                .with_requires("(>= a 0)")
                .with_ensures("(and (>= (mod a b) 0) (< (mod a b) b))"),
            // Division by 1: a / 1 = a
            LemmaDefinition::builtin("div_identity")
                .with_param("a", "i32")
                .with_ensures("(= (div a 1) a)"),
        ]
    }

    /// Get lemmas for array/slice bounds
    #[must_use]
    pub fn bounds_lemmas() -> Vec<LemmaDefinition> {
        vec![
            // Index in range stays in range after increment (if space)
            LemmaDefinition::builtin("index_increment_in_bounds")
                .with_param("i", "usize")
                .with_param("len", "usize")
                .with_requires("(< (+ i 1) len)")
                .with_ensures("(< (+ i 1) len)"),
            // Zero is valid index for non-empty
            LemmaDefinition::builtin("zero_index_valid")
                .with_param("len", "usize")
                .with_requires("(> len 0)")
                .with_ensures("(< 0 len)"),
            // Last index is len - 1
            LemmaDefinition::builtin("last_index")
                .with_param("len", "usize")
                .with_requires("(> len 0)")
                .with_ensures("(< (- len 1) len)"),
        ]
    }

    /// Get all built-in lemmas
    #[must_use]
    pub fn all_lemmas() -> Vec<LemmaDefinition> {
        let mut all = Vec::new();
        all.extend(arithmetic_lemmas());
        all.extend(sign_lemmas());
        all.extend(ordering_lemmas());
        all.extend(division_lemmas());
        all.extend(bounds_lemmas());
        all
    }

    /// Find a lemma by name
    #[must_use]
    pub fn find_lemma(name: &str) -> Option<LemmaDefinition> {
        all_lemmas().into_iter().find(|l| l.name == name)
    }
}

// ============================================
// Wiring Verification (Phase 6.5)
// ============================================

/// Wire annotation for structural connectivity verification
///
/// Wire annotations prove that code paths exist from entry points
/// through all annotated states. This is valuable for AI-generated
/// code validation where compilation succeeds but code paths may
/// be disconnected.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum WireAnnotation {
    /// Entry point: `#[wire::start]`
    Start,
    /// Named state: `#[wire::state("name")]`
    State(String),
    /// Required successors: `#[wire::must_reach("state1", "state2")]`
    MustReach(Vec<String>),
    /// Recoverable state: `#[wire::recoverable]`
    Recoverable,
    /// Data flow: `#[wire::data_flow(input, output)]`
    DataFlow { input: String, output: String },
    /// Terminal state: `#[wire::terminal]`
    Terminal,
}

/// Wiring specification for a function
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct WireSpec {
    pub annotations: Vec<WireAnnotation>,
    pub span: Option<SourceSpan>,
}

impl WireSpec {
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.annotations.is_empty()
    }
    #[must_use]
    pub fn is_start(&self) -> bool {
        self.annotations
            .iter()
            .any(|a| matches!(a, WireAnnotation::Start))
    }
    #[must_use]
    pub fn is_terminal(&self) -> bool {
        self.annotations
            .iter()
            .any(|a| matches!(a, WireAnnotation::Terminal))
    }
    #[must_use]
    pub fn is_recoverable(&self) -> bool {
        self.annotations
            .iter()
            .any(|a| matches!(a, WireAnnotation::Recoverable))
    }
    #[must_use]
    pub fn state_name(&self) -> Option<&str> {
        self.annotations.iter().find_map(|a| match a {
            WireAnnotation::State(name) => Some(name.as_str()),
            _ => None,
        })
    }
    #[must_use]
    pub fn must_reach(&self) -> Vec<&str> {
        self.annotations
            .iter()
            .filter_map(|a| match a {
                WireAnnotation::MustReach(states) => {
                    Some(states.iter().map(std::string::String::as_str))
                }
                _ => None,
            })
            .flatten()
            .collect()
    }
}

/// Result of wiring verification
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct WireVerifyResult {
    pub unreachable_states: Vec<UnreachableState>,
    pub missing_reaches: Vec<MissingReach>,
    pub unrecoverable_states: Vec<String>,
    pub data_flow_violations: Vec<DataFlowViolation>,
    /// Path anomalies detected (Phase 6.5.4)
    pub path_anomalies: Vec<PathAnomaly>,
}

impl WireVerifyResult {
    #[must_use]
    pub const fn passed(&self) -> bool {
        self.unreachable_states.is_empty()
            && self.missing_reaches.is_empty()
            && self.unrecoverable_states.is_empty()
            && self.data_flow_violations.is_empty()
            && self.path_anomalies.is_empty()
    }
    #[must_use]
    pub const fn violation_count(&self) -> usize {
        self.unreachable_states.len()
            + self.missing_reaches.len()
            + self.unrecoverable_states.len()
            + self.data_flow_violations.len()
            + self.path_anomalies.len()
    }
}

/// Unreachable state violation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnreachableState {
    pub state: String,
    pub function: String,
    pub span: SourceSpan,
}

/// Missing reach violation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MissingReach {
    pub from_function: String,
    pub target_state: String,
    pub span: SourceSpan,
}

/// Data flow violation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataFlowViolation {
    pub function: String,
    pub input: String,
    pub output: String,
    pub reason: String,
    pub span: SourceSpan,
}

// ============================================
// Path Anomaly Detection (Phase 6.5.4)
// ============================================

/// Path anomaly detected in control flow analysis
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PathAnomaly {
    /// Unhandled Result error path
    UnhandledResult(UnhandledResult),
    /// Dead code (unreachable function)
    DeadCode(DeadCode),
    /// Unused computed value
    UnusedValue(UnusedValue),
    /// Missing await on future
    MissingAwait(MissingAwait),
    /// Partial struct update (some fields not initialized)
    PartialStructUpdate(PartialStructUpdate),
    /// Async chain violation (Phase 6.5.2)
    AsyncChainViolation(AsyncChainViolation),
}

/// Unhandled Result error path
///
/// Detects when a function returns Result but the caller ignores
/// or doesn't properly handle the Err case.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnhandledResult {
    /// Function where the unhandled Result is detected
    pub function: String,
    /// The call expression that returns Result
    pub call_site: String,
    /// The callee function that returns Result
    pub callee: String,
    /// How the Result was (mis)handled
    pub handling: ResultHandling,
    /// Source location
    pub span: SourceSpan,
}

/// How a Result value was handled
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResultHandling {
    /// Result was completely ignored (not bound)
    Ignored,
    /// Result was bound but never used
    BoundButUnused,
    /// Result was unwrapped without error handling
    UnwrappedWithoutCheck,
    /// Only Ok path was handled, Err discarded
    OkOnlyHandled,
}

/// Dead code path (unreachable function)
///
/// Detects functions that are defined but never called from any
/// entry point or start function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadCode {
    /// Name of the dead function
    pub function: String,
    /// Why it was flagged as dead
    pub reason: DeadCodeReason,
    /// Source location
    pub span: SourceSpan,
}

/// Reason for dead code detection
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DeadCodeReason {
    /// Not reachable from any start function
    UnreachableFromStart,
    /// Conditionally unreachable (behind always-false condition)
    ConditionallyUnreachable { condition: String },
    /// Never called (no callers found)
    NeverCalled,
    /// Defined but masked by another definition
    ShadowedDefinition,
}

/// Unused computed value
///
/// Detects when a value is computed but never used or returned.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnusedValue {
    /// Function containing the unused value
    pub function: String,
    /// Description of the unused computation
    pub computation: String,
    /// Source location
    pub span: SourceSpan,
}

/// Missing await on future
///
/// Detects when an async function is called but the resulting
/// Future is not awaited.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MissingAwait {
    /// Function containing the missing await
    pub function: String,
    /// The async callee whose Future wasn't awaited
    pub async_callee: String,
    /// Source location
    pub span: SourceSpan,
}

/// Partial struct update
///
/// Detects when a struct is created or updated but some fields
/// are left uninitialized or with stale values. This commonly
/// occurs with struct update syntax (`..old_struct`) where
/// fields are unintentionally carried over.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PartialStructUpdate {
    /// Function containing the partial struct update
    pub function: String,
    /// Name of the struct type
    pub struct_type: String,
    /// Fields that were not explicitly initialized
    pub uninitialized_fields: Vec<String>,
    /// Fields that were explicitly set
    pub initialized_fields: Vec<String>,
    /// Why this is considered problematic
    pub reason: PartialUpdateReason,
    /// Source location
    pub span: SourceSpan,
}

/// Reason for partial struct update being flagged
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PartialUpdateReason {
    /// Using struct update syntax with potentially stale fields
    StructUpdateSyntax,
    /// Missing field initialization in constructor
    MissingFieldInit,
    /// Partial move of struct fields
    PartialMove,
    /// Only some fields mutated through &mut self
    PartialMutation,
}

// ============================================
// Async Chain Tracking (Phase 6.5.2)
// ============================================

/// Async chain violation detected in control flow analysis
///
/// Represents a violation in async function call chains, such as
/// chains that don't properly terminate with .await, or chains
/// that have unreachable async code.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AsyncChainViolation {
    /// The async chain that contains the violation
    pub chain: AsyncChain,
    /// Type of violation detected
    pub violation_type: AsyncChainViolationType,
    /// Description of the violation
    pub description: String,
    /// Source location where the violation occurs
    pub span: SourceSpan,
}

/// Type of async chain violation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AsyncChainViolationType {
    /// Async chain has no await point (Future created but never awaited)
    NoAwaitPoint,
    /// Async chain terminates without proper completion
    IncompleteChain,
    /// Async chain has unreachable code after await
    UnreachableAfterAwait,
    /// Async chain spawns task but doesn't join
    DanglingSpawn,
    /// Async chain has potential deadlock (cyclic await dependency)
    CyclicDependency,
    /// Async chain crosses sync boundary without proper handling
    SyncBoundaryCrossing,
    /// Indirect call to async function through closure or function pointer
    /// The Future returned may not be properly awaited
    IndirectAsyncCall,
    /// Closure passed to spawn function without JoinHandle tracking
    UnmonitoredSpawnClosure,
}

/// Represents a chain of async function calls
///
/// An async chain tracks the flow of futures through a program,
/// from creation to eventual .await or other termination.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AsyncChain {
    /// Unique identifier for this chain
    pub id: usize,
    /// Nodes in the chain (in call order)
    pub nodes: Vec<AsyncChainNode>,
    /// Whether this chain is properly terminated
    pub is_terminated: bool,
    /// How the chain terminates (if it does)
    pub termination: Option<AsyncTermination>,
}

/// A node in an async call chain
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AsyncChainNode {
    /// Name of the async function at this node
    pub function: String,
    /// Whether this is the chain origin (where the Future is created)
    pub is_origin: bool,
    /// Whether this node has an await point
    pub has_await: bool,
    /// Callees (async functions called from this node)
    pub callees: Vec<String>,
    /// Source location
    pub span: SourceSpan,
}

/// How an async chain terminates
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AsyncTermination {
    /// Chain ends with .await expression
    Awaited,
    /// Chain ends with block_on (sync entry to async)
    BlockOn,
    /// Future is spawned onto an executor
    Spawned,
    /// Future is stored (e.g., in a struct field)
    Stored,
    /// Future is returned from function
    Returned,
    /// Future is dropped (error case)
    Dropped,
}

impl AsyncChain {
    /// Create a new empty async chain
    #[must_use]
    pub const fn new(id: usize) -> Self {
        Self {
            id,
            nodes: Vec::new(),
            is_terminated: false,
            termination: None,
        }
    }

    /// Add a node to the chain
    pub fn add_node(&mut self, node: AsyncChainNode) {
        self.nodes.push(node);
    }

    /// Mark the chain as terminated
    pub const fn terminate(&mut self, termination: AsyncTermination) {
        self.is_terminated = true;
        self.termination = Some(termination);
    }

    /// Get the origin function of the chain
    #[must_use]
    pub fn origin(&self) -> Option<&str> {
        self.nodes
            .iter()
            .find(|n| n.is_origin)
            .map(|n| n.function.as_str())
    }

    /// Get all async functions in the chain
    #[must_use]
    pub fn functions(&self) -> Vec<&str> {
        self.nodes.iter().map(|n| n.function.as_str()).collect()
    }

    /// Check if any node in the chain has an await point
    #[must_use]
    pub fn has_any_await(&self) -> bool {
        self.nodes.iter().any(|n| n.has_await)
    }

    /// Get the length of the chain
    #[must_use]
    pub const fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Check if the chain is empty
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }
}

impl AsyncChainNode {
    /// Create a new async chain node
    #[must_use]
    pub fn new(function: &str, is_origin: bool, span: SourceSpan) -> Self {
        Self {
            function: function.to_string(),
            is_origin,
            has_await: false,
            callees: Vec::new(),
            span,
        }
    }

    /// Mark this node as having an await point
    #[must_use]
    pub const fn with_await(mut self) -> Self {
        self.has_await = true;
        self
    }

    /// Add callees to this node
    #[must_use]
    pub fn with_callees(mut self, callees: Vec<String>) -> Self {
        self.callees = callees;
        self
    }
}

impl AsyncChainViolation {
    /// Create a new async chain violation
    #[must_use]
    pub fn new(
        chain: AsyncChain,
        violation_type: AsyncChainViolationType,
        description: &str,
        span: SourceSpan,
    ) -> Self {
        Self {
            chain,
            violation_type,
            description: description.to_string(),
            span,
        }
    }

    /// Get the origin function of the violating chain
    #[must_use]
    pub fn origin_function(&self) -> Option<&str> {
        self.chain.origin()
    }
}

impl PathAnomaly {
    /// Get the span for this anomaly
    #[must_use]
    pub const fn span(&self) -> &SourceSpan {
        match self {
            Self::UnhandledResult(u) => &u.span,
            Self::DeadCode(d) => &d.span,
            Self::UnusedValue(u) => &u.span,
            Self::MissingAwait(m) => &m.span,
            Self::PartialStructUpdate(p) => &p.span,
            Self::AsyncChainViolation(a) => &a.span,
        }
    }

    /// Get a human-readable description
    #[must_use]
    pub fn description(&self) -> String {
        match self {
            Self::UnhandledResult(u) => {
                format!("unhandled Result from call to `{}`", u.callee)
            }
            Self::DeadCode(d) => {
                format!("dead code: function `{}` is never called", d.function)
            }
            Self::UnusedValue(u) => {
                format!("unused value: {} in `{}`", u.computation, u.function)
            }
            Self::MissingAwait(m) => {
                format!("missing await on Future from `{}`", m.async_callee)
            }
            Self::PartialStructUpdate(p) => {
                let fields = p.uninitialized_fields.join(", ");
                format!(
                    "partial struct update of `{}`: fields not explicitly set: {}",
                    p.struct_type, fields
                )
            }
            Self::AsyncChainViolation(a) => {
                let origin = a.chain.origin().unwrap_or("unknown");
                format!("async chain violation in `{}`: {}", origin, a.description)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    // ============================================
    // FunctionSpec tests
    // ============================================

    #[test]
    fn test_function_spec_default() {
        let spec = FunctionSpec::default();

        assert!(spec.requires.is_empty());
        assert!(spec.ensures.is_empty());
        assert!(spec.decreases.is_none());
        assert!(spec.temporal.is_empty());
        assert!(!spec.pure);
        assert!(!spec.may_diverge);
        assert!(!spec.trusted);
    }

    #[test]
    fn test_function_spec_with_requires() {
        let mut spec = FunctionSpec::default();
        spec.requires.push(SpecClause {
            pred: Predicate::expr(Expr::var("x").gt(Expr::int(0))),
            span: SourceSpan::default(),
            label: Some("x must be positive".to_string()),
        });

        assert_eq!(spec.requires.len(), 1);
        assert_eq!(
            spec.requires[0].label,
            Some("x must be positive".to_string())
        );
    }

    #[test]
    fn test_function_spec_with_ensures() {
        let mut spec = FunctionSpec::default();
        spec.ensures.push(SpecClause {
            pred: Predicate::expr(Expr::Result.ge(Expr::int(0))),
            span: SourceSpan::default(),
            label: None,
        });

        assert_eq!(spec.ensures.len(), 1);
    }

    #[test]
    fn test_function_spec_annotations() {
        let spec = FunctionSpec {
            pure: true,
            may_diverge: true,
            trusted: true,
            ..Default::default()
        };

        assert!(spec.pure);
        assert!(spec.may_diverge);
        assert!(spec.trusted);
    }

    #[test]
    fn test_function_spec_with_decreases() {
        let spec = FunctionSpec {
            decreases: Some(DecreasesClause {
                measure: Expr::var("n"),
                relation: Some(WellFoundedRelation::Nat),
                span: SourceSpan::default(),
            }),
            ..Default::default()
        };

        assert!(spec.decreases.is_some());
        let dec = spec.decreases.as_ref().unwrap();
        assert!(matches!(dec.relation, Some(WellFoundedRelation::Nat)));
    }

    #[test]
    fn test_function_spec_serialization() {
        let mut spec = FunctionSpec {
            pure: true,
            ..Default::default()
        };
        spec.requires.push(SpecClause {
            pred: Predicate::t(),
            span: SourceSpan::default(),
            label: None,
        });

        let json = serde_json::to_string(&spec).expect("serialize");
        let parsed: FunctionSpec = serde_json::from_str(&json).expect("deserialize");

        assert!(parsed.pure);
        assert_eq!(parsed.requires.len(), 1);
    }

    // ============================================
    // TypeSpec tests
    // ============================================

    #[test]
    fn test_type_spec_default() {
        let spec = TypeSpec::default();
        assert!(spec.invariants.is_empty());
        assert!(spec.rep_invariants.is_empty());
    }

    #[test]
    fn test_type_spec_with_invariants() {
        let mut spec = TypeSpec::default();
        spec.invariants.push(SpecClause {
            pred: Predicate::expr(
                Expr::StructField(Box::new(Expr::var("self")), "balance".to_string())
                    .ge(Expr::int(0)),
            ),
            span: SourceSpan::default(),
            label: Some("balance >= 0".to_string()),
        });

        assert_eq!(spec.invariants.len(), 1);
    }

    #[test]
    fn test_type_spec_with_rep_invariant() {
        let mut spec = TypeSpec::default();
        spec.rep_invariants.push(SpecClause {
            pred: Predicate::t(), // placeholder
            span: SourceSpan::default(),
            label: Some("unsafe representation valid".to_string()),
        });

        assert_eq!(spec.rep_invariants.len(), 1);
    }

    // ============================================
    // TraitSpec tests
    // ============================================

    #[test]
    fn test_trait_spec_default() {
        let spec = TraitSpec::default();
        assert!(spec.invariants.is_empty());
        assert!(spec.methods.is_empty());
    }

    #[test]
    fn test_trait_spec_with_method() {
        let mut spec = TraitSpec::default();

        let mut method_spec = FunctionSpec::default();
        method_spec.requires.push(SpecClause {
            pred: Predicate::t(),
            span: SourceSpan::default(),
            label: None,
        });

        spec.methods.push(("process".to_string(), method_spec));

        assert_eq!(spec.methods.len(), 1);
        assert_eq!(spec.methods[0].0, "process");
    }

    // ============================================
    // LoopSpec tests
    // ============================================

    #[test]
    fn test_loop_spec() {
        let loop_spec = LoopSpec {
            invariants: vec![SpecClause {
                pred: Predicate::expr(Expr::var("i").lt(Expr::var("n"))),
                span: SourceSpan::default(),
                label: Some("i < n".to_string()),
            }],
            variant: Some(DecreasesClause {
                measure: Expr::var("n").sub(Expr::var("i")),
                relation: Some(WellFoundedRelation::Nat),
                span: SourceSpan::default(),
            }),
        };

        assert_eq!(loop_spec.invariants.len(), 1);
        assert!(loop_spec.variant.is_some());
    }

    #[test]
    fn test_loop_spec_serialization() {
        let loop_spec = LoopSpec {
            invariants: vec![],
            variant: None,
        };

        let json = serde_json::to_string(&loop_spec).expect("serialize");
        let parsed: LoopSpec = serde_json::from_str(&json).expect("deserialize");

        assert!(parsed.invariants.is_empty());
        assert!(parsed.variant.is_none());
    }

    // ============================================
    // DecreasesClause tests
    // ============================================

    #[test]
    fn test_decreases_clause_nat() {
        let dec = DecreasesClause {
            measure: Expr::var("n"),
            relation: Some(WellFoundedRelation::Nat),
            span: SourceSpan::default(),
        };

        assert!(matches!(dec.relation, Some(WellFoundedRelation::Nat)));
    }

    #[test]
    fn test_decreases_clause_lex() {
        let dec = DecreasesClause {
            measure: Expr::Apply {
                func: "tuple".to_string(),
                args: vec![Expr::var("a"), Expr::var("b")],
            },
            relation: Some(WellFoundedRelation::Lex),
            span: SourceSpan::default(),
        };

        assert!(matches!(dec.relation, Some(WellFoundedRelation::Lex)));
    }

    #[test]
    fn test_decreases_clause_custom() {
        let dec = DecreasesClause {
            measure: Expr::var("x"),
            relation: Some(WellFoundedRelation::Custom("my_order".to_string())),
            span: SourceSpan::default(),
        };

        match dec.relation {
            Some(WellFoundedRelation::Custom(name)) => {
                assert_eq!(name, "my_order");
            }
            _ => panic!("Expected Custom relation"),
        }
    }

    // ============================================
    // GhostBlock and GhostStmt tests
    // ============================================

    #[test]
    fn test_ghost_block() {
        let ghost = GhostBlock {
            stmts: vec![
                GhostStmt::Let {
                    name: "ghost_val".to_string(),
                    value: Expr::int(42),
                },
                GhostStmt::Assert(Predicate::expr(Expr::var("ghost_val").eq(Expr::int(42)))),
            ],
            span: SourceSpan::default(),
        };

        assert_eq!(ghost.stmts.len(), 2);
    }

    #[test]
    fn test_ghost_stmt_let() {
        let stmt = GhostStmt::Let {
            name: "x".to_string(),
            value: Expr::int(10),
        };

        match stmt {
            GhostStmt::Let { name, .. } => assert_eq!(name, "x"),
            _ => panic!("Expected Let"),
        }
    }

    #[test]
    fn test_ghost_stmt_assert() {
        let stmt = GhostStmt::Assert(Predicate::t());
        assert!(matches!(stmt, GhostStmt::Assert(_)));
    }

    #[test]
    fn test_ghost_stmt_assume() {
        let stmt = GhostStmt::Assume(Predicate::t());
        assert!(matches!(stmt, GhostStmt::Assume(_)));
    }

    #[test]
    fn test_ghost_stmt_unfold() {
        let stmt = GhostStmt::Unfold {
            pred: "is_list".to_string(),
            args: vec![Expr::var("head")],
        };

        match stmt {
            GhostStmt::Unfold { pred, args } => {
                assert_eq!(pred, "is_list");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("Expected Unfold"),
        }
    }

    #[test]
    fn test_ghost_stmt_fold() {
        let stmt = GhostStmt::Fold {
            pred: "is_tree".to_string(),
            args: vec![Expr::var("root")],
        };

        assert!(matches!(stmt, GhostStmt::Fold { .. }));
    }

    #[test]
    fn test_ghost_stmt_lemma() {
        let stmt = GhostStmt::Lemma {
            name: "list_length_positive".to_string(),
            args: vec![Expr::var("list")],
        };

        match stmt {
            GhostStmt::Lemma { name, args } => {
                assert_eq!(name, "list_length_positive");
                assert_eq!(args.len(), 1);
            }
            _ => panic!("Expected Lemma"),
        }
    }

    // ============================================
    // LemmaDefinition tests (Phase 8.2)
    // ============================================

    #[test]
    fn test_lemma_definition_new() {
        let lemma = LemmaDefinition::new("sum_formula", SourceSpan::default());
        assert_eq!(lemma.name, "sum_formula");
        assert!(lemma.params.is_empty());
        assert!(lemma.requires.is_empty());
        assert!(lemma.ensures.is_empty());
        assert!(!lemma.is_builtin);
    }

    #[test]
    fn test_lemma_definition_builtin() {
        let lemma = LemmaDefinition::builtin("add_commutative");
        assert_eq!(lemma.name, "add_commutative");
        assert!(lemma.is_builtin);
    }

    #[test]
    fn test_lemma_definition_with_params() {
        let lemma = LemmaDefinition::new("pos_sum", SourceSpan::default())
            .with_param("a", "i32")
            .with_param("b", "i32");

        assert_eq!(lemma.params.len(), 2);
        assert_eq!(lemma.params[0].name, "a");
        assert_eq!(lemma.params[0].ty, "i32");
        assert_eq!(lemma.params[1].name, "b");
        assert_eq!(lemma.params[1].ty, "i32");
    }

    #[test]
    fn test_lemma_definition_with_requires() {
        let lemma =
            LemmaDefinition::new("pos_lemma", SourceSpan::default()).with_requires("(>= a 0)");

        assert_eq!(lemma.requires.len(), 1);
        assert_eq!(lemma.requires[0], "(>= a 0)");
    }

    #[test]
    fn test_lemma_definition_with_ensures() {
        let lemma = LemmaDefinition::new("result_lemma", SourceSpan::default())
            .with_ensures("(>= result 0)");

        assert_eq!(lemma.ensures.len(), 1);
        assert_eq!(lemma.ensures[0], "(>= result 0)");
    }

    #[test]
    fn test_lemma_to_smt_no_params() {
        let lemma = LemmaDefinition::new("simple", SourceSpan::default())
            .with_requires("(> x 0)")
            .with_ensures("(> (* x x) 0)");

        let smt = lemma.to_smt_assertion();
        assert_eq!(smt, "(assert (=> (> x 0) (> (* x x) 0)))");
    }

    #[test]
    fn test_lemma_to_smt_with_params() {
        let lemma = LemmaDefinition::new("add_assoc", SourceSpan::default())
            .with_param("a", "i32")
            .with_param("b", "i32")
            .with_param("c", "i32")
            .with_ensures("(= (+ (+ a b) c) (+ a (+ b c)))");

        let smt = lemma.to_smt_assertion();
        assert!(smt.contains("forall"));
        assert!(smt.contains("(a Int)"));
        assert!(smt.contains("(b Int)"));
        assert!(smt.contains("(c Int)"));
        assert!(smt.contains("(+ (+ a b) c)"));
    }

    #[test]
    fn test_lemma_to_smt_multiple_requires() {
        let lemma = LemmaDefinition::new("bounded", SourceSpan::default())
            .with_requires("(>= x 0)")
            .with_requires("(<= x 100)")
            .with_ensures("(<= (* x x) 10000)");

        let smt = lemma.to_smt_assertion();
        assert!(smt.contains("(and (>= x 0) (<= x 100))"));
    }

    #[test]
    fn test_lemma_to_smt_multiple_ensures() {
        let lemma = LemmaDefinition::new("multi_ensures", SourceSpan::default())
            .with_requires("(> x 0)")
            .with_ensures("(> (+ x 1) 0)")
            .with_ensures("(> (* x 2) 0)");

        let smt = lemma.to_smt_assertion();
        assert!(smt.contains("(and (> (+ x 1) 0) (> (* x 2) 0))"));
    }

    #[test]
    fn test_lemma_request_new() {
        let request = LemmaRequest::new("(>= sum 0)", SourceSpan::default());
        assert_eq!(request.goal, "(>= sum 0)");
        assert!(request.variables.is_empty());
        assert!(request.suggested_patterns.is_empty());
    }

    #[test]
    fn test_lemma_request_with_variables() {
        let request = LemmaRequest::new("goal", SourceSpan::default())
            .with_variable("n", "i32")
            .with_variable("sum", "i32");

        assert_eq!(request.variables.len(), 2);
        assert_eq!(request.variables[0], ("n".to_string(), "i32".to_string()));
    }

    #[test]
    fn test_lemma_suggestion_new() {
        let suggestion = LemmaSuggestion::new(
            "Arithmetic induction",
            "#[lemma]\n#[requires(\"n >= 0\")]\n#[ensures(\"sum(n) >= 0\")]\nfn sum_nonneg(n: i32) {}",
            0.85
        );

        assert_eq!(suggestion.description, "Arithmetic induction");
        assert!(suggestion.skeleton.contains("#[lemma]"));
        assert!((suggestion.confidence - 0.85).abs() < 0.001);
    }

    #[test]
    fn test_lemma_suggestion_confidence_clamped() {
        let suggestion = LemmaSuggestion::new("test", "test", 1.5);
        assert!((suggestion.confidence - 1.0).abs() < 0.001);

        let suggestion2 = LemmaSuggestion::new("test", "test", -0.5);
        assert!((suggestion2.confidence - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_lemma_request_with_suggestion() {
        let suggestion = LemmaSuggestion::new("hint", "skeleton", 0.5);
        let request = LemmaRequest::new("goal", SourceSpan::default()).with_suggestion(suggestion);

        assert_eq!(request.suggested_patterns.len(), 1);
        assert_eq!(request.suggested_patterns[0].description, "hint");
    }

    // ============================================
    // Builtin Lemma Library Tests (Phase 8.2)
    // ============================================

    #[test]
    fn test_builtin_arithmetic_lemmas() {
        let lemmas = builtin_lemmas::arithmetic_lemmas();
        assert!(!lemmas.is_empty());

        // Check add_commutative exists
        let add_comm = lemmas.iter().find(|l| l.name == "add_commutative");
        assert!(add_comm.is_some());
        let add_comm = add_comm.unwrap();
        assert_eq!(add_comm.params.len(), 2);
        assert!(add_comm.is_builtin);

        // Check distributive exists
        let distr = lemmas.iter().find(|l| l.name == "distributive");
        assert!(distr.is_some());
    }

    #[test]
    fn test_builtin_sign_lemmas() {
        let lemmas = builtin_lemmas::sign_lemmas();
        assert!(!lemmas.is_empty());

        // Check mul_nonneg exists with proper preconditions
        let mul_nonneg = lemmas.iter().find(|l| l.name == "mul_nonneg");
        assert!(mul_nonneg.is_some());
        let mul_nonneg = mul_nonneg.unwrap();
        assert_eq!(mul_nonneg.requires.len(), 2);
        assert_eq!(mul_nonneg.ensures.len(), 1);
    }

    #[test]
    fn test_builtin_ordering_lemmas() {
        let lemmas = builtin_lemmas::ordering_lemmas();
        assert!(!lemmas.is_empty());

        // Check le_transitive exists
        let trans = lemmas.iter().find(|l| l.name == "le_transitive");
        assert!(trans.is_some());
        let trans = trans.unwrap();
        assert_eq!(trans.params.len(), 3);
    }

    #[test]
    fn test_builtin_division_lemmas() {
        let lemmas = builtin_lemmas::division_lemmas();
        assert!(!lemmas.is_empty());

        // Check div_mod_identity has division-by-zero precondition
        let div_mod = lemmas.iter().find(|l| l.name == "div_mod_identity");
        assert!(div_mod.is_some());
        let div_mod = div_mod.unwrap();
        assert!(!div_mod.requires.is_empty());
    }

    #[test]
    fn test_builtin_bounds_lemmas() {
        let lemmas = builtin_lemmas::bounds_lemmas();
        assert!(!lemmas.is_empty());

        // Check last_index lemma
        let last = lemmas.iter().find(|l| l.name == "last_index");
        assert!(last.is_some());
    }

    #[test]
    fn test_builtin_all_lemmas() {
        let all = builtin_lemmas::all_lemmas();

        // Should have at least 20 lemmas across all categories
        assert!(all.len() >= 20);

        // All should be builtin
        assert!(all.iter().all(|l| l.is_builtin));
    }

    #[test]
    fn test_builtin_find_lemma() {
        // Find existing lemma
        let found = builtin_lemmas::find_lemma("add_commutative");
        assert!(found.is_some());
        assert_eq!(found.unwrap().name, "add_commutative");

        // Non-existing lemma returns None
        let not_found = builtin_lemmas::find_lemma("nonexistent_lemma");
        assert!(not_found.is_none());
    }

    #[test]
    fn test_builtin_lemma_smt_generation() {
        let lemma = builtin_lemmas::find_lemma("add_commutative").unwrap();
        let smt = lemma.to_smt_assertion();

        // Should be a quantified assertion
        assert!(smt.contains("assert"));
        assert!(smt.contains("forall"));
        assert!(smt.contains("(a Int)"));
        assert!(smt.contains("(b Int)"));
    }

    // ============================================
    // RefinementType tests
    // ============================================

    #[test]
    fn test_refinement_type() {
        let reftype = RefinementType {
            base: "i32".to_string(),
            refinement: Predicate::expr(Expr::var("self").gt(Expr::int(0))),
            span: SourceSpan::default(),
        };

        assert_eq!(reftype.base, "i32");
    }

    #[test]
    fn test_refinement_type_serialization() {
        let reftype = RefinementType {
            base: "u64".to_string(),
            refinement: Predicate::t(),
            span: SourceSpan::default(),
        };

        let json = serde_json::to_string(&reftype).expect("serialize");
        let parsed: RefinementType = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(parsed.base, "u64");
    }

    // ============================================
    // TemporalClause tests
    // ============================================

    #[test]
    fn test_temporal_clause() {
        let clause = TemporalClause {
            formula: TemporalFormula::Eventually(Box::new(TemporalFormula::State(Predicate::t()))),
            span: SourceSpan::default(),
        };

        assert!(matches!(clause.formula, TemporalFormula::Eventually(_)));
    }

    // ============================================
    // Effect tests
    // ============================================

    #[test]
    fn test_effect_parse() {
        assert_eq!(Effect::parse("io"), Some(Effect::IO));
        assert_eq!(Effect::parse("IO"), Some(Effect::IO));
        assert_eq!(Effect::parse("alloc"), Some(Effect::Alloc));
        assert_eq!(Effect::parse("Alloc"), Some(Effect::Alloc));
        assert_eq!(Effect::parse("panic"), Some(Effect::Panic));
        assert_eq!(Effect::parse("diverge"), Some(Effect::Diverge));
        assert_eq!(Effect::parse("unsafe"), Some(Effect::Unsafe));
        assert_eq!(Effect::parse("globalstate"), Some(Effect::GlobalState));
        assert_eq!(Effect::parse("global_state"), Some(Effect::GlobalState));
        assert_eq!(Effect::parse("unknown"), None);
    }

    #[test]
    fn test_effect_as_str() {
        assert_eq!(Effect::IO.as_str(), "IO");
        assert_eq!(Effect::Alloc.as_str(), "Alloc");
        assert_eq!(Effect::Panic.as_str(), "Panic");
        assert_eq!(Effect::Diverge.as_str(), "Diverge");
        assert_eq!(Effect::Unsafe.as_str(), "Unsafe");
        assert_eq!(Effect::GlobalState.as_str(), "GlobalState");
    }

    #[test]
    fn test_effect_all() {
        let all = Effect::all();
        assert_eq!(all.len(), 6);
        assert!(all.contains(&Effect::IO));
        assert!(all.contains(&Effect::Alloc));
        assert!(all.contains(&Effect::Panic));
        assert!(all.contains(&Effect::Diverge));
        assert!(all.contains(&Effect::Unsafe));
        assert!(all.contains(&Effect::GlobalState));
    }

    #[test]
    fn test_effect_equality_and_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(Effect::IO);
        set.insert(Effect::Alloc);
        set.insert(Effect::IO); // duplicate
        assert_eq!(set.len(), 2);
    }

    // ============================================
    // EffectSet tests
    // ============================================

    #[test]
    fn test_effect_set_empty() {
        let set = EffectSet::empty();
        assert!(set.is_pure());
        assert!(!set.has(Effect::IO));
    }

    #[test]
    fn test_effect_set_from_effects() {
        let set = EffectSet::from_effects([Effect::IO, Effect::Alloc]);
        assert!(!set.is_pure());
        assert!(set.has(Effect::IO));
        assert!(set.has(Effect::Alloc));
        assert!(!set.has(Effect::Panic));
    }

    #[test]
    fn test_effect_set_add() {
        let mut set = EffectSet::empty();
        assert!(set.is_pure());
        set.add(Effect::Panic);
        assert!(!set.is_pure());
        assert!(set.has(Effect::Panic));
    }

    #[test]
    fn test_effect_set_subset() {
        let pure = EffectSet::empty();
        let io_only = EffectSet::from_effects([Effect::IO]);
        let io_alloc = EffectSet::from_effects([Effect::IO, Effect::Alloc]);

        // Pure is subset of everything
        assert!(pure.is_subset_of(&pure));
        assert!(pure.is_subset_of(&io_only));
        assert!(pure.is_subset_of(&io_alloc));

        // io_only is subset of io_alloc
        assert!(io_only.is_subset_of(&io_alloc));
        assert!(!io_alloc.is_subset_of(&io_only));

        // io_only is not subset of pure
        assert!(!io_only.is_subset_of(&pure));
    }

    #[test]
    fn test_effect_set_union() {
        let io = EffectSet::from_effects([Effect::IO]);
        let alloc = EffectSet::from_effects([Effect::Alloc]);
        let union = io.union(&alloc);

        assert!(union.has(Effect::IO));
        assert!(union.has(Effect::Alloc));
        assert!(!union.has(Effect::Panic));
    }

    #[test]
    fn test_effect_set_difference() {
        let io_alloc = EffectSet::from_effects([Effect::IO, Effect::Alloc]);
        let io = EffectSet::from_effects([Effect::IO]);
        let diff = io_alloc.difference(&io);

        assert!(!diff.has(Effect::IO));
        assert!(diff.has(Effect::Alloc));
    }

    #[test]
    fn test_effect_set_parse() {
        let set = EffectSet::parse("IO, Alloc, Panic");
        assert!(set.has(Effect::IO));
        assert!(set.has(Effect::Alloc));
        assert!(set.has(Effect::Panic));
        assert!(!set.has(Effect::Diverge));
    }

    #[test]
    fn test_effect_set_serialization() {
        let set = EffectSet::from_effects([Effect::IO, Effect::Panic]);
        let json = serde_json::to_string(&set).expect("serialize");
        let parsed: EffectSet = serde_json::from_str(&json).expect("deserialize");

        assert!(parsed.has(Effect::IO));
        assert!(parsed.has(Effect::Panic));
        assert!(!parsed.has(Effect::Alloc));
    }

    // ============================================
    // FunctionSpec effects tests
    // ============================================

    #[test]
    fn test_function_spec_effective_effects_pure() {
        let spec = FunctionSpec {
            pure: true,
            ..Default::default()
        };

        let effects = spec.effective_effects().unwrap();
        assert!(effects.is_pure());
    }

    #[test]
    fn test_function_spec_effective_effects_declared() {
        let spec = FunctionSpec {
            effects: Some(EffectSet::from_effects([Effect::IO])),
            ..Default::default()
        };

        let effects = spec.effective_effects().unwrap();
        assert!(effects.has(Effect::IO));
        assert!(!effects.is_pure());
    }

    #[test]
    fn test_function_spec_effective_effects_none() {
        let spec = FunctionSpec::default();
        assert!(spec.effective_effects().is_none());
    }

    #[test]
    fn test_function_spec_pure_overrides_effects() {
        // If both pure=true and effects are set, pure takes precedence
        let spec = FunctionSpec {
            pure: true,
            effects: Some(EffectSet::from_effects([Effect::IO])),
            ..Default::default()
        };

        let effects = spec.effective_effects().unwrap();
        assert!(effects.is_pure()); // Pure wins
    }

    #[test]
    fn test_function_spec_has_declared_effects() {
        let spec_default = FunctionSpec::default();
        assert!(!spec_default.has_declared_effects());

        let spec_pure = FunctionSpec {
            pure: true,
            ..Default::default()
        };
        assert!(spec_pure.has_declared_effects());

        let spec_effects = FunctionSpec {
            effects: Some(EffectSet::from_effects([Effect::Alloc])),
            ..Default::default()
        };
        assert!(spec_effects.has_declared_effects());
    }

    // ============================================
    // Effect variable tests
    // ============================================

    #[test]
    fn test_effect_var_creation() {
        let var = EffectVar::new("E");
        assert_eq!(var.name(), "E");
        assert_eq!(var.0, "E");
    }

    #[test]
    fn test_effect_var_equality() {
        let var1 = EffectVar::new("E");
        let var2 = EffectVar::new("E");
        let var3 = EffectVar::new("F");
        assert_eq!(var1, var2);
        assert_ne!(var1, var3);
    }

    #[test]
    fn test_effect_var_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(EffectVar::new("E"));
        set.insert(EffectVar::new("E")); // duplicate
        set.insert(EffectVar::new("F"));
        assert_eq!(set.len(), 2);
    }

    // ============================================
    // EffectSource tests
    // ============================================

    #[test]
    fn test_effect_source_concrete() {
        let source = EffectSource::concrete([Effect::IO, Effect::Alloc]);
        assert!(source.is_concrete());
        assert!(!source.is_pure());

        let effect_set = source.to_effect_set().unwrap();
        assert!(effect_set.has(Effect::IO));
        assert!(effect_set.has(Effect::Alloc));
    }

    #[test]
    fn test_effect_source_pure() {
        let source = EffectSource::concrete([]);
        assert!(source.is_concrete());
        assert!(source.is_pure());

        let effect_set = source.to_effect_set().unwrap();
        assert!(effect_set.is_pure());
    }

    #[test]
    fn test_effect_source_variable() {
        let source = EffectSource::var("E");
        assert!(!source.is_concrete());
        assert!(!source.is_pure());
        assert!(source.to_effect_set().is_none()); // Can't resolve without substitution

        let vars = source.effect_vars();
        assert_eq!(vars.len(), 1);
        assert_eq!(vars[0].name(), "E");
    }

    #[test]
    fn test_effect_source_param() {
        let source = EffectSource::param("callback");
        assert!(!source.is_concrete());
        assert!(!source.is_pure());
        assert!(source.to_effect_set().is_none());

        let params = source.param_refs();
        assert_eq!(params.len(), 1);
        assert_eq!(params[0], "callback");
    }

    #[test]
    fn test_effect_source_union() {
        let source = EffectSource::union(vec![
            EffectSource::concrete([Effect::IO]),
            EffectSource::concrete([Effect::Alloc]),
        ]);

        assert!(source.is_concrete());
        let effect_set = source.to_effect_set().unwrap();
        assert!(effect_set.has(Effect::IO));
        assert!(effect_set.has(Effect::Alloc));
    }

    #[test]
    fn test_effect_source_union_with_param() {
        let source = EffectSource::union(vec![
            EffectSource::concrete([Effect::IO]),
            EffectSource::param("f"),
        ]);

        assert!(!source.is_concrete()); // Has parameter reference
        assert!(source.to_effect_set().is_none()); // Can't fully resolve

        let params = source.param_refs();
        assert_eq!(params.len(), 1);
        assert_eq!(params[0], "f");
    }

    #[test]
    fn test_effect_source_union_flattening() {
        let inner_union = EffectSource::union(vec![
            EffectSource::concrete([Effect::IO]),
            EffectSource::concrete([Effect::Alloc]),
        ]);
        let outer_union =
            EffectSource::union(vec![inner_union, EffectSource::concrete([Effect::Panic])]);

        // Union should be flattened
        match outer_union {
            EffectSource::Union(sources) => {
                assert_eq!(sources.len(), 3); // Flattened from nested
            }
            _ => panic!("Expected flattened Union"),
        }
    }

    #[test]
    fn test_effect_source_single_union_simplification() {
        let source = EffectSource::union(vec![EffectSource::concrete([Effect::IO])]);

        // Single-element union should be simplified to the element
        match source {
            EffectSource::Concrete(effects) => {
                assert_eq!(effects.len(), 1);
                assert_eq!(effects[0], Effect::IO);
            }
            _ => panic!("Expected simplified Concrete"),
        }
    }

    // ============================================
    // FunctionSpec effect polymorphism tests
    // ============================================

    #[test]
    fn test_function_spec_effect_source_pure() {
        let spec = FunctionSpec {
            pure: true,
            ..Default::default()
        };

        let source = spec.effect_source().unwrap();
        assert!(source.is_pure());
        assert!(!spec.has_polymorphic_effects());
    }

    #[test]
    fn test_function_spec_effect_source_concrete() {
        let spec = FunctionSpec {
            effects: Some(EffectSet::from_effects([Effect::IO])),
            ..Default::default()
        };

        let source = spec.effect_source().unwrap();
        assert!(source.is_concrete());
        assert!(!spec.has_polymorphic_effects());
    }

    #[test]
    fn test_function_spec_effect_source_polymorphic() {
        let spec = FunctionSpec {
            effect_source: Some(EffectSource::param("callback")),
            ..Default::default()
        };

        let source = spec.effect_source().unwrap();
        assert!(!source.is_concrete());
        assert!(spec.has_polymorphic_effects());
        assert!(spec.has_declared_effects());
    }

    #[test]
    fn test_function_spec_effect_source_union_with_concrete_and_param() {
        // #[effects(IO, effects_of(f))]
        let spec = FunctionSpec {
            effect_source: Some(EffectSource::union(vec![
                EffectSource::concrete([Effect::IO]),
                EffectSource::param("f"),
            ])),
            ..Default::default()
        };

        assert!(spec.has_polymorphic_effects());

        let source = spec.effect_source().unwrap();
        let params = source.param_refs();
        assert_eq!(params.len(), 1);
        assert_eq!(params[0], "f");
    }

    #[test]
    fn test_effect_source_serialization() {
        let source = EffectSource::union(vec![
            EffectSource::concrete([Effect::IO]),
            EffectSource::param("f"),
        ]);

        let json = serde_json::to_string(&source).expect("serialize");
        let parsed: EffectSource = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(source, parsed);
    }

    #[test]
    fn test_effect_var_serialization() {
        let var = EffectVar::new("E");
        let json = serde_json::to_string(&var).expect("serialize");
        let parsed: EffectVar = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(var, parsed);
    }

    // ============================================
    // Effect substitution tests
    // ============================================

    #[test]
    fn test_effect_source_substitute_concrete() {
        use std::collections::HashMap;
        let source = EffectSource::concrete([Effect::IO, Effect::Alloc]);
        let params: HashMap<String, EffectSet> = HashMap::new();

        let result = source.substitute(&params).unwrap();
        assert!(result.has(Effect::IO));
        assert!(result.has(Effect::Alloc));
    }

    #[test]
    fn test_effect_source_substitute_param() {
        use std::collections::HashMap;
        let source = EffectSource::param("callback");
        let mut params = HashMap::new();
        params.insert(
            "callback".to_string(),
            EffectSet::from_effects([Effect::IO]),
        );

        let result = source.substitute(&params).unwrap();
        assert!(result.has(Effect::IO));
        assert!(!result.has(Effect::Alloc));
    }

    #[test]
    fn test_effect_source_substitute_param_missing() {
        use std::collections::HashMap;
        let source = EffectSource::param("callback");
        let params: HashMap<String, EffectSet> = HashMap::new();

        // Missing parameter should return None
        assert!(source.substitute(&params).is_none());
    }

    #[test]
    fn test_effect_source_substitute_union() {
        use std::collections::HashMap;
        let source = EffectSource::union(vec![
            EffectSource::concrete([Effect::Alloc]),
            EffectSource::param("f"),
        ]);
        let mut params = HashMap::new();
        params.insert("f".to_string(), EffectSet::from_effects([Effect::IO]));

        let result = source.substitute(&params).unwrap();
        assert!(result.has(Effect::IO));
        assert!(result.has(Effect::Alloc));
    }

    #[test]
    fn test_effect_source_substitute_with_fallback_missing() {
        use std::collections::HashMap;
        let source = EffectSource::param("unknown");
        let params: HashMap<String, EffectSet> = HashMap::new();
        let fallback = EffectSet::from_effects([Effect::IO, Effect::Panic]);

        let result = source.substitute_with_fallback(&params, &fallback);
        assert!(result.has(Effect::IO));
        assert!(result.has(Effect::Panic));
    }

    #[test]
    fn test_effect_source_substitute_with_fallback_found() {
        use std::collections::HashMap;
        let source = EffectSource::param("callback");
        let mut params = HashMap::new();
        params.insert(
            "callback".to_string(),
            EffectSet::from_effects([Effect::Alloc]),
        );
        let fallback = EffectSet::from_effects([Effect::IO, Effect::Panic]);

        let result = source.substitute_with_fallback(&params, &fallback);
        assert!(result.has(Effect::Alloc));
        assert!(!result.has(Effect::IO)); // Should use param value, not fallback
    }

    #[test]
    fn test_effect_source_substitute_variable_returns_none() {
        use std::collections::HashMap;
        let source = EffectSource::var("E");
        let params: HashMap<String, EffectSet> = HashMap::new();

        // Effect variables can't be substituted with param_effects
        assert!(source.substitute(&params).is_none());
    }

    #[test]
    fn test_effect_source_substitute_variable_uses_fallback() {
        use std::collections::HashMap;
        let source = EffectSource::var("E");
        let params: HashMap<String, EffectSet> = HashMap::new();
        let fallback = EffectSet::from_effects([Effect::Diverge]);

        let result = source.substitute_with_fallback(&params, &fallback);
        assert!(result.has(Effect::Diverge));
    }

    // ============================================
    // WireAnnotation tests (Phase 6.5)
    // ============================================

    #[test]
    fn test_wire_annotation_start() {
        let ann = WireAnnotation::Start;
        assert!(matches!(ann, WireAnnotation::Start));
    }

    #[test]
    fn test_wire_annotation_state() {
        let ann = WireAnnotation::State("checkout".to_string());
        if let WireAnnotation::State(name) = ann {
            assert_eq!(name, "checkout");
        } else {
            panic!("Expected State");
        }
    }

    #[test]
    fn test_wire_annotation_must_reach() {
        let ann = WireAnnotation::MustReach(vec!["success".to_string(), "error".to_string()]);
        if let WireAnnotation::MustReach(states) = ann {
            assert_eq!(states.len(), 2);
            assert_eq!(states[0], "success");
            assert_eq!(states[1], "error");
        } else {
            panic!("Expected MustReach");
        }
    }

    #[test]
    fn test_wire_annotation_data_flow() {
        let ann = WireAnnotation::DataFlow {
            input: "cart".to_string(),
            output: "receipt".to_string(),
        };
        if let WireAnnotation::DataFlow { input, output } = ann {
            assert_eq!(input, "cart");
            assert_eq!(output, "receipt");
        } else {
            panic!("Expected DataFlow");
        }
    }

    #[test]
    fn test_wire_spec_default() {
        let spec = WireSpec::default();
        assert!(spec.is_empty());
        assert!(!spec.is_start());
        assert!(!spec.is_terminal());
        assert!(!spec.is_recoverable());
        assert!(spec.state_name().is_none());
        assert!(spec.must_reach().is_empty());
    }

    #[test]
    fn test_wire_spec_with_start() {
        let spec = WireSpec {
            annotations: vec![WireAnnotation::Start],
            span: None,
        };
        assert!(!spec.is_empty());
        assert!(spec.is_start());
        assert!(!spec.is_terminal());
    }

    #[test]
    fn test_wire_spec_with_state() {
        let spec = WireSpec {
            annotations: vec![WireAnnotation::State("payment".to_string())],
            span: None,
        };
        assert_eq!(spec.state_name(), Some("payment"));
    }

    #[test]
    fn test_wire_spec_must_reach() {
        let spec = WireSpec {
            annotations: vec![
                WireAnnotation::State("checkout".to_string()),
                WireAnnotation::MustReach(vec!["success".to_string(), "error".to_string()]),
            ],
            span: None,
        };
        let reaches = spec.must_reach();
        assert_eq!(reaches.len(), 2);
        assert!(reaches.contains(&"success"));
        assert!(reaches.contains(&"error"));
    }

    #[test]
    fn test_wire_verify_result_passed() {
        let result = WireVerifyResult::default();
        assert!(result.passed());
        assert_eq!(result.violation_count(), 0);
    }

    #[test]
    fn test_wire_verify_result_with_unreachable() {
        let result = WireVerifyResult {
            unreachable_states: vec![UnreachableState {
                state: "dead_code".to_string(),
                function: "unreachable_fn".to_string(),
                span: SourceSpan::default(),
            }],
            ..Default::default()
        };
        assert!(!result.passed());
        assert_eq!(result.violation_count(), 1);
    }

    #[test]
    fn test_wire_verify_result_with_missing_reach() {
        let result = WireVerifyResult {
            missing_reaches: vec![MissingReach {
                from_function: "checkout".to_string(),
                target_state: "payment".to_string(),
                span: SourceSpan::default(),
            }],
            ..Default::default()
        };
        assert!(!result.passed());
        assert_eq!(result.violation_count(), 1);
    }

    #[test]
    fn test_wire_annotation_serialization() {
        let ann = WireAnnotation::State("test".to_string());
        let json = serde_json::to_string(&ann).expect("serialize");
        let parsed: WireAnnotation = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(ann, parsed);
    }

    #[test]
    fn test_wire_spec_serialization() {
        let spec = WireSpec {
            annotations: vec![
                WireAnnotation::Start,
                WireAnnotation::MustReach(vec!["done".to_string()]),
            ],
            span: None,
        };
        let json = serde_json::to_string(&spec).expect("serialize");
        let parsed: WireSpec = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(spec.annotations.len(), parsed.annotations.len());
    }

    // ============================================
    // Path Anomaly Detection tests (Phase 6.5.4)
    // ============================================

    #[test]
    fn test_path_anomaly_unhandled_result() {
        let anomaly = PathAnomaly::UnhandledResult(UnhandledResult {
            function: "process_data".to_string(),
            call_site: "file.open()".to_string(),
            callee: "open".to_string(),
            handling: ResultHandling::Ignored,
            span: SourceSpan::default(),
        });
        assert!(anomaly.description().contains("unhandled Result"));
        assert!(anomaly.description().contains("open"));
    }

    #[test]
    fn test_path_anomaly_dead_code() {
        let anomaly = PathAnomaly::DeadCode(DeadCode {
            function: "unused_helper".to_string(),
            reason: DeadCodeReason::NeverCalled,
            span: SourceSpan::default(),
        });
        assert!(anomaly.description().contains("dead code"));
        assert!(anomaly.description().contains("unused_helper"));
    }

    #[test]
    fn test_path_anomaly_unused_value() {
        let anomaly = PathAnomaly::UnusedValue(UnusedValue {
            function: "calculate".to_string(),
            computation: "expensive_result".to_string(),
            span: SourceSpan::default(),
        });
        assert!(anomaly.description().contains("unused value"));
    }

    #[test]
    fn test_path_anomaly_missing_await() {
        let anomaly = PathAnomaly::MissingAwait(MissingAwait {
            function: "handle_request".to_string(),
            async_callee: "fetch_data".to_string(),
            span: SourceSpan::default(),
        });
        assert!(anomaly.description().contains("missing await"));
        assert!(anomaly.description().contains("fetch_data"));
    }

    #[test]
    fn test_result_handling_variants() {
        let ignored = ResultHandling::Ignored;
        let bound = ResultHandling::BoundButUnused;
        let unwrapped = ResultHandling::UnwrappedWithoutCheck;
        let ok_only = ResultHandling::OkOnlyHandled;

        // Just verify they exist and can be serialized
        let json = serde_json::to_string(&ignored).expect("serialize");
        assert!(json.contains("Ignored"));

        let json = serde_json::to_string(&bound).expect("serialize");
        assert!(json.contains("BoundButUnused"));

        let json = serde_json::to_string(&unwrapped).expect("serialize");
        assert!(json.contains("UnwrappedWithoutCheck"));

        let json = serde_json::to_string(&ok_only).expect("serialize");
        assert!(json.contains("OkOnlyHandled"));
    }

    #[test]
    fn test_dead_code_reason_variants() {
        let unreachable = DeadCodeReason::UnreachableFromStart;
        let conditional = DeadCodeReason::ConditionallyUnreachable {
            condition: "false".to_string(),
        };
        let never_called = DeadCodeReason::NeverCalled;
        let shadowed = DeadCodeReason::ShadowedDefinition;

        // Verify serialization
        let json = serde_json::to_string(&unreachable).expect("serialize");
        assert!(json.contains("UnreachableFromStart"));

        let json = serde_json::to_string(&conditional).expect("serialize");
        assert!(json.contains("ConditionallyUnreachable"));

        let json = serde_json::to_string(&never_called).expect("serialize");
        assert!(json.contains("NeverCalled"));

        let json = serde_json::to_string(&shadowed).expect("serialize");
        assert!(json.contains("ShadowedDefinition"));
    }

    #[test]
    fn test_wire_verify_result_with_path_anomalies() {
        let result = WireVerifyResult {
            path_anomalies: vec![PathAnomaly::DeadCode(DeadCode {
                function: "unused".to_string(),
                reason: DeadCodeReason::NeverCalled,
                span: SourceSpan::default(),
            })],
            ..Default::default()
        };
        assert!(!result.passed());
        assert_eq!(result.violation_count(), 1);
    }

    #[test]
    fn test_path_anomaly_serialization() {
        let anomaly = PathAnomaly::UnhandledResult(UnhandledResult {
            function: "test".to_string(),
            call_site: "io::read()".to_string(),
            callee: "read".to_string(),
            handling: ResultHandling::Ignored,
            span: SourceSpan::default(),
        });
        let json = serde_json::to_string(&anomaly).expect("serialize");
        let parsed: PathAnomaly = serde_json::from_str(&json).expect("deserialize");
        assert!(parsed.description().contains("read"));
    }

    #[test]
    fn test_path_anomaly_span() {
        let anomaly = PathAnomaly::DeadCode(DeadCode {
            function: "test".to_string(),
            reason: DeadCodeReason::NeverCalled,
            span: SourceSpan {
                file: Arc::from("main.rs"),
                line_start: 42,
                line_end: 50,
                col_start: 0,
                col_end: 10,
            },
        });
        let span = anomaly.span();
        assert_eq!(span.line_start, 42);
        assert_eq!(&*span.file, "main.rs");
    }

    #[test]
    fn test_partial_struct_update_creation() {
        let anomaly = PathAnomaly::PartialStructUpdate(PartialStructUpdate {
            function: "updater".to_string(),
            struct_type: "Point".to_string(),
            uninitialized_fields: vec!["y".to_string(), "z".to_string()],
            initialized_fields: vec!["x".to_string()],
            reason: PartialUpdateReason::StructUpdateSyntax,
            span: SourceSpan::default(),
        });

        let desc = anomaly.description();
        assert!(desc.contains("Point"));
        assert!(desc.contains("y, z"));
    }

    #[test]
    fn test_partial_struct_update_serialization() {
        let anomaly = PathAnomaly::PartialStructUpdate(PartialStructUpdate {
            function: "builder".to_string(),
            struct_type: "Config".to_string(),
            uninitialized_fields: vec!["timeout".to_string()],
            initialized_fields: vec!["host".to_string(), "port".to_string()],
            reason: PartialUpdateReason::MissingFieldInit,
            span: SourceSpan::default(),
        });

        let json = serde_json::to_string(&anomaly).expect("serialize");
        assert!(json.contains("PartialStructUpdate"));
        assert!(json.contains("Config"));
        assert!(json.contains("timeout"));
        assert!(json.contains("MissingFieldInit"));

        let parsed: PathAnomaly = serde_json::from_str(&json).expect("deserialize");
        if let PathAnomaly::PartialStructUpdate(update) = parsed {
            assert_eq!(update.function, "builder");
            assert_eq!(update.struct_type, "Config");
            assert_eq!(update.uninitialized_fields, vec!["timeout".to_string()]);
            assert!(matches!(
                update.reason,
                PartialUpdateReason::MissingFieldInit
            ));
        } else {
            panic!("Expected PartialStructUpdate");
        }
    }

    #[test]
    fn test_partial_update_reason_variants() {
        let reasons = vec![
            PartialUpdateReason::StructUpdateSyntax,
            PartialUpdateReason::MissingFieldInit,
            PartialUpdateReason::PartialMove,
            PartialUpdateReason::PartialMutation,
        ];

        for reason in reasons {
            let json = serde_json::to_string(&reason).expect("serialize");
            let parsed: PartialUpdateReason = serde_json::from_str(&json).expect("deserialize");
            // Just verify serialization round-trips
            let json2 = serde_json::to_string(&parsed).expect("serialize");
            assert_eq!(json, json2);
        }
    }

    // ============================================
    // Async Chain Tracking tests (Phase 6.5.2)
    // ============================================

    #[test]
    fn test_async_chain_new() {
        let chain = AsyncChain::new(1);
        assert_eq!(chain.id, 1);
        assert!(chain.nodes.is_empty());
        assert!(!chain.is_terminated);
        assert!(chain.termination.is_none());
    }

    #[test]
    fn test_async_chain_add_node() {
        let mut chain = AsyncChain::new(1);
        let node = AsyncChainNode::new("async_fetch", true, SourceSpan::default());
        chain.add_node(node);

        assert_eq!(chain.len(), 1);
        assert!(!chain.is_empty());
        assert_eq!(chain.origin(), Some("async_fetch"));
    }

    #[test]
    fn test_async_chain_terminate() {
        let mut chain = AsyncChain::new(1);
        chain.add_node(AsyncChainNode::new("async_op", true, SourceSpan::default()));
        chain.terminate(AsyncTermination::Awaited);

        assert!(chain.is_terminated);
        assert!(matches!(chain.termination, Some(AsyncTermination::Awaited)));
    }

    #[test]
    fn test_async_chain_functions() {
        let mut chain = AsyncChain::new(1);
        chain.add_node(AsyncChainNode::new("start", true, SourceSpan::default()));
        chain.add_node(AsyncChainNode::new("middle", false, SourceSpan::default()));
        chain.add_node(AsyncChainNode::new("end", false, SourceSpan::default()));

        let funcs = chain.functions();
        assert_eq!(funcs, vec!["start", "middle", "end"]);
    }

    #[test]
    fn test_async_chain_has_any_await() {
        let mut chain = AsyncChain::new(1);
        chain.add_node(AsyncChainNode::new("no_await", true, SourceSpan::default()));
        assert!(!chain.has_any_await());

        chain
            .add_node(AsyncChainNode::new("with_await", false, SourceSpan::default()).with_await());
        assert!(chain.has_any_await());
    }

    #[test]
    fn test_async_chain_node_new() {
        let node = AsyncChainNode::new("async_fn", true, SourceSpan::default());
        assert_eq!(node.function, "async_fn");
        assert!(node.is_origin);
        assert!(!node.has_await);
        assert!(node.callees.is_empty());
    }

    #[test]
    fn test_async_chain_node_with_await() {
        let node = AsyncChainNode::new("fn", false, SourceSpan::default()).with_await();
        assert!(node.has_await);
    }

    #[test]
    fn test_async_chain_node_with_callees() {
        let node = AsyncChainNode::new("fn", false, SourceSpan::default())
            .with_callees(vec!["callee1".to_string(), "callee2".to_string()]);
        assert_eq!(node.callees.len(), 2);
        assert_eq!(node.callees[0], "callee1");
    }

    #[test]
    fn test_async_chain_violation_new() {
        let mut chain = AsyncChain::new(1);
        chain.add_node(AsyncChainNode::new("async_op", true, SourceSpan::default()));

        let violation = AsyncChainViolation::new(
            chain,
            AsyncChainViolationType::NoAwaitPoint,
            "Future never awaited",
            SourceSpan::default(),
        );

        assert!(matches!(
            violation.violation_type,
            AsyncChainViolationType::NoAwaitPoint
        ));
        assert_eq!(violation.description, "Future never awaited");
        assert_eq!(violation.origin_function(), Some("async_op"));
    }

    #[test]
    fn test_async_chain_violation_types() {
        let types = vec![
            AsyncChainViolationType::NoAwaitPoint,
            AsyncChainViolationType::IncompleteChain,
            AsyncChainViolationType::UnreachableAfterAwait,
            AsyncChainViolationType::DanglingSpawn,
            AsyncChainViolationType::CyclicDependency,
            AsyncChainViolationType::SyncBoundaryCrossing,
            AsyncChainViolationType::IndirectAsyncCall,
            AsyncChainViolationType::UnmonitoredSpawnClosure,
        ];

        for violation_type in types {
            let json = serde_json::to_string(&violation_type).expect("serialize");
            let parsed: AsyncChainViolationType = serde_json::from_str(&json).expect("deserialize");
            let json2 = serde_json::to_string(&parsed).expect("serialize");
            assert_eq!(json, json2);
        }
    }

    #[test]
    fn test_async_termination_types() {
        let terms = vec![
            AsyncTermination::Awaited,
            AsyncTermination::BlockOn,
            AsyncTermination::Spawned,
            AsyncTermination::Stored,
            AsyncTermination::Returned,
            AsyncTermination::Dropped,
        ];

        for term in terms {
            let json = serde_json::to_string(&term).expect("serialize");
            let parsed: AsyncTermination = serde_json::from_str(&json).expect("deserialize");
            let json2 = serde_json::to_string(&parsed).expect("serialize");
            assert_eq!(json, json2);
        }
    }

    #[test]
    fn test_async_chain_serialization() {
        let mut chain = AsyncChain::new(42);
        chain.add_node(
            AsyncChainNode::new("async_fetch", true, SourceSpan::default())
                .with_await()
                .with_callees(vec!["http_get".to_string()]),
        );
        chain.terminate(AsyncTermination::Awaited);

        let json = serde_json::to_string(&chain).expect("serialize");
        assert!(json.contains("async_fetch"));
        assert!(json.contains("Awaited"));

        let parsed: AsyncChain = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.id, 42);
        assert!(parsed.is_terminated);
        assert_eq!(parsed.origin(), Some("async_fetch"));
    }

    #[test]
    fn test_async_chain_violation_serialization() {
        let mut chain = AsyncChain::new(1);
        chain.add_node(AsyncChainNode::new(
            "spawn_task",
            true,
            SourceSpan::default(),
        ));

        let violation = AsyncChainViolation::new(
            chain,
            AsyncChainViolationType::DanglingSpawn,
            "Spawned task not joined",
            SourceSpan::default(),
        );

        let json = serde_json::to_string(&violation).expect("serialize");
        assert!(json.contains("DanglingSpawn"));
        assert!(json.contains("spawn_task"));

        let parsed: AsyncChainViolation = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(
            parsed.violation_type,
            AsyncChainViolationType::DanglingSpawn
        ));
    }

    #[test]
    fn test_path_anomaly_async_chain_violation() {
        let mut chain = AsyncChain::new(1);
        chain.add_node(AsyncChainNode::new(
            "leaked_future",
            true,
            SourceSpan::default(),
        ));

        let anomaly = PathAnomaly::AsyncChainViolation(AsyncChainViolation::new(
            chain,
            AsyncChainViolationType::NoAwaitPoint,
            "Future created but never awaited",
            SourceSpan::default(),
        ));

        let desc = anomaly.description();
        assert!(desc.contains("leaked_future"));
        assert!(desc.contains("Future created but never awaited"));

        // Test serialization
        let json = serde_json::to_string(&anomaly).expect("serialize");
        assert!(json.contains("AsyncChainViolation"));
        let parsed: PathAnomaly = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(parsed, PathAnomaly::AsyncChainViolation(_)));
    }

    #[test]
    fn test_async_chain_empty_origin() {
        let chain = AsyncChain::new(1);
        assert!(chain.origin().is_none());
        assert!(!chain.has_any_await());
    }

    #[test]
    fn test_async_chain_multiple_origins() {
        // Only first marked as origin should be returned
        let mut chain = AsyncChain::new(1);
        chain.add_node(AsyncChainNode::new("first", true, SourceSpan::default()));
        chain.add_node(AsyncChainNode::new("second", true, SourceSpan::default()));

        // Should return first origin
        assert_eq!(chain.origin(), Some("first"));
    }

    // ============================================
    // Effect-Based Optimization tests (Phase 5.3)
    // ============================================

    #[test]
    fn test_effect_optimization_description() {
        assert!(EffectOptimization::Memoizable
            .description()
            .contains("pure"));
        assert!(EffectOptimization::NoUnwind.description().contains("panic"));
        assert!(EffectOptimization::EmbeddedSafe
            .description()
            .contains("allocate"));
        assert!(EffectOptimization::ConstEvalCandidate
            .description()
            .contains("I/O"));
        assert!(EffectOptimization::ThreadSafe
            .description()
            .contains("thread"));
        assert!(EffectOptimization::MemorySafe
            .description()
            .contains("unsafe"));
    }

    #[test]
    fn test_effect_optimization_name() {
        assert_eq!(EffectOptimization::Memoizable.name(), "memoizable");
        assert_eq!(EffectOptimization::NoUnwind.name(), "no_unwind");
        assert_eq!(EffectOptimization::EmbeddedSafe.name(), "embedded_safe");
        assert_eq!(EffectOptimization::ConstEvalCandidate.name(), "const_eval");
        assert_eq!(EffectOptimization::ThreadSafe.name(), "thread_safe");
        assert_eq!(EffectOptimization::MemorySafe.name(), "memory_safe");
    }

    #[test]
    fn test_effect_optimizations_empty() {
        let opts = EffectOptimizations::empty();
        assert!(opts.is_empty());
        assert_eq!(opts.len(), 0);
        assert!(!opts.is_memoizable());
        assert!(!opts.is_no_unwind());
        assert!(!opts.is_embedded_safe());
    }

    #[test]
    fn test_effect_optimizations_add() {
        let mut opts = EffectOptimizations::empty();
        opts.add(EffectOptimization::Memoizable);
        opts.add(EffectOptimization::NoUnwind);

        assert!(opts.is_memoizable());
        assert!(opts.is_no_unwind());
        assert!(!opts.is_embedded_safe());
        assert_eq!(opts.len(), 2);
    }

    #[test]
    fn test_effect_optimizations_from_optimizations() {
        let opts = EffectOptimizations::from_optimizations([
            EffectOptimization::Memoizable,
            EffectOptimization::EmbeddedSafe,
        ]);

        assert!(opts.is_memoizable());
        assert!(opts.is_embedded_safe());
        assert_eq!(opts.len(), 2);
    }

    #[test]
    fn test_effect_optimizations_from_pure_effects() {
        // Pure function (no effects) should get all optimizations
        let pure_effects = EffectSet::empty();
        let opts = EffectOptimizations::from_effects(&pure_effects);

        assert!(opts.is_memoizable());
        assert!(opts.is_no_unwind());
        assert!(opts.is_embedded_safe());
        assert!(opts.has(EffectOptimization::ConstEvalCandidate));
        assert!(opts.has(EffectOptimization::ThreadSafe));
        assert!(opts.has(EffectOptimization::MemorySafe));
        assert_eq!(opts.len(), 6); // All 6 optimizations
    }

    #[test]
    fn test_effect_optimizations_from_io_only() {
        // Function with only IO effect
        let io_effects = EffectSet::from_effects([Effect::IO]);
        let opts = EffectOptimizations::from_effects(&io_effects);

        // Should NOT be memoizable (has effects)
        assert!(!opts.is_memoizable());
        // Should be NoUnwind (no Panic)
        assert!(opts.is_no_unwind());
        // Should be EmbeddedSafe (no Alloc)
        assert!(opts.is_embedded_safe());
        // Should NOT be const eval candidate (has IO)
        assert!(!opts.has(EffectOptimization::ConstEvalCandidate));
        // Should be ThreadSafe (no GlobalState)
        assert!(opts.has(EffectOptimization::ThreadSafe));
        // Should be MemorySafe (no Unsafe)
        assert!(opts.has(EffectOptimization::MemorySafe));
    }

    #[test]
    fn test_effect_optimizations_from_panic_only() {
        // Function with only Panic effect
        let panic_effects = EffectSet::from_effects([Effect::Panic]);
        let opts = EffectOptimizations::from_effects(&panic_effects);

        // Should NOT be NoUnwind (has Panic)
        assert!(!opts.is_no_unwind());
        // Should be EmbeddedSafe (no Alloc)
        assert!(opts.is_embedded_safe());
        // Should be const eval candidate (no IO)
        assert!(opts.has(EffectOptimization::ConstEvalCandidate));
    }

    #[test]
    fn test_effect_optimizations_from_alloc_only() {
        // Function with only Alloc effect
        let alloc_effects = EffectSet::from_effects([Effect::Alloc]);
        let opts = EffectOptimizations::from_effects(&alloc_effects);

        // Should be NoUnwind (no Panic)
        assert!(opts.is_no_unwind());
        // Should NOT be EmbeddedSafe (has Alloc)
        assert!(!opts.is_embedded_safe());
    }

    #[test]
    fn test_effect_optimizations_from_multiple_effects() {
        // Function with IO, Panic, and Alloc effects
        let effects = EffectSet::from_effects([Effect::IO, Effect::Panic, Effect::Alloc]);
        let opts = EffectOptimizations::from_effects(&effects);

        // Should NOT be memoizable
        assert!(!opts.is_memoizable());
        // Should NOT be NoUnwind (has Panic)
        assert!(!opts.is_no_unwind());
        // Should NOT be EmbeddedSafe (has Alloc)
        assert!(!opts.is_embedded_safe());
        // Should NOT be const eval candidate (has IO)
        assert!(!opts.has(EffectOptimization::ConstEvalCandidate));
        // Should be ThreadSafe (no GlobalState)
        assert!(opts.has(EffectOptimization::ThreadSafe));
        // Should be MemorySafe (no Unsafe)
        assert!(opts.has(EffectOptimization::MemorySafe));
    }

    #[test]
    fn test_effect_optimizations_source() {
        let opts = EffectOptimizations::empty();
        assert_eq!(opts.source(), OptimizationSource::Inferred);

        let opts_declared = opts.with_source(OptimizationSource::Declared);
        assert_eq!(opts_declared.source(), OptimizationSource::Declared);

        let opts_verified = EffectOptimizations::empty().with_source(OptimizationSource::Verified);
        assert_eq!(opts_verified.source(), OptimizationSource::Verified);
    }

    #[test]
    fn test_effect_optimizations_to_names() {
        let opts = EffectOptimizations::from_optimizations([
            EffectOptimization::Memoizable,
            EffectOptimization::NoUnwind,
        ]);
        let names = opts.to_names();
        assert!(names.contains(&"memoizable"));
        assert!(names.contains(&"no_unwind"));
        assert_eq!(names.len(), 2);
    }

    #[test]
    fn test_effect_optimizations_serialization() {
        let opts = EffectOptimizations::from_optimizations([
            EffectOptimization::Memoizable,
            EffectOptimization::EmbeddedSafe,
        ]);
        let json = serde_json::to_string(&opts).expect("serialize");
        let parsed: EffectOptimizations = serde_json::from_str(&json).expect("deserialize");

        assert!(parsed.is_memoizable());
        assert!(parsed.is_embedded_safe());
        assert_eq!(parsed.len(), 2);
    }

    #[test]
    fn test_effect_optimization_serialization() {
        let opt = EffectOptimization::Memoizable;
        let json = serde_json::to_string(&opt).expect("serialize");
        let parsed: EffectOptimization = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(opt, parsed);
    }

    #[test]
    fn test_optimization_source_serialization() {
        for source in [
            OptimizationSource::Inferred,
            OptimizationSource::Declared,
            OptimizationSource::Verified,
        ] {
            let json = serde_json::to_string(&source).expect("serialize");
            let parsed: OptimizationSource = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(source, parsed);
        }
    }

    // ============================================
    // Tactic tests (Phase 8.3)
    // ============================================

    #[test]
    fn test_tactic_kind_induction() {
        let tactic = TacticKind::induction("n");
        assert!(
            matches!(tactic, TacticKind::Induction(InductionTarget::Variable(ref v)) if v == "n")
        );
        assert_eq!(tactic.description(), "induction on n");
    }

    #[test]
    fn test_tactic_kind_induction_param() {
        let tactic = TacticKind::induction_param(0);
        assert!(matches!(
            tactic,
            TacticKind::Induction(InductionTarget::Parameter(0))
        ));
        assert_eq!(tactic.description(), "induction on parameter 0");
    }

    #[test]
    fn test_tactic_kind_case_split() {
        let tactic = TacticKind::case_split("x > 0");
        assert!(
            matches!(tactic, TacticKind::CaseSplit(CaseSplitCondition::Expression(ref e)) if e == "x > 0")
        );
        assert_eq!(tactic.description(), "case split on x > 0");
    }

    #[test]
    fn test_tactic_kind_case_split_sign() {
        let tactic = TacticKind::case_split_sign("x");
        assert!(
            matches!(tactic, TacticKind::CaseSplit(CaseSplitCondition::Sign(ref v)) if v == "x")
        );
        assert_eq!(tactic.description(), "case split on x >= 0");
    }

    #[test]
    fn test_tactic_kind_custom() {
        let tactic = TacticKind::custom("my_tactic");
        assert!(matches!(tactic, TacticKind::Custom(ref s) if s == "my_tactic"));
        assert_eq!(tactic.description(), "custom tactic 'my_tactic'");
    }

    #[test]
    fn test_induction_target_variable() {
        let target = InductionTarget::var("n");
        assert_eq!(target.description(), "n");
    }

    #[test]
    fn test_induction_target_parameter() {
        let target = InductionTarget::param(2);
        assert_eq!(target.description(), "parameter 2");
    }

    #[test]
    fn test_induction_target_tuple() {
        let target = InductionTarget::tuple(["x", "y", "z"]);
        assert_eq!(target.description(), "(x, y, z)");
    }

    #[test]
    fn test_induction_target_structural() {
        let target = InductionTarget::structural("List");
        assert_eq!(target.description(), "structure of List");
    }

    #[test]
    fn test_case_split_expression() {
        let cond = CaseSplitCondition::expr("x == y");
        assert_eq!(cond.description(), "x == y");
        let cases = cond.get_cases();
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0].0, "case: x == y");
        assert_eq!(cases[1].0, "case: ¬(x == y)");
    }

    #[test]
    fn test_case_split_sign() {
        let cond = CaseSplitCondition::sign("x");
        assert_eq!(cond.description(), "x >= 0");
        let cases = cond.get_cases();
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0].1, "(>= x 0)");
        assert_eq!(cases[1].1, "(< x 0)");
    }

    #[test]
    fn test_case_split_enum() {
        let cond = CaseSplitCondition::enum_split(
            "color",
            vec!["Red".to_string(), "Green".to_string(), "Blue".to_string()],
        );
        assert!(cond.description().contains("Red"));
        let cases = cond.get_cases();
        assert_eq!(cases.len(), 3);
    }

    #[test]
    fn test_case_split_option() {
        let cond = CaseSplitCondition::option("opt");
        assert_eq!(cond.description(), "opt.is_some()");
        let cases = cond.get_cases();
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0].1, "(is-Some opt)");
        assert_eq!(cases[1].1, "(is-None opt)");
    }

    #[test]
    fn test_case_split_result() {
        let cond = CaseSplitCondition::result("res");
        assert_eq!(cond.description(), "res.is_ok()");
        let cases = cond.get_cases();
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0].1, "(is-Ok res)");
        assert_eq!(cases[1].1, "(is-Err res)");
    }

    #[test]
    fn test_tactic_annotation_new() {
        let tactic = TacticAnnotation::new(TacticKind::induction("n"), SourceSpan::default());
        assert!(tactic.label.is_none());
        assert!(tactic.hints.is_empty());
    }

    #[test]
    fn test_tactic_annotation_with_label() {
        let tactic = TacticAnnotation::new(TacticKind::induction("n"), SourceSpan::default())
            .with_label("sum formula");
        assert_eq!(tactic.label, Some("sum formula".to_string()));
        assert_eq!(tactic.format_description(), "induction on n (sum formula)");
    }

    #[test]
    fn test_tactic_annotation_with_hints() {
        let tactic = TacticAnnotation::new(TacticKind::induction("n"), SourceSpan::default())
            .with_hint(TacticHint::base_case("0"))
            .with_hint(TacticHint::step(1));
        assert_eq!(tactic.hints.len(), 2);
    }

    #[test]
    fn test_tactic_hint_base_case() {
        let hint = TacticHint::base_case("0");
        assert!(matches!(hint, TacticHint::BaseCase(ref s) if s == "0"));
    }

    #[test]
    fn test_tactic_hint_step_size() {
        let hint = TacticHint::step(2);
        assert!(matches!(hint, TacticHint::StepSize(2)));
    }

    #[test]
    fn test_tactic_hint_use_lemmas() {
        let hint = TacticHint::use_lemmas(vec!["add_comm".to_string(), "add_assoc".to_string()]);
        assert!(matches!(hint, TacticHint::UseLemmas(ref v) if v.len() == 2));
    }

    #[test]
    fn test_tactic_hint_max_depth() {
        let hint = TacticHint::max_depth(10);
        assert!(matches!(hint, TacticHint::MaxDepth(10)));
    }

    #[test]
    fn test_tactic_hint_timeout() {
        let hint = TacticHint::timeout(5000);
        assert!(matches!(hint, TacticHint::Timeout(5000)));
    }

    #[test]
    fn test_tactic_registry_new() {
        let registry = TacticRegistry::new();
        assert!(!registry.contains("foo"));
        assert_eq!(registry.names().count(), 0);
    }

    #[test]
    fn test_tactic_registry_register_and_get() {
        let mut registry = TacticRegistry::new();
        let tactic = CustomTactic::new(
            "auto_split",
            "Automatically split on all conditions",
            TacticTransform::Simplify,
        );
        registry.register(tactic);

        assert!(registry.contains("auto_split"));
        let retrieved = registry.get("auto_split").unwrap();
        assert_eq!(
            retrieved.description,
            "Automatically split on all conditions"
        );
    }

    #[test]
    fn test_tactic_registry_names() {
        let mut registry = TacticRegistry::new();
        registry.register(CustomTactic::new(
            "tactic1",
            "desc1",
            TacticTransform::Simplify,
        ));
        registry.register(CustomTactic::new(
            "tactic2",
            "desc2",
            TacticTransform::Simplify,
        ));

        let names: Vec<_> = registry.names().collect();
        assert_eq!(names.len(), 2);
        assert!(names.contains(&"tactic1"));
        assert!(names.contains(&"tactic2"));
    }

    #[test]
    fn test_custom_tactic_new() {
        let tactic = CustomTactic::new(
            "my_tactic",
            "Does something useful",
            TacticTransform::Split {
                subgoals: vec!["goal1".to_string(), "goal2".to_string()],
            },
        );
        assert_eq!(tactic.name, "my_tactic");
        assert_eq!(tactic.description, "Does something useful");
        assert!(
            matches!(tactic.transform, TacticTransform::Split { ref subgoals } if subgoals.len() == 2)
        );
    }

    #[test]
    fn test_tactic_transform_split() {
        let transform = TacticTransform::Split {
            subgoals: vec!["g1".to_string()],
        };
        assert!(matches!(transform, TacticTransform::Split { .. }));
    }

    #[test]
    fn test_tactic_transform_assume() {
        let transform = TacticTransform::Assume {
            assumptions: vec!["x > 0".to_string()],
        };
        assert!(matches!(transform, TacticTransform::Assume { .. }));
    }

    #[test]
    fn test_tactic_transform_unfold() {
        let transform = TacticTransform::Unfold {
            name: "my_def".to_string(),
        };
        assert!(matches!(transform, TacticTransform::Unfold { ref name } if name == "my_def"));
    }

    #[test]
    fn test_tactic_transform_sequence() {
        let transform = TacticTransform::Sequence(vec![
            TacticTransform::Simplify,
            TacticTransform::Unfold {
                name: "foo".to_string(),
            },
        ]);
        assert!(matches!(transform, TacticTransform::Sequence(ref v) if v.len() == 2));
    }

    #[test]
    fn test_tactic_kind_serialization() {
        let tactic = TacticKind::induction("n");
        let json = serde_json::to_string(&tactic).expect("serialize");
        let parsed: TacticKind = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(tactic, parsed);
    }

    #[test]
    fn test_induction_target_serialization() {
        for target in [
            InductionTarget::var("x"),
            InductionTarget::param(0),
            InductionTarget::tuple(["a", "b"]),
            InductionTarget::structural("Tree"),
        ] {
            let json = serde_json::to_string(&target).expect("serialize");
            let parsed: InductionTarget = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(target, parsed);
        }
    }

    #[test]
    fn test_case_split_condition_serialization() {
        for cond in [
            CaseSplitCondition::expr("x > 0"),
            CaseSplitCondition::sign("y"),
            CaseSplitCondition::option("opt"),
            CaseSplitCondition::result("res"),
        ] {
            let json = serde_json::to_string(&cond).expect("serialize");
            let parsed: CaseSplitCondition = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(cond, parsed);
        }
    }

    #[test]
    fn test_tactic_annotation_serialization() {
        let tactic = TacticAnnotation::new(TacticKind::case_split("x > 0"), SourceSpan::default())
            .with_label("positive case")
            .with_hint(TacticHint::timeout(1000));

        let json = serde_json::to_string(&tactic).expect("serialize");
        let parsed: TacticAnnotation = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(parsed.label, Some("positive case".to_string()));
        assert_eq!(parsed.hints.len(), 1);
    }

    #[test]
    fn test_tactic_hint_serialization() {
        for hint in [
            TacticHint::base_case("0"),
            TacticHint::step(1),
            TacticHint::use_lemmas(vec!["lem".to_string()]),
            TacticHint::max_depth(5),
            TacticHint::timeout(1000),
        ] {
            let json = serde_json::to_string(&hint).expect("serialize");
            let parsed: TacticHint = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(hint, parsed);
        }
    }

    #[test]
    fn test_tactic_transform_serialization() {
        for transform in [
            TacticTransform::Simplify,
            TacticTransform::Split {
                subgoals: vec!["g".to_string()],
            },
            TacticTransform::Assume {
                assumptions: vec!["a".to_string()],
            },
            TacticTransform::Unfold {
                name: "f".to_string(),
            },
            TacticTransform::Sequence(vec![TacticTransform::Simplify]),
        ] {
            let json = serde_json::to_string(&transform).expect("serialize");
            let parsed: TacticTransform = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(transform, parsed);
        }
    }
}
