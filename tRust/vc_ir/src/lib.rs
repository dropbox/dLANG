//! Verification Condition Intermediate Representation
//!
//! This crate defines the common IR that sits between rustc's MIR and
//! the various proof backends (Z4, Kani, TLA, Lean5, CROWN, etc.).
//!
//! The VC IR is designed to be:
//! - Backend-agnostic: any prover can consume it
//! - Rich enough to express all verification conditions from Rust
//! - Serializable for proof caching
//! - Incrementally verifiable

pub mod backend;
pub mod certificate;
pub mod config;
pub mod error;
pub mod expr;
pub mod nn;
pub mod pred;
pub mod proof_hints;
pub mod specs;
pub mod tactic_exec;
pub mod temporal;

pub use backend::*;
pub use certificate::*;
pub use config::*;
pub use error::*;
pub use expr::*;
pub use nn::*;
pub use pred::*;
pub use proof_hints::*;
pub use specs::*;
pub use tactic_exec::*;
pub use temporal::*;

use serde::{Deserialize, Serialize};

/// Trust level for a crate or module
///
/// Determines what level of verification is required and how
/// unverified code is treated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub enum TrustLevel {
    /// Fully verified - all specs must be proven
    /// Verification failures are compile errors
    Verified,

    /// Assumed correct - no verification performed
    /// Used for legacy code, FFI, or code being gradually migrated
    #[default]
    Assumed,

    /// Externally audited - has specs but not machine-verified
    /// Specs are trusted without proof
    Audited,

    /// Verified with warnings - specs must be proven, but failures are warnings
    /// Useful during development/migration
    VerifiedWarn,
}

impl TrustLevel {
    /// Parse trust level from string
    #[allow(clippy::should_implement_trait)] // Returns Option, not Result like FromStr
    #[must_use]
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "verified" => Some(Self::Verified),
            "assumed" => Some(Self::Assumed),
            "audited" => Some(Self::Audited),
            "verified_warn" | "verified-warn" => Some(Self::VerifiedWarn),
            _ => None,
        }
    }

    /// Returns true if this level requires verification
    #[must_use]
    pub const fn requires_verification(&self) -> bool {
        matches!(self, Self::Verified | Self::VerifiedWarn)
    }

    /// Returns true if verification failures should be errors
    #[must_use]
    pub const fn failures_are_errors(&self) -> bool {
        matches!(self, Self::Verified)
    }

    /// Returns the string representation
    #[must_use]
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::Verified => "verified",
            Self::Assumed => "assumed",
            Self::Audited => "audited",
            Self::VerifiedWarn => "verified_warn",
        }
    }
}
use std::sync::Arc;

/// Unique identifier for a verification condition
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VcId(pub u64);

/// A verification condition to be proven
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationCondition {
    /// Unique identifier
    pub id: VcId,
    /// Human-readable name for error reporting
    pub name: String,
    /// Source location for error reporting
    pub span: SourceSpan,
    /// The actual condition to verify
    pub condition: VcKind,
    /// Hint about which backend to prefer
    pub preferred_backend: Option<BackendHint>,
}

/// The kind of verification condition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VcKind {
    /// Simple predicate that must hold (requires/ensures/invariant)
    Predicate(Predicate),

    /// Implication: if antecedent holds, consequent must hold
    Implies {
        antecedent: Predicate,
        consequent: Predicate,
    },

    /// Universal quantification
    Forall {
        vars: Vec<BoundVar>,
        body: Box<VcKind>,
    },

    /// Existential quantification
    Exists {
        vars: Vec<BoundVar>,
        body: Box<VcKind>,
    },

    /// Temporal property (for distributed systems)
    Temporal(TemporalFormula),

    /// Neural network property (robustness, bounds)
    NeuralNetwork(NnSpec),

    /// Termination proof obligation
    Termination {
        decreases: Expr,
        recursive_calls: Vec<Expr>,
    },

    /// Memory safety (separation logic)
    Separation(SeparationAssertion),
}

/// Hint for which backend should handle this VC
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BackendHint {
    /// SMT solver (Z4) - good for decidable arithmetic, arrays, bitvectors
    Smt,
    /// Bounded model checker (Kani) - exhaustive up to bounds
    BoundedModelCheck,
    /// Temporal logic (TLA) - distributed systems properties
    TemporalLogic,
    /// Theorem prover (Lean5) - inductive proofs, complex math
    TheoremProver,
    /// Separation logic (Prusti) - heap reasoning
    SeparationLogic,
    /// Neural network verifier (CROWN) - certified bounds
    NeuralNetwork,
    /// Property testing (proptest) - fast feedback, fuzzing
    PropertyTest,
}

/// Source location for error reporting
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceSpan {
    pub file: Arc<str>,
    pub line_start: u32,
    pub line_end: u32,
    pub col_start: u32,
    pub col_end: u32,
}

impl Default for SourceSpan {
    fn default() -> Self {
        Self {
            file: "<unknown>".into(),
            line_start: 0,
            line_end: 0,
            col_start: 0,
            col_end: 0,
        }
    }
}

impl SourceSpan {
    /// Create a dummy source span for testing
    #[must_use]
    pub fn dummy() -> Self {
        Self::default()
    }
}

impl std::fmt::Display for SourceSpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.line_start == self.line_end {
            write!(
                f,
                "{}:{}:{}-{}",
                self.file, self.line_start, self.col_start, self.col_end
            )
        } else {
            write!(
                f,
                "{}:{}:{}-{}:{}",
                self.file, self.line_start, self.col_start, self.line_end, self.col_end
            )
        }
    }
}

/// A bound variable in a quantifier
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BoundVar {
    pub name: String,
    pub ty: VcType,
}

/// Types in the VC IR
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VcType {
    Bool,
    Int {
        signed: bool,
        bits: u32,
    },
    Float {
        bits: u32,
    },
    BitVec {
        bits: u32,
    },
    Array {
        elem: Box<VcType>,
        len: Option<usize>,
    },
    Tuple(Vec<VcType>),
    Struct {
        name: String,
        fields: Vec<(String, VcType)>,
    },
    Ref {
        mutable: bool,
        inner: Box<VcType>,
    },
    /// Neural network tensor
    Tensor {
        elem: Box<VcType>,
        shape: Vec<usize>,
    },
    /// Abstract/opaque type
    Abstract(String),
}

impl std::fmt::Display for VcType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool => write!(f, "bool"),
            Self::Int { signed, bits } => {
                let prefix = if *signed { "i" } else { "u" };
                write!(f, "{prefix}{bits}")
            }
            Self::Float { bits } => write!(f, "f{bits}"),
            Self::BitVec { bits } => write!(f, "bv{bits}"),
            Self::Array { elem, len } => match len {
                Some(len) => write!(f, "[{elem}; {len}]"),
                None => write!(f, "[{elem}]"),
            },
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
            Self::Struct { name, .. } | Self::Abstract(name) => write!(f, "{name}"),
            Self::Ref { mutable, inner } => {
                if *mutable {
                    write!(f, "&mut {inner}")
                } else {
                    write!(f, "&{inner}")
                }
            }
            Self::Tensor { elem, shape } => {
                write!(f, "tensor<{elem}>[")?;
                for (i, dim) in shape.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{dim}")?;
                }
                write!(f, "]")
            }
        }
    }
}

/// A set of verification conditions for a function
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionVcs {
    /// Function name
    pub name: String,
    /// Function signature for context
    pub signature: FunctionSignature,
    /// Preconditions (from `#[requires]`)
    pub requires: Vec<VerificationCondition>,
    /// Postconditions (from `#[ensures]`)
    pub ensures: Vec<VerificationCondition>,
    /// Loop invariants
    pub loop_invariants: Vec<VerificationCondition>,
    /// Assertion VCs (from assert! with proofs)
    pub assertions: Vec<VerificationCondition>,
    /// Termination proof obligations
    pub termination: Option<VerificationCondition>,
}

/// Function signature in VC IR
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionSignature {
    pub name: String,
    pub params: Vec<(String, VcType)>,
    pub return_type: VcType,
}

/// Overall verification result
#[derive(Debug, Clone)]
pub enum VerifyResult {
    /// All conditions proven
    Proven,
    /// At least one condition has a counterexample
    Counterexample(Counterexample),
    /// Verification timed out
    Timeout {
        partial_results: Vec<(VcId, VerifyResult)>,
    },
    /// Backend error
    Error(VerifyError),
    /// Unknown (solver returned unknown)
    Unknown { reason: String },
}

/// A counterexample showing why a VC failed
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Counterexample {
    pub vc_id: VcId,
    /// Variable assignments that violate the condition
    pub assignments: Vec<(String, Value)>,
    /// Execution trace (for temporal/BMC)
    pub trace: Option<Vec<TraceStep>>,
    /// Human-readable explanation
    pub explanation: String,
}

/// A concrete value in a counterexample
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Value {
    Bool(bool),
    Int(i128),
    Float(f64),
    BitVec {
        bits: u32,
        value: Vec<u8>,
    },
    Array(Vec<Value>),
    Tuple(Vec<Value>),
    Struct {
        name: String,
        fields: Vec<(String, Value)>,
    },
    Tensor {
        shape: Vec<usize>,
        data: Vec<f64>,
    },
}

/// A step in an execution trace
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraceStep {
    pub location: SourceSpan,
    pub state: Vec<(String, Value)>,
    pub action: Option<String>,
}

// ============================================
// Display implementations for counterexample presentation (N4.1)
// ============================================

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Int(i) => write!(f, "{i}"),
            Value::Float(fl) => {
                // Handle special float values
                if fl.is_nan() {
                    write!(f, "NaN")
                } else if fl.is_infinite() {
                    if *fl > 0.0 {
                        write!(f, "+Inf")
                    } else {
                        write!(f, "-Inf")
                    }
                } else {
                    write!(f, "{fl}")
                }
            }
            Value::BitVec { bits, value } => {
                // Format as hex for readability
                write!(f, "0x")?;
                for byte in value.iter().rev() {
                    write!(f, "{byte:02x}")?;
                }
                write!(f, " (bv{bits})")
            }
            Value::Array(elems) => {
                write!(f, "[")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{elem}")?;
                }
                write!(f, "]")
            }
            Value::Tuple(elems) => {
                write!(f, "(")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{elem}")?;
                }
                write!(f, ")")
            }
            Value::Struct { name, fields } => {
                write!(f, "{name} {{ ")?;
                for (i, (field_name, val)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{field_name}: {val}")?;
                }
                write!(f, " }}")
            }
            Value::Tensor { shape, data } => {
                write!(f, "Tensor<")?;
                for (i, dim) in shape.iter().enumerate() {
                    if i > 0 {
                        write!(f, "x")?;
                    }
                    write!(f, "{dim}")?;
                }
                write!(f, ">(")?;
                // Show first few elements for large tensors
                let max_show = 8;
                for (i, val) in data.iter().take(max_show).enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{val}")?;
                }
                if data.len() > max_show {
                    write!(f, ", ... ({} more)", data.len() - max_show)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl std::fmt::Display for Counterexample {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Counterexample found (VC #{}):", self.vc_id.0)?;

        if !self.assignments.is_empty() {
            writeln!(f, "  Input values:")?;
            for (name, value) in &self.assignments {
                writeln!(f, "    {name} = {value}")?;
            }
        }

        if let Some(trace) = &self.trace {
            writeln!(f, "  Execution trace:")?;
            for (i, step) in trace.iter().enumerate() {
                write!(f, "    Step {i}")?;
                if let Some(action) = &step.action {
                    write!(f, " ({action})")?;
                }
                writeln!(f, ":")?;
                for (var, val) in &step.state {
                    writeln!(f, "      {var} = {val}")?;
                }
            }
        }

        if !self.explanation.is_empty() {
            writeln!(f, "  Explanation: {}", self.explanation)?;
        }

        Ok(())
    }
}

impl std::fmt::Display for TraceStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(action) = &self.action {
            write!(f, "({action}) ")?;
        }
        let vars: Vec<String> = self.state.iter().map(|(k, v)| format!("{k}={v}")).collect();
        write!(f, "{}", vars.join(", "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    // ============================================
    // VcId tests
    // ============================================

    #[test]
    fn test_vc_id_equality() {
        let id1 = VcId(42);
        let id2 = VcId(42);
        let id3 = VcId(43);

        assert_eq!(id1, id2);
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_vc_id_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(VcId(1));
        set.insert(VcId(2));
        set.insert(VcId(1)); // duplicate

        assert_eq!(set.len(), 2);
    }

    // ============================================
    // VerificationCondition tests
    // ============================================

    #[test]
    fn test_verification_condition_creation() {
        let vc = VerificationCondition {
            id: VcId(1),
            name: "test_vc".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: None,
        };

        assert_eq!(vc.id, VcId(1));
        assert_eq!(vc.name, "test_vc");
        assert!(vc.preferred_backend.is_none());
    }

    #[test]
    fn test_verification_condition_with_backend_hint() {
        let vc = VerificationCondition {
            id: VcId(2),
            name: "smt_vc".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: Some(BackendHint::Smt),
        };

        assert_eq!(vc.preferred_backend, Some(BackendHint::Smt));
    }

    // ============================================
    // VcKind tests
    // ============================================

    #[test]
    fn test_vc_kind_predicate() {
        let kind = VcKind::Predicate(Predicate::t());
        assert!(matches!(kind, VcKind::Predicate(_)));
    }

    #[test]
    fn test_vc_kind_implies() {
        let kind = VcKind::Implies {
            antecedent: Predicate::t(),
            consequent: Predicate::f(),
        };
        assert!(matches!(kind, VcKind::Implies { .. }));
    }

    #[test]
    fn test_vc_kind_forall() {
        let kind = VcKind::Forall {
            vars: vec![BoundVar {
                name: "x".to_string(),
                ty: VcType::Int {
                    signed: true,
                    bits: 32,
                },
            }],
            body: Box::new(VcKind::Predicate(Predicate::t())),
        };
        assert!(matches!(kind, VcKind::Forall { .. }));
    }

    #[test]
    fn test_vc_kind_exists() {
        let kind = VcKind::Exists {
            vars: vec![BoundVar {
                name: "y".to_string(),
                ty: VcType::Bool,
            }],
            body: Box::new(VcKind::Predicate(Predicate::t())),
        };
        assert!(matches!(kind, VcKind::Exists { .. }));
    }

    #[test]
    fn test_vc_kind_temporal() {
        let kind = VcKind::Temporal(TemporalFormula::State(Predicate::t()));
        assert!(matches!(kind, VcKind::Temporal(_)));
    }

    #[test]
    fn test_vc_kind_neural_network() {
        let kind = VcKind::NeuralNetwork(NnSpec::LocalRobustness(nn::RobustnessSpec {
            input: Expr::var("x"),
            epsilon: 0.01,
            norm: nn::Norm::Linf,
            property: nn::RobustnessProperty::ClassificationInvariant,
        }));
        assert!(matches!(kind, VcKind::NeuralNetwork(_)));
    }

    #[test]
    fn test_vc_kind_termination() {
        let kind = VcKind::Termination {
            decreases: Expr::var("n"),
            recursive_calls: vec![Expr::var("n").sub(Expr::int(1))],
        };
        assert!(matches!(kind, VcKind::Termination { .. }));
    }

    #[test]
    fn test_vc_kind_separation() {
        let kind = VcKind::Separation(SeparationAssertion::emp());
        assert!(matches!(kind, VcKind::Separation(_)));
    }

    // ============================================
    // BackendHint tests
    // ============================================

    #[test]
    fn test_backend_hints() {
        assert_eq!(BackendHint::Smt, BackendHint::Smt);
        assert_ne!(BackendHint::Smt, BackendHint::TheoremProver);

        // Test all variants exist
        let _smt = BackendHint::Smt;
        let _bmc = BackendHint::BoundedModelCheck;
        let _tl = BackendHint::TemporalLogic;
        let _tp = BackendHint::TheoremProver;
        let _sep = BackendHint::SeparationLogic;
        let _nn = BackendHint::NeuralNetwork;
        let _pt = BackendHint::PropertyTest;
    }

    // ============================================
    // SourceSpan tests
    // ============================================

    #[test]
    fn test_source_span() {
        let span = SourceSpan {
            file: Arc::from("src/lib.rs"),
            line_start: 10,
            line_end: 15,
            col_start: 4,
            col_end: 20,
        };

        assert_eq!(&*span.file, "src/lib.rs");
        assert_eq!(span.line_start, 10);
        assert_eq!(span.line_end, 15);
    }

    // ============================================
    // BoundVar tests
    // ============================================

    #[test]
    fn test_bound_var() {
        let var = BoundVar {
            name: "x".to_string(),
            ty: VcType::Int {
                signed: true,
                bits: 64,
            },
        };

        assert_eq!(var.name, "x");
        assert!(matches!(
            var.ty,
            VcType::Int {
                signed: true,
                bits: 64
            }
        ));
    }

    // ============================================
    // VcType tests
    // ============================================

    #[test]
    fn test_vc_type_bool() {
        let ty = VcType::Bool;
        assert!(matches!(ty, VcType::Bool));
    }

    #[test]
    fn test_vc_type_int() {
        let signed = VcType::Int {
            signed: true,
            bits: 32,
        };
        let unsigned = VcType::Int {
            signed: false,
            bits: 64,
        };

        assert!(matches!(
            signed,
            VcType::Int {
                signed: true,
                bits: 32
            }
        ));
        assert!(matches!(
            unsigned,
            VcType::Int {
                signed: false,
                bits: 64
            }
        ));
    }

    #[test]
    fn test_vc_type_float() {
        let f32 = VcType::Float { bits: 32 };
        let f64 = VcType::Float { bits: 64 };

        assert!(matches!(f32, VcType::Float { bits: 32 }));
        assert!(matches!(f64, VcType::Float { bits: 64 }));
    }

    #[test]
    fn test_vc_type_bitvec() {
        let bv = VcType::BitVec { bits: 256 };
        assert!(matches!(bv, VcType::BitVec { bits: 256 }));
    }

    #[test]
    fn test_vc_type_array() {
        let arr = VcType::Array {
            elem: Box::new(VcType::Int {
                signed: true,
                bits: 32,
            }),
            len: Some(10),
        };
        assert!(matches!(arr, VcType::Array { len: Some(10), .. }));

        let dynamic = VcType::Array {
            elem: Box::new(VcType::Bool),
            len: None,
        };
        assert!(matches!(dynamic, VcType::Array { len: None, .. }));
    }

    #[test]
    fn test_vc_type_tuple() {
        let tuple = VcType::Tuple(vec![
            VcType::Bool,
            VcType::Int {
                signed: true,
                bits: 32,
            },
        ]);

        if let VcType::Tuple(elems) = tuple {
            assert_eq!(elems.len(), 2);
        } else {
            panic!("Expected Tuple");
        }
    }

    #[test]
    fn test_vc_type_struct() {
        let s = VcType::Struct {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), VcType::Float { bits: 64 }),
                ("y".to_string(), VcType::Float { bits: 64 }),
            ],
        };

        match s {
            VcType::Struct { name, fields } => {
                assert_eq!(name, "Point");
                assert_eq!(fields.len(), 2);
            }
            _ => panic!("Expected Struct"),
        }
    }

    #[test]
    fn test_vc_type_ref() {
        let immut = VcType::Ref {
            mutable: false,
            inner: Box::new(VcType::Int {
                signed: true,
                bits: 32,
            }),
        };

        let mut_ = VcType::Ref {
            mutable: true,
            inner: Box::new(VcType::Bool),
        };

        assert!(matches!(immut, VcType::Ref { mutable: false, .. }));
        assert!(matches!(mut_, VcType::Ref { mutable: true, .. }));
    }

    #[test]
    fn test_vc_type_tensor() {
        let tensor = VcType::Tensor {
            elem: Box::new(VcType::Float { bits: 32 }),
            shape: vec![3, 224, 224],
        };

        match tensor {
            VcType::Tensor { shape, .. } => {
                assert_eq!(shape, vec![3, 224, 224]);
            }
            _ => panic!("Expected Tensor"),
        }
    }

    #[test]
    fn test_vc_type_abstract() {
        let abs = VcType::Abstract("MyOpaqueType".to_string());
        match abs {
            VcType::Abstract(name) => assert_eq!(name, "MyOpaqueType"),
            _ => panic!("Expected Abstract"),
        }
    }

    // ============================================
    // FunctionVcs tests
    // ============================================

    #[test]
    fn test_function_vcs() {
        let fvcs = FunctionVcs {
            name: "my_function".to_string(),
            signature: FunctionSignature {
                name: "my_function".to_string(),
                params: vec![(
                    "x".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                )],
                return_type: VcType::Int {
                    signed: true,
                    bits: 32,
                },
            },
            requires: vec![],
            ensures: vec![],
            loop_invariants: vec![],
            assertions: vec![],
            termination: None,
        };

        assert_eq!(fvcs.name, "my_function");
        assert_eq!(fvcs.signature.params.len(), 1);
    }

    // ============================================
    // Value tests
    // ============================================

    #[test]
    fn test_value_bool() {
        let v = Value::Bool(true);
        assert!(matches!(v, Value::Bool(true)));
    }

    #[test]
    fn test_value_int() {
        let v = Value::Int(42);
        assert!(matches!(v, Value::Int(42)));

        let big = Value::Int(i128::MAX);
        assert!(matches!(big, Value::Int(i128::MAX)));
    }

    #[test]
    fn test_value_float() {
        let v = Value::Float(1.234_567);
        if let Value::Float(f) = v {
            assert!((f - 1.234_567).abs() < 0.0001);
        }
    }

    #[test]
    fn test_value_array() {
        let v = Value::Array(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);

        if let Value::Array(elems) = v {
            assert_eq!(elems.len(), 3);
        }
    }

    #[test]
    fn test_value_tuple() {
        let v = Value::Tuple(vec![Value::Bool(true), Value::Int(10)]);

        if let Value::Tuple(elems) = v {
            assert_eq!(elems.len(), 2);
        }
    }

    #[test]
    fn test_value_struct() {
        let v = Value::Struct {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), Value::Float(1.0)),
                ("y".to_string(), Value::Float(2.0)),
            ],
        };

        match v {
            Value::Struct { name, fields } => {
                assert_eq!(name, "Point");
                assert_eq!(fields.len(), 2);
            }
            _ => panic!("Expected Struct"),
        }
    }

    #[test]
    fn test_value_tensor() {
        let v = Value::Tensor {
            shape: vec![2, 2],
            data: vec![1.0, 2.0, 3.0, 4.0],
        };

        match v {
            Value::Tensor { shape, data } => {
                assert_eq!(shape, vec![2, 2]);
                assert_eq!(data.len(), 4);
            }
            _ => panic!("Expected Tensor"),
        }
    }

    // ============================================
    // Counterexample tests
    // ============================================

    #[test]
    fn test_counterexample() {
        let cex = Counterexample {
            vc_id: VcId(1),
            assignments: vec![("x".to_string(), Value::Int(-5))],
            trace: None,
            explanation: "x must be positive".to_string(),
        };

        assert_eq!(cex.vc_id, VcId(1));
        assert_eq!(cex.assignments.len(), 1);
        assert!(cex.trace.is_none());
    }

    #[test]
    fn test_counterexample_with_trace() {
        let cex = Counterexample {
            vc_id: VcId(2),
            assignments: vec![],
            trace: Some(vec![
                TraceStep {
                    location: SourceSpan::default(),
                    state: vec![("x".to_string(), Value::Int(0))],
                    action: Some("initial".to_string()),
                },
                TraceStep {
                    location: SourceSpan::default(),
                    state: vec![("x".to_string(), Value::Int(1))],
                    action: Some("step".to_string()),
                },
            ]),
            explanation: "deadlock detected".to_string(),
        };

        assert_eq!(cex.trace.as_ref().unwrap().len(), 2);
    }

    // ============================================
    // Display implementation tests (N4.1)
    // ============================================

    #[test]
    fn test_value_display_bool() {
        assert_eq!(format!("{}", Value::Bool(true)), "true");
        assert_eq!(format!("{}", Value::Bool(false)), "false");
    }

    #[test]
    fn test_value_display_int() {
        assert_eq!(format!("{}", Value::Int(42)), "42");
        assert_eq!(format!("{}", Value::Int(-100)), "-100");
        assert_eq!(format!("{}", Value::Int(0)), "0");
    }

    #[test]
    fn test_value_display_float() {
        assert_eq!(format!("{}", Value::Float(2.75)), "2.75");
        assert_eq!(format!("{}", Value::Float(-0.5)), "-0.5");
        assert_eq!(format!("{}", Value::Float(f64::NAN)), "NaN");
        assert_eq!(format!("{}", Value::Float(f64::INFINITY)), "+Inf");
        assert_eq!(format!("{}", Value::Float(f64::NEG_INFINITY)), "-Inf");
    }

    #[test]
    fn test_value_display_bitvec() {
        let bv = Value::BitVec {
            bits: 8,
            value: vec![0xAB],
        };
        assert_eq!(format!("{}", bv), "0xab (bv8)");

        let bv32 = Value::BitVec {
            bits: 32,
            value: vec![0x12, 0x34, 0x56, 0x78],
        };
        assert_eq!(format!("{}", bv32), "0x78563412 (bv32)");
    }

    #[test]
    fn test_value_display_array() {
        let arr = Value::Array(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        assert_eq!(format!("{}", arr), "[1, 2, 3]");

        let empty = Value::Array(vec![]);
        assert_eq!(format!("{}", empty), "[]");
    }

    #[test]
    fn test_value_display_tuple() {
        let tup = Value::Tuple(vec![Value::Int(1), Value::Bool(true)]);
        assert_eq!(format!("{}", tup), "(1, true)");

        let single = Value::Tuple(vec![Value::Int(42)]);
        assert_eq!(format!("{}", single), "(42)");
    }

    #[test]
    fn test_value_display_struct() {
        let s = Value::Struct {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), Value::Int(10)),
                ("y".to_string(), Value::Int(20)),
            ],
        };
        assert_eq!(format!("{}", s), "Point { x: 10, y: 20 }");
    }

    #[test]
    fn test_value_display_tensor() {
        let tensor = Value::Tensor {
            shape: vec![2, 2],
            data: vec![1.0, 2.0, 3.0, 4.0],
        };
        assert_eq!(format!("{}", tensor), "Tensor<2x2>(1, 2, 3, 4)");

        // Large tensor should truncate
        let large = Value::Tensor {
            shape: vec![10],
            data: (0..10).map(|i| i as f64).collect(),
        };
        let display = format!("{}", large);
        assert!(display.contains("... (2 more)"));
    }

    #[test]
    fn test_counterexample_display_simple() {
        let cex = Counterexample {
            vc_id: VcId(42),
            assignments: vec![
                ("x".to_string(), Value::Int(5)),
                ("y".to_string(), Value::Int(-3)),
            ],
            trace: None,
            explanation: "x + y must be positive".to_string(),
        };

        let display = format!("{}", cex);
        assert!(display.contains("Counterexample found (VC #42):"));
        assert!(display.contains("x = 5"));
        assert!(display.contains("y = -3"));
        assert!(display.contains("x + y must be positive"));
    }

    #[test]
    fn test_counterexample_display_with_trace() {
        let cex = Counterexample {
            vc_id: VcId(1),
            assignments: vec![("n".to_string(), Value::Int(10))],
            trace: Some(vec![
                TraceStep {
                    location: SourceSpan::default(),
                    state: vec![("i".to_string(), Value::Int(0))],
                    action: Some("init".to_string()),
                },
                TraceStep {
                    location: SourceSpan::default(),
                    state: vec![("i".to_string(), Value::Int(1))],
                    action: Some("increment".to_string()),
                },
            ]),
            explanation: "loop invariant violated".to_string(),
        };

        let display = format!("{}", cex);
        assert!(display.contains("Execution trace:"));
        assert!(display.contains("Step 0 (init):"));
        assert!(display.contains("Step 1 (increment):"));
        assert!(display.contains("i = 0"));
        assert!(display.contains("i = 1"));
    }

    #[test]
    fn test_trace_step_display() {
        let step = TraceStep {
            location: SourceSpan::default(),
            state: vec![
                ("x".to_string(), Value::Int(1)),
                ("y".to_string(), Value::Int(2)),
            ],
            action: Some("step".to_string()),
        };
        assert_eq!(format!("{}", step), "(step) x=1, y=2");

        let step_no_action = TraceStep {
            location: SourceSpan::default(),
            state: vec![("z".to_string(), Value::Bool(true))],
            action: None,
        };
        assert_eq!(format!("{}", step_no_action), "z=true");
    }

    // ============================================
    // VerifyResult tests
    // ============================================

    #[test]
    fn test_verify_result_proven() {
        let result = VerifyResult::Proven;
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_verify_result_counterexample() {
        let cex = Counterexample {
            vc_id: VcId(1),
            assignments: vec![],
            trace: None,
            explanation: "failed".to_string(),
        };
        let result = VerifyResult::Counterexample(cex);
        assert!(matches!(result, VerifyResult::Counterexample(_)));
    }

    #[test]
    fn test_verify_result_timeout() {
        let result = VerifyResult::Timeout {
            partial_results: vec![(VcId(1), VerifyResult::Proven)],
        };
        assert!(matches!(result, VerifyResult::Timeout { .. }));
    }

    #[test]
    fn test_verify_result_unknown() {
        let result = VerifyResult::Unknown {
            reason: "solver returned unknown".to_string(),
        };
        assert!(matches!(result, VerifyResult::Unknown { .. }));
    }

    // ============================================
    // Serialization tests
    // ============================================

    #[test]
    fn test_vc_serialization() {
        let vc = VerificationCondition {
            id: VcId(100),
            name: "serialize_test".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: Some(BackendHint::Smt),
        };

        let json = serde_json::to_string(&vc).expect("serialize");
        let parsed: VerificationCondition = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(parsed.id, VcId(100));
        assert_eq!(parsed.name, "serialize_test");
    }

    #[test]
    fn test_value_serialization() {
        let val = Value::Struct {
            name: "Test".to_string(),
            fields: vec![
                ("a".to_string(), Value::Int(1)),
                ("b".to_string(), Value::Bool(true)),
            ],
        };

        let json = serde_json::to_string(&val).expect("serialize");
        let parsed: Value = serde_json::from_str(&json).expect("deserialize");

        assert!(matches!(parsed, Value::Struct { .. }));
    }

    // ============================================
    // TrustLevel tests
    // ============================================

    #[test]
    fn test_trust_level_default() {
        let level = TrustLevel::default();
        assert_eq!(level, TrustLevel::Assumed);
    }

    #[test]
    fn test_trust_level_from_str() {
        assert_eq!(TrustLevel::from_str("verified"), Some(TrustLevel::Verified));
        assert_eq!(TrustLevel::from_str("VERIFIED"), Some(TrustLevel::Verified));
        assert_eq!(TrustLevel::from_str("assumed"), Some(TrustLevel::Assumed));
        assert_eq!(TrustLevel::from_str("audited"), Some(TrustLevel::Audited));
        assert_eq!(
            TrustLevel::from_str("verified_warn"),
            Some(TrustLevel::VerifiedWarn)
        );
        assert_eq!(
            TrustLevel::from_str("verified-warn"),
            Some(TrustLevel::VerifiedWarn)
        );
        assert_eq!(TrustLevel::from_str("invalid"), None);
    }

    #[test]
    fn test_trust_level_requires_verification() {
        assert!(TrustLevel::Verified.requires_verification());
        assert!(TrustLevel::VerifiedWarn.requires_verification());
        assert!(!TrustLevel::Assumed.requires_verification());
        assert!(!TrustLevel::Audited.requires_verification());
    }

    #[test]
    fn test_trust_level_failures_are_errors() {
        assert!(TrustLevel::Verified.failures_are_errors());
        assert!(!TrustLevel::VerifiedWarn.failures_are_errors());
        assert!(!TrustLevel::Assumed.failures_are_errors());
        assert!(!TrustLevel::Audited.failures_are_errors());
    }

    #[test]
    fn test_trust_level_as_str() {
        assert_eq!(TrustLevel::Verified.as_str(), "verified");
        assert_eq!(TrustLevel::Assumed.as_str(), "assumed");
        assert_eq!(TrustLevel::Audited.as_str(), "audited");
        assert_eq!(TrustLevel::VerifiedWarn.as_str(), "verified_warn");
    }

    #[test]
    fn test_trust_level_serialization() {
        let level = TrustLevel::Verified;
        let json = serde_json::to_string(&level).expect("serialize");
        let parsed: TrustLevel = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed, TrustLevel::Verified);
    }

    #[test]
    fn test_trust_level_equality() {
        assert_eq!(TrustLevel::Verified, TrustLevel::Verified);
        assert_ne!(TrustLevel::Verified, TrustLevel::Assumed);
    }

    #[test]
    fn test_trust_level_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(TrustLevel::Verified);
        set.insert(TrustLevel::Assumed);
        set.insert(TrustLevel::Verified); // duplicate
        assert_eq!(set.len(), 2);
    }
}
