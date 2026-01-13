//! Verification Backend Interface
//!
//! This module defines the trait that all proof backends must implement.
//! Each backend (Z4, Kani, TLA, Lean5, CROWN, etc.) provides an implementation.

use crate::{BackendHint, Counterexample, Predicate, VcKind, VerificationCondition, VerifyResult};

/// The main trait for verification backends
pub trait ProofBackend: Send + Sync {
    /// Backend name for logging and error messages
    fn name(&self) -> &'static str;

    /// What kinds of VCs can this backend handle?
    fn capabilities(&self) -> BackendCapabilities;

    /// Check a verification condition
    fn check(&self, vc: &VerificationCondition, config: &VerifyConfig) -> VerifyResult;

    /// Check multiple VCs (allows backend to batch/parallelize)
    fn check_batch(
        &self,
        vcs: &[VerificationCondition],
        config: &VerifyConfig,
    ) -> Vec<(usize, VerifyResult)> {
        // Default implementation: check sequentially
        vcs.iter()
            .enumerate()
            .map(|(i, vc)| (i, self.check(vc, config)))
            .collect()
    }

    /// Generate a counterexample if the VC is invalid
    fn counterexample(&self, vc: &VerificationCondition) -> Option<Counterexample>;

    /// Reset internal state (for incremental solving)
    fn reset(&mut self);

    /// Push a context (for incremental solving)
    fn push(&mut self) {}

    /// Pop a context (for incremental solving)
    fn pop(&mut self) {}

    /// Add an assumption that holds for subsequent checks
    fn assume(&mut self, pred: &Predicate);
}

/// Capabilities of a verification backend
#[derive(Debug, Clone, Default)]
pub struct BackendCapabilities {
    /// Can handle basic predicates (SMT-level)
    pub predicates: bool,
    /// Can handle quantifiers
    pub quantifiers: bool,
    /// Supported theories
    pub theories: Vec<Theory>,
    /// Can handle temporal logic
    pub temporal: bool,
    /// Can handle separation logic
    pub separation: bool,
    /// Can handle neural network specs
    pub neural_network: bool,
    /// Can do bounded model checking
    pub bounded_model_check: bool,
    /// Can do inductive proofs
    pub induction: bool,
    /// Supports incremental solving
    pub incremental: bool,
    /// Can produce counterexamples
    pub counterexamples: bool,
    /// Can produce proofs/certificates
    pub proof_production: bool,
}

/// SMT theories
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Theory {
    /// Core (boolean logic)
    Core,
    /// Linear integer arithmetic
    LIA,
    /// Linear real arithmetic
    LRA,
    /// Nonlinear integer arithmetic
    NIA,
    /// Nonlinear real arithmetic
    NRA,
    /// Bitvectors
    BV,
    /// Arrays
    Arrays,
    /// Uninterpreted functions
    UF,
    /// Floating point
    FP,
    /// Strings
    Strings,
    /// Sequences
    Sequences,
    /// Datatypes (algebraic)
    Datatypes,
}

/// Configuration for verification
#[derive(Debug, Clone)]
pub struct VerifyConfig {
    /// Timeout per VC in milliseconds
    pub timeout_ms: u64,
    /// Memory limit in MB
    pub memory_limit_mb: usize,
    /// For bounded model checking: max depth
    pub bmc_depth: usize,
    /// Produce counterexamples
    pub produce_counterexamples: bool,
    /// Produce proof certificates
    pub produce_proofs: bool,
    /// Number of parallel workers
    pub parallelism: usize,
    /// Random seed for reproducibility
    pub seed: Option<u64>,
}

impl Default for VerifyConfig {
    fn default() -> Self {
        Self {
            timeout_ms: 30_000,    // 30 seconds
            memory_limit_mb: 4096, // 4GB
            bmc_depth: 100,
            produce_counterexamples: true,
            produce_proofs: false,
            parallelism: num_cpus::get(),
            seed: None,
        }
    }
}

/// Registry of all available backends
pub struct BackendRegistry {
    backends: Vec<Box<dyn ProofBackend>>,
}

impl Default for BackendRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl BackendRegistry {
    #[must_use]
    pub fn new() -> Self {
        Self { backends: vec![] }
    }

    pub fn register(&mut self, backend: Box<dyn ProofBackend>) {
        self.backends.push(backend);
    }

    /// Find the best backend for a given VC
    #[must_use]
    pub fn select_backend(&self, vc: &VerificationCondition) -> Option<&dyn ProofBackend> {
        // If there's a hint, try that first
        if let Some(hint) = &vc.preferred_backend {
            for backend in &self.backends {
                if matches_hint(backend.as_ref(), *hint)
                    && can_handle(backend.as_ref(), &vc.condition)
                {
                    return Some(backend.as_ref());
                }
            }
        }

        // Otherwise find any capable backend
        for backend in &self.backends {
            if can_handle(backend.as_ref(), &vc.condition) {
                return Some(backend.as_ref());
            }
        }

        None
    }

    /// Check a VC using the appropriate backend
    #[must_use]
    pub fn check(&self, vc: &VerificationCondition, config: &VerifyConfig) -> VerifyResult {
        match self.select_backend(vc) {
            Some(backend) => backend.check(vc, config),
            None => VerifyResult::Error(crate::VerifyError::NoBackend {
                vc_kind: format!("{:?}", vc.condition),
            }),
        }
    }
}

fn matches_hint(backend: &dyn ProofBackend, hint: BackendHint) -> bool {
    match hint {
        BackendHint::Smt => backend.name().contains("z4") || backend.name().contains("smt"),
        BackendHint::BoundedModelCheck => {
            backend.name().contains("kani") || backend.name().contains("bmc")
        }
        BackendHint::TemporalLogic => backend.name().contains("tla"),
        BackendHint::TheoremProver => backend.name().contains("lean"),
        BackendHint::SeparationLogic => {
            backend.name().contains("prusti") || backend.name().contains("sep")
        }
        BackendHint::NeuralNetwork => {
            backend.name().contains("crown") || backend.name().contains("nn")
        }
        BackendHint::PropertyTest => backend.name().contains("proptest"),
    }
}

fn can_handle(backend: &dyn ProofBackend, kind: &VcKind) -> bool {
    let caps = backend.capabilities();
    match kind {
        VcKind::Predicate(_) | VcKind::Implies { .. } => caps.predicates,
        VcKind::Forall { .. } | VcKind::Exists { .. } => caps.quantifiers,
        VcKind::Temporal(_) => caps.temporal,
        VcKind::NeuralNetwork(_) => caps.neural_network,
        VcKind::Termination { .. } => caps.induction,
        VcKind::Separation(_) => caps.separation,
    }
}

/// Trait for backends that support incremental solving
pub trait IncrementalBackend: ProofBackend {
    /// Assert a formula permanently
    fn assert(&mut self, pred: &Predicate);

    /// Check satisfiability under current assertions
    fn check_sat(&mut self) -> SatResult;

    /// Get model (if sat)
    fn get_model(&self) -> Option<Model>;
}

/// Satisfiability result
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SatResult {
    Sat,
    Unsat,
    Unknown,
}

/// A model (satisfying assignment)
#[derive(Debug, Clone)]
pub struct Model {
    pub assignments: Vec<(String, crate::Value)>,
}

/// Trait for backends that produce proof certificates
pub trait CertifyingBackend: ProofBackend {
    /// Get a proof certificate for a proven VC
    fn get_certificate(&self, vc: &VerificationCondition) -> Option<ProofCertificate>;

    /// Verify a proof certificate
    fn verify_certificate(&self, cert: &ProofCertificate) -> bool;
}

/// A proof certificate that can be independently verified
#[derive(Debug, Clone)]
pub struct ProofCertificate {
    /// The VC that was proven
    pub vc_id: crate::VcId,
    /// The proof in some format
    pub proof: ProofFormat,
    /// Backend that produced this proof
    pub backend: String,
}

/// Proof formats
#[derive(Debug, Clone)]
pub enum ProofFormat {
    /// SMT-LIB proof
    SmtLib(String),
    /// Lean proof term
    Lean(String),
    /// Coq proof term
    Coq(String),
    /// Custom format
    Custom { format: String, data: Vec<u8> },
}

// Placeholder for num_cpus (would be a dependency)
mod num_cpus {
    pub fn get() -> usize {
        std::thread::available_parallelism()
            .map(std::num::NonZero::get)
            .unwrap_or(4)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SourceSpan, VcId};

    // Test BackendCapabilities default
    #[test]
    fn test_backend_capabilities_default() {
        let caps = BackendCapabilities::default();
        assert!(!caps.predicates);
        assert!(!caps.quantifiers);
        assert!(caps.theories.is_empty());
        assert!(!caps.temporal);
        assert!(!caps.separation);
        assert!(!caps.neural_network);
        assert!(!caps.bounded_model_check);
        assert!(!caps.induction);
        assert!(!caps.incremental);
        assert!(!caps.counterexamples);
        assert!(!caps.proof_production);
    }

    // Test VerifyConfig default values
    #[test]
    fn test_verify_config_default() {
        let config = VerifyConfig::default();
        assert_eq!(config.timeout_ms, 30_000);
        assert_eq!(config.memory_limit_mb, 4096);
        assert_eq!(config.bmc_depth, 100);
        assert!(config.produce_counterexamples);
        assert!(!config.produce_proofs);
        assert!(config.parallelism > 0);
        assert!(config.seed.is_none());
    }

    // Test BackendRegistry creation and empty state
    #[test]
    fn test_backend_registry_new() {
        let registry = BackendRegistry::new();
        // Empty registry should not find any backend
        let vc = VerificationCondition {
            id: VcId(0),
            name: "test".to_string(),
            span: SourceSpan {
                file: "test.rs".into(),
                line_start: 1,
                line_end: 1,
                col_start: 1,
                col_end: 10,
            },
            condition: VcKind::Predicate(Predicate::Bool(true)),
            preferred_backend: None,
        };
        assert!(registry.select_backend(&vc).is_none());
    }

    // Test BackendRegistry default impl
    #[test]
    fn test_backend_registry_default() {
        let registry = BackendRegistry::default();
        let vc = VerificationCondition {
            id: VcId(0),
            name: "test".to_string(),
            span: SourceSpan {
                file: "test.rs".into(),
                line_start: 1,
                line_end: 1,
                col_start: 1,
                col_end: 10,
            },
            condition: VcKind::Predicate(Predicate::Bool(true)),
            preferred_backend: None,
        };
        // Should return NoBackend error
        let result = registry.check(&vc, &VerifyConfig::default());
        assert!(matches!(
            result,
            VerifyResult::Error(crate::VerifyError::NoBackend { .. })
        ));
    }

    // Test Theory enum values
    #[test]
    fn test_theory_values() {
        // Verify all Theory variants exist and have correct debug output
        let theories = vec![
            Theory::Core,
            Theory::LIA,
            Theory::LRA,
            Theory::NIA,
            Theory::NRA,
            Theory::BV,
            Theory::Arrays,
            Theory::UF,
            Theory::FP,
            Theory::Strings,
            Theory::Sequences,
            Theory::Datatypes,
        ];
        assert_eq!(theories.len(), 12);
        // Test Clone and Copy
        let t = Theory::LIA;
        let t2 = t;
        assert_eq!(t, t2);
    }

    // Test SatResult enum
    #[test]
    fn test_sat_result_values() {
        let sat = SatResult::Sat;
        let unsat = SatResult::Unsat;
        let unknown = SatResult::Unknown;
        // Test equality
        assert_eq!(sat, SatResult::Sat);
        assert_eq!(unsat, SatResult::Unsat);
        assert_eq!(unknown, SatResult::Unknown);
        // Test Clone and Copy
        let sat2 = sat;
        assert_eq!(sat, sat2);
    }

    // Test Model creation
    #[test]
    fn test_model_creation() {
        let model = Model {
            assignments: vec![
                ("x".to_string(), crate::Value::Int(42)),
                ("y".to_string(), crate::Value::Bool(true)),
            ],
        };
        assert_eq!(model.assignments.len(), 2);
        assert_eq!(model.assignments[0].0, "x");
    }

    // Test ProofCertificate creation
    #[test]
    fn test_proof_certificate() {
        let cert = ProofCertificate {
            vc_id: VcId(123),
            proof: ProofFormat::SmtLib("(proof ...)".to_string()),
            backend: "z4".to_string(),
        };
        assert_eq!(cert.vc_id.0, 123);
        assert_eq!(cert.backend, "z4");
    }

    // Test ProofFormat variants
    #[test]
    fn test_proof_format_variants() {
        let smt = ProofFormat::SmtLib("(proof)".to_string());
        let lean = ProofFormat::Lean("theorem".to_string());
        let coq = ProofFormat::Coq("Proof.".to_string());
        let custom = ProofFormat::Custom {
            format: "binary".to_string(),
            data: vec![1, 2, 3],
        };

        // Test Debug
        assert!(format!("{smt:?}").contains("SmtLib"));
        assert!(format!("{lean:?}").contains("Lean"));
        assert!(format!("{coq:?}").contains("Coq"));
        assert!(format!("{custom:?}").contains("Custom"));
    }

    // Mock backend for testing
    struct MockBackend {
        name: &'static str,
        caps: BackendCapabilities,
    }

    impl ProofBackend for MockBackend {
        fn name(&self) -> &'static str {
            self.name
        }
        fn capabilities(&self) -> BackendCapabilities {
            self.caps.clone()
        }
        fn check(&self, _vc: &VerificationCondition, _config: &VerifyConfig) -> VerifyResult {
            VerifyResult::Proven
        }
        fn counterexample(&self, _vc: &VerificationCondition) -> Option<Counterexample> {
            None
        }
        fn reset(&mut self) {}
        fn assume(&mut self, _pred: &Predicate) {}
    }

    // Test matches_hint function
    #[test]
    fn test_matches_hint_smt() {
        let z4 = MockBackend {
            name: "z4-solver",
            caps: BackendCapabilities::default(),
        };
        let smt = MockBackend {
            name: "smt-backend",
            caps: BackendCapabilities::default(),
        };
        let kani = MockBackend {
            name: "kani-bmc",
            caps: BackendCapabilities::default(),
        };

        assert!(matches_hint(&z4, BackendHint::Smt));
        assert!(matches_hint(&smt, BackendHint::Smt));
        assert!(!matches_hint(&kani, BackendHint::Smt));
    }

    #[test]
    fn test_matches_hint_bmc() {
        let kani = MockBackend {
            name: "kani-bmc",
            caps: BackendCapabilities::default(),
        };
        let bmc = MockBackend {
            name: "bmc-checker",
            caps: BackendCapabilities::default(),
        };

        assert!(matches_hint(&kani, BackendHint::BoundedModelCheck));
        assert!(matches_hint(&bmc, BackendHint::BoundedModelCheck));
    }

    #[test]
    fn test_matches_hint_temporal() {
        let tla = MockBackend {
            name: "tla-checker",
            caps: BackendCapabilities::default(),
        };
        assert!(matches_hint(&tla, BackendHint::TemporalLogic));
    }

    #[test]
    fn test_matches_hint_theorem_prover() {
        let lean = MockBackend {
            name: "lean-prover",
            caps: BackendCapabilities::default(),
        };
        assert!(matches_hint(&lean, BackendHint::TheoremProver));
    }

    #[test]
    fn test_matches_hint_separation() {
        let prusti = MockBackend {
            name: "prusti-verifier",
            caps: BackendCapabilities::default(),
        };
        let sep = MockBackend {
            name: "sep-logic",
            caps: BackendCapabilities::default(),
        };
        assert!(matches_hint(&prusti, BackendHint::SeparationLogic));
        assert!(matches_hint(&sep, BackendHint::SeparationLogic));
    }

    #[test]
    fn test_matches_hint_neural() {
        let crown = MockBackend {
            name: "crown-verifier",
            caps: BackendCapabilities::default(),
        };
        let nn = MockBackend {
            name: "nn-checker",
            caps: BackendCapabilities::default(),
        };
        assert!(matches_hint(&crown, BackendHint::NeuralNetwork));
        assert!(matches_hint(&nn, BackendHint::NeuralNetwork));
    }

    #[test]
    fn test_matches_hint_proptest() {
        let proptest = MockBackend {
            name: "proptest-runner",
            caps: BackendCapabilities::default(),
        };
        assert!(matches_hint(&proptest, BackendHint::PropertyTest));
    }

    // Test can_handle function
    #[test]
    fn test_can_handle_predicates() {
        let backend = MockBackend {
            name: "pred",
            caps: BackendCapabilities {
                predicates: true,
                ..Default::default()
            },
        };
        assert!(can_handle(
            &backend,
            &VcKind::Predicate(Predicate::Bool(true))
        ));
        assert!(can_handle(
            &backend,
            &VcKind::Implies {
                antecedent: Predicate::Bool(true),
                consequent: Predicate::Bool(false),
            }
        ));
        assert!(!can_handle(
            &backend,
            &VcKind::Forall {
                vars: vec![],
                body: Box::new(VcKind::Predicate(Predicate::Bool(true))),
            }
        ));
    }

    #[test]
    fn test_can_handle_quantifiers() {
        let backend = MockBackend {
            name: "quant",
            caps: BackendCapabilities {
                predicates: true,
                quantifiers: true,
                ..Default::default()
            },
        };
        assert!(can_handle(
            &backend,
            &VcKind::Forall {
                vars: vec![],
                body: Box::new(VcKind::Predicate(Predicate::Bool(true))),
            }
        ));
        assert!(can_handle(
            &backend,
            &VcKind::Exists {
                vars: vec![],
                body: Box::new(VcKind::Predicate(Predicate::Bool(true))),
            }
        ));
    }

    #[test]
    fn test_can_handle_temporal() {
        let backend = MockBackend {
            name: "temporal",
            caps: BackendCapabilities {
                temporal: true,
                ..Default::default()
            },
        };
        // Use TemporalFormula::state to create a simple temporal formula
        let temporal = crate::temporal::TemporalFormula::state(Predicate::Bool(true));
        assert!(can_handle(&backend, &VcKind::Temporal(temporal)));
        assert!(!can_handle(
            &backend,
            &VcKind::Predicate(Predicate::Bool(true))
        ));
    }

    #[test]
    fn test_can_handle_neural_network() {
        let backend = MockBackend {
            name: "nn",
            caps: BackendCapabilities {
                neural_network: true,
                ..Default::default()
            },
        };
        assert!(can_handle(
            &backend,
            &VcKind::NeuralNetwork(crate::nn::NnSpec::OutputBounds(crate::nn::BoundsSpec {
                input_region: crate::nn::InputRegion::Box {
                    lower: vec![0.0],
                    upper: vec![1.0],
                },
                lower_bounds: None,
                upper_bounds: None,
            }))
        ));
    }

    #[test]
    fn test_can_handle_termination() {
        let backend = MockBackend {
            name: "inductive",
            caps: BackendCapabilities {
                induction: true,
                ..Default::default()
            },
        };
        assert!(can_handle(
            &backend,
            &VcKind::Termination {
                decreases: crate::Expr::IntLit(0),
                recursive_calls: vec![],
            }
        ));
    }

    #[test]
    fn test_can_handle_separation() {
        let backend = MockBackend {
            name: "sep",
            caps: BackendCapabilities {
                separation: true,
                ..Default::default()
            },
        };
        assert!(can_handle(
            &backend,
            &VcKind::Separation(crate::SeparationAssertion::emp())
        ));
    }

    // Test BackendRegistry register and select
    #[test]
    fn test_backend_registry_register() {
        let mut registry = BackendRegistry::new();
        registry.register(Box::new(MockBackend {
            name: "test-smt",
            caps: BackendCapabilities {
                predicates: true,
                ..Default::default()
            },
        }));

        let vc = VerificationCondition {
            id: VcId(0),
            name: "test".to_string(),
            span: SourceSpan {
                file: "test.rs".into(),
                line_start: 1,
                line_end: 1,
                col_start: 1,
                col_end: 10,
            },
            condition: VcKind::Predicate(Predicate::Bool(true)),
            preferred_backend: None,
        };

        let selected = registry.select_backend(&vc);
        assert!(selected.is_some());
        assert_eq!(selected.unwrap().name(), "test-smt");
    }

    #[test]
    fn test_backend_registry_with_hint() {
        let mut registry = BackendRegistry::new();
        registry.register(Box::new(MockBackend {
            name: "other",
            caps: BackendCapabilities {
                predicates: true,
                ..Default::default()
            },
        }));
        registry.register(Box::new(MockBackend {
            name: "z4-smt",
            caps: BackendCapabilities {
                predicates: true,
                ..Default::default()
            },
        }));

        let vc_with_hint = VerificationCondition {
            id: VcId(0),
            name: "test".to_string(),
            span: SourceSpan {
                file: "test.rs".into(),
                line_start: 1,
                line_end: 1,
                col_start: 1,
                col_end: 10,
            },
            condition: VcKind::Predicate(Predicate::Bool(true)),
            preferred_backend: Some(BackendHint::Smt),
        };

        let selected = registry.select_backend(&vc_with_hint);
        assert!(selected.is_some());
        assert_eq!(selected.unwrap().name(), "z4-smt");
    }

    #[test]
    fn test_backend_registry_hint_fallback() {
        // Test that if hint doesn't match, we still find a capable backend
        let mut registry = BackendRegistry::new();
        registry.register(Box::new(MockBackend {
            name: "other",
            caps: BackendCapabilities {
                predicates: true,
                ..Default::default()
            },
        }));

        let vc_with_hint = VerificationCondition {
            id: VcId(0),
            name: "test".to_string(),
            span: SourceSpan {
                file: "test.rs".into(),
                line_start: 1,
                line_end: 1,
                col_start: 1,
                col_end: 10,
            },
            condition: VcKind::Predicate(Predicate::Bool(true)),
            preferred_backend: Some(BackendHint::Smt), // No SMT backend registered
        };

        let selected = registry.select_backend(&vc_with_hint);
        assert!(selected.is_some());
        assert_eq!(selected.unwrap().name(), "other");
    }

    // Test check_batch default implementation
    #[test]
    fn test_check_batch_default() {
        struct CountingBackend {
            call_count: std::sync::atomic::AtomicUsize,
        }
        impl ProofBackend for CountingBackend {
            fn name(&self) -> &'static str {
                "batch"
            }
            fn capabilities(&self) -> BackendCapabilities {
                BackendCapabilities {
                    predicates: true,
                    ..Default::default()
                }
            }
            fn check(&self, _vc: &VerificationCondition, _config: &VerifyConfig) -> VerifyResult {
                self.call_count
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                VerifyResult::Proven
            }
            fn counterexample(&self, _vc: &VerificationCondition) -> Option<Counterexample> {
                None
            }
            fn reset(&mut self) {}
            fn assume(&mut self, _pred: &Predicate) {}
        }

        let backend = CountingBackend {
            call_count: std::sync::atomic::AtomicUsize::new(0),
        };

        let vcs: Vec<VerificationCondition> = (0..3)
            .map(|i| VerificationCondition {
                id: VcId(i),
                name: format!("test_{i}"),
                span: SourceSpan {
                    file: "test.rs".into(),
                    line_start: 1,
                    line_end: 1,
                    col_start: 1,
                    col_end: 10,
                },
                condition: VcKind::Predicate(Predicate::Bool(true)),
                preferred_backend: None,
            })
            .collect();

        let results = backend.check_batch(&vcs, &VerifyConfig::default());
        assert_eq!(results.len(), 3);
        assert_eq!(
            backend.call_count.load(std::sync::atomic::Ordering::SeqCst),
            3
        );
        for (i, (idx, result)) in results.into_iter().enumerate() {
            assert_eq!(idx, i);
            assert!(matches!(result, VerifyResult::Proven));
        }
    }

    // Test num_cpus module
    #[test]
    fn test_num_cpus() {
        let cpus = num_cpus::get();
        assert!(cpus >= 1);
    }

    // Test BackendCapabilities clone
    #[test]
    fn test_backend_capabilities_clone() {
        let caps = BackendCapabilities {
            predicates: true,
            quantifiers: true,
            theories: vec![Theory::LIA, Theory::BV],
            temporal: true,
            separation: false,
            neural_network: true,
            bounded_model_check: false,
            induction: true,
            incremental: true,
            counterexamples: true,
            proof_production: false,
        };
        let cloned = caps.clone();
        assert_eq!(caps.predicates, cloned.predicates);
        assert_eq!(caps.theories.len(), cloned.theories.len());
    }

    // Test VerifyConfig clone
    #[test]
    fn test_verify_config_clone() {
        let config = VerifyConfig {
            timeout_ms: 5000,
            memory_limit_mb: 2048,
            bmc_depth: 50,
            produce_counterexamples: false,
            produce_proofs: true,
            parallelism: 8,
            seed: Some(42),
        };
        let cloned = config.clone();
        assert_eq!(config.timeout_ms, cloned.timeout_ms);
        assert_eq!(config.seed, cloned.seed);
    }
}
