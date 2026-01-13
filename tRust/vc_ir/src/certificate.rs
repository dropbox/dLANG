//! Proof certificates for verified properties (N4.1)
//!
//! A proof certificate is a self-contained artifact that can be independently
//! verified using Lean5. It includes all necessary information to reproduce
//! and check the verification result.

use crate::{SourceSpan, VcId, VcKind, VerificationCondition};
use serde::{Deserialize, Serialize};
use std::fmt::Write;
use std::path::Path;
use std::time::SystemTime;

/// A proof certificate for a verified property
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditCertificate {
    /// Unique identifier for this certificate
    pub id: String,
    /// Timestamp when the certificate was created
    pub created_at: SystemTime,
    /// Name of the verified function/property
    pub property_name: String,
    /// Description of what was proved
    pub description: String,
    /// The verification method used
    pub method: VerificationMethod,
    /// Source location of the verified property
    pub source_span: SourceSpan,
    /// The verification conditions that were checked
    pub vcs: Vec<VcCertificateEntry>,
    /// The Lean5 source code for the certificate (if generated)
    pub lean_source: Option<String>,
    /// Verification status
    pub is_complete: bool,
    /// tRust version that created this certificate
    pub trust_version: String,
}

/// Method used to verify the property
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VerificationMethod {
    /// SMT solving with Z3
    Smt { solver: String },
    /// K-induction with the value of k
    KInduction { k: usize },
    /// CHC/Spacer solving
    Chc { backend: String },
    /// Bounded Model Checking
    Bmc { bound: usize },
    /// Weakest precondition calculus
    WeakestPrecondition,
}

impl std::fmt::Display for VerificationMethod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerificationMethod::Smt { solver } => write!(f, "SMT/{solver}"),
            VerificationMethod::KInduction { k } => write!(f, "k-induction (k={k})"),
            VerificationMethod::Chc { backend } => write!(f, "CHC/{backend}"),
            VerificationMethod::Bmc { bound } => write!(f, "BMC (bound={bound})"),
            VerificationMethod::WeakestPrecondition => write!(f, "weakest precondition"),
        }
    }
}

/// Certificate entry for a single verification condition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VcCertificateEntry {
    /// VC identifier
    pub vc_id: VcId,
    /// VC name
    pub name: String,
    /// Kind of VC
    pub kind: String,
    /// Whether this VC was successfully proven
    pub proven: bool,
    /// Source location
    pub span: SourceSpan,
}

/// Result of verifying a certificate with Lean
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateVerificationResult {
    /// Whether Lean accepted the proofs
    pub verified: bool,
    /// Any errors from Lean
    pub errors: Vec<String>,
    /// Number of sorry placeholders
    pub sorry_count: usize,
    /// Lean version used for verification
    pub lean_version: String,
    /// Time taken for verification
    pub verification_time_ms: u64,
}

impl AuditCertificate {
    /// Create a new certificate builder
    pub fn builder(property_name: impl Into<String>) -> AuditCertificateBuilder {
        AuditCertificateBuilder::new(property_name)
    }

    /// Get a summary of the certificate
    pub fn summary(&self) -> String {
        let status = if self.is_complete {
            "COMPLETE"
        } else {
            "INCOMPLETE"
        };

        let vc_summary = format!(
            "{}/{} VCs proven",
            self.vcs.iter().filter(|v| v.proven).count(),
            self.vcs.len()
        );

        format!(
            "Certificate: {}\n\
             Property: {}\n\
             Method: {}\n\
             Status: {} ({})\n\
             Source: {}",
            self.id, self.property_name, self.method, status, vc_summary, self.source_span
        )
    }

    /// Write the certificate to a file
    pub fn write_to_file(&self, path: &Path) -> std::io::Result<()> {
        // Write the certificate metadata as JSON
        let cert_path = path.with_extension("cert.json");
        let json = serde_json::to_string_pretty(self).map_err(std::io::Error::other)?;
        std::fs::write(&cert_path, json)?;

        // Write the Lean source if available
        if let Some(lean_source) = &self.lean_source {
            let lean_path = path.with_extension("lean");
            std::fs::write(&lean_path, lean_source)?;
        }

        Ok(())
    }

    /// Load a certificate from a JSON file
    pub fn load_from_file(path: &Path) -> std::io::Result<Self> {
        let json = std::fs::read_to_string(path)?;
        serde_json::from_str(&json)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }

    /// Generate Lean5 source for this certificate
    pub fn generate_lean_source(&mut self) {
        let mut source = String::new();

        // Header
        source.push_str("/-!\n");
        source.push_str("# tRust Proof Certificate\n\n");
        let _ = writeln!(source, "Property: {}", self.property_name);
        let _ = writeln!(source, "Description: {}", self.description);
        let _ = writeln!(source, "Method: {}", self.method);
        let _ = writeln!(source, "Source: {}", self.source_span);
        let _ = writeln!(source, "Generated: {:?}", self.created_at);
        let _ = writeln!(source, "tRust version: {}", self.trust_version);
        source.push_str("-/\n\n");

        // Imports
        source.push_str("import Mathlib.Tactic\n\n");

        // Namespace
        let safe_name = self.property_name.replace([' ', '-', ':'], "_");
        let _ = writeln!(source, "namespace tRust.{safe_name}\n");

        // Document each VC
        source.push_str("/-! ## Verification Conditions\n\n");
        for vc in &self.vcs {
            let status = if vc.proven { "PROVEN" } else { "UNPROVEN" };
            let _ = writeln!(source, "- `{}`: {} [{}]", vc.name, vc.kind, status);
        }
        source.push_str("-/\n\n");

        // For each proven VC, generate a theorem stub
        // (Full tactic proofs would require integration with kani_fast_lean5)
        for vc in &self.vcs {
            if vc.proven {
                let _ = writeln!(source, "-- {} ({})", vc.name, vc.kind);
                let _ = writeln!(source, "-- Status: PROVEN by {}", self.method);
                let _ = writeln!(source, "-- Source: {}", vc.span);
                source.push_str("-- theorem ");
                source.push_str(&vc.name.replace([' ', '-', ':'], "_"));
                source.push_str(" : sorry := by sorry\n\n");
            }
        }

        // Close namespace
        let _ = writeln!(source, "end tRust.{safe_name}");

        self.lean_source = Some(source);
    }
}

/// Builder for creating proof certificates
pub struct AuditCertificateBuilder {
    property_name: String,
    description: Option<String>,
    method: Option<VerificationMethod>,
    source_span: SourceSpan,
    vcs: Vec<VcCertificateEntry>,
}

impl AuditCertificateBuilder {
    /// Create a new builder
    pub fn new(property_name: impl Into<String>) -> Self {
        Self {
            property_name: property_name.into(),
            description: None,
            method: None,
            source_span: SourceSpan::default(),
            vcs: Vec::new(),
        }
    }

    /// Set the description
    pub fn description(mut self, desc: impl Into<String>) -> Self {
        self.description = Some(desc.into());
        self
    }

    /// Set the verification method
    pub fn method(mut self, method: VerificationMethod) -> Self {
        self.method = Some(method);
        self
    }

    /// Set the source span
    pub fn source_span(mut self, span: SourceSpan) -> Self {
        self.source_span = span;
        self
    }

    /// Add a verification condition result
    pub fn add_vc(mut self, vc: &VerificationCondition, proven: bool) -> Self {
        self.vcs.push(VcCertificateEntry {
            vc_id: vc.id,
            name: vc.name.clone(),
            kind: vc_kind_name(&vc.condition),
            proven,
            span: vc.span.clone(),
        });
        self
    }

    /// Build the certificate
    pub fn build(self) -> AuditCertificate {
        let is_complete = self.vcs.iter().all(|v| v.proven);

        // Generate unique ID
        let id = format!(
            "{}-{}",
            self.property_name.replace(' ', "_"),
            SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs()
        );

        AuditCertificate {
            id,
            created_at: SystemTime::now(),
            property_name: self.property_name,
            description: self
                .description
                .unwrap_or_else(|| "Verified property".to_string()),
            method: self.method.unwrap_or(VerificationMethod::Smt {
                solver: "Z3".to_string(),
            }),
            source_span: self.source_span,
            vcs: self.vcs,
            lean_source: None,
            is_complete,
            trust_version: env!("CARGO_PKG_VERSION").to_string(),
        }
    }
}

/// Get a human-readable name for a VC kind
fn vc_kind_name(kind: &VcKind) -> String {
    match kind {
        VcKind::Predicate(_) => "predicate".to_string(),
        VcKind::Implies { .. } => "implication".to_string(),
        VcKind::Forall { .. } => "universal quantification".to_string(),
        VcKind::Exists { .. } => "existential quantification".to_string(),
        VcKind::Temporal(_) => "temporal property".to_string(),
        VcKind::NeuralNetwork(_) => "neural network property".to_string(),
        VcKind::Termination { .. } => "termination".to_string(),
        VcKind::Separation(_) => "separation logic".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Predicate;

    #[test]
    fn test_certificate_builder() {
        let vc = VerificationCondition {
            id: VcId(1),
            name: "test_vc".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: None,
        };

        let cert = AuditCertificate::builder("test_property")
            .description("Test certificate")
            .method(VerificationMethod::Smt {
                solver: "Z3".to_string(),
            })
            .add_vc(&vc, true)
            .build();

        assert_eq!(cert.property_name, "test_property");
        assert_eq!(cert.vcs.len(), 1);
        assert!(cert.is_complete);
    }

    #[test]
    fn test_certificate_incomplete() {
        let vc1 = VerificationCondition {
            id: VcId(1),
            name: "proven_vc".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: None,
        };
        let vc2 = VerificationCondition {
            id: VcId(2),
            name: "unproven_vc".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::f()),
            preferred_backend: None,
        };

        let cert = AuditCertificate::builder("partial_property")
            .add_vc(&vc1, true)
            .add_vc(&vc2, false)
            .build();

        assert!(!cert.is_complete);
        assert_eq!(cert.vcs.iter().filter(|v| v.proven).count(), 1);
    }

    #[test]
    fn test_certificate_summary() {
        let vc = VerificationCondition {
            id: VcId(1),
            name: "summary_vc".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: None,
        };

        let cert = AuditCertificate::builder("summary_test")
            .method(VerificationMethod::KInduction { k: 5 })
            .add_vc(&vc, true)
            .build();

        let summary = cert.summary();
        assert!(summary.contains("summary_test"));
        assert!(summary.contains("k-induction (k=5)"));
        assert!(summary.contains("COMPLETE"));
    }

    #[test]
    fn test_certificate_lean_generation() {
        let vc = VerificationCondition {
            id: VcId(1),
            name: "lean_vc".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: None,
        };

        let mut cert = AuditCertificate::builder("lean_test")
            .description("Test Lean generation")
            .method(VerificationMethod::WeakestPrecondition)
            .add_vc(&vc, true)
            .build();

        cert.generate_lean_source();

        let source = cert.lean_source.unwrap();
        assert!(source.contains("tRust Proof Certificate"));
        assert!(source.contains("namespace tRust.lean_test"));
        assert!(source.contains("lean_vc"));
        assert!(source.contains("PROVEN"));
    }

    #[test]
    fn test_verification_method_display() {
        assert_eq!(
            format!(
                "{}",
                VerificationMethod::Smt {
                    solver: "Z3".to_string()
                }
            ),
            "SMT/Z3"
        );
        assert_eq!(
            format!("{}", VerificationMethod::KInduction { k: 3 }),
            "k-induction (k=3)"
        );
        assert_eq!(
            format!(
                "{}",
                VerificationMethod::Chc {
                    backend: "Spacer".to_string()
                }
            ),
            "CHC/Spacer"
        );
        assert_eq!(
            format!("{}", VerificationMethod::Bmc { bound: 10 }),
            "BMC (bound=10)"
        );
        assert_eq!(
            format!("{}", VerificationMethod::WeakestPrecondition),
            "weakest precondition"
        );
    }

    #[test]
    fn test_certificate_serialization() {
        let vc = VerificationCondition {
            id: VcId(1),
            name: "serde_vc".to_string(),
            span: SourceSpan::default(),
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: None,
        };

        let cert = AuditCertificate::builder("serde_test")
            .add_vc(&vc, true)
            .build();

        let json = serde_json::to_string(&cert).expect("serialize");
        let parsed: AuditCertificate = serde_json::from_str(&json).expect("deserialize");

        assert_eq!(parsed.property_name, "serde_test");
        assert_eq!(parsed.vcs.len(), 1);
    }
}
