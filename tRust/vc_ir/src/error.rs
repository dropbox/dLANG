//! Error types for verification

use crate::SourceSpan;
use serde::{Deserialize, Serialize};
use std::fmt::Write;

/// Verification error
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VerifyError {
    /// No backend available for this VC kind
    NoBackend { vc_kind: String },

    /// Backend timed out
    Timeout { backend: String, timeout_ms: u64 },

    /// Backend ran out of memory
    OutOfMemory { backend: String, limit_mb: usize },

    /// Backend internal error
    BackendError { backend: String, message: String },

    /// Invalid specification syntax
    InvalidSpec { span: SourceSpan, message: String },

    /// Type error in specification
    TypeError {
        span: SourceSpan,
        expected: String,
        found: String,
    },

    /// Unknown function in specification
    UnknownFunction { span: SourceSpan, name: String },

    /// Unsupported feature
    Unsupported {
        feature: String,
        suggestion: Option<String>,
    },

    /// Cyclic dependency in specifications
    CyclicSpec { cycle: Vec<String> },
}

impl std::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoBackend { vc_kind } => {
                write!(f, "no verification backend available for: {vc_kind}")
            }
            Self::Timeout {
                backend,
                timeout_ms,
            } => {
                write!(
                    f,
                    "verification timed out after {timeout_ms}ms in {backend}"
                )
            }
            Self::OutOfMemory { backend, limit_mb } => {
                write!(
                    f,
                    "verification exceeded {limit_mb}MB memory limit in {backend}"
                )
            }
            Self::BackendError { backend, message } => {
                write!(f, "error in {backend}: {message}")
            }
            Self::InvalidSpec { message, .. } => {
                write!(f, "invalid specification: {message}")
            }
            Self::TypeError {
                expected, found, ..
            } => {
                write!(f, "type error: expected {expected}, found {found}")
            }
            Self::UnknownFunction { name, .. } => {
                write!(f, "unknown function in specification: {name}")
            }
            Self::Unsupported {
                feature,
                suggestion,
            } => {
                if let Some(sug) = suggestion {
                    write!(f, "unsupported: {feature}. Try: {sug}")
                } else {
                    write!(f, "unsupported: {feature}")
                }
            }
            Self::CyclicSpec { cycle } => {
                write!(f, "cyclic specification dependency: {}", cycle.join(" -> "))
            }
        }
    }
}

impl std::error::Error for VerifyError {}

/// Diagnostic for reporting to the user
#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub level: DiagnosticLevel,
    pub code: String,
    pub message: String,
    pub primary_span: Option<SpanLabel>,
    pub secondary_spans: Vec<SpanLabel>,
    pub notes: Vec<String>,
    pub suggestions: Vec<Suggestion>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticLevel {
    Error,
    Warning,
    Note,
    Help,
}

#[derive(Debug, Clone)]
pub struct SpanLabel {
    pub span: SourceSpan,
    pub label: String,
}

#[derive(Debug, Clone)]
pub struct Suggestion {
    pub message: String,
    pub replacement: String,
    pub span: SourceSpan,
}

impl Diagnostic {
    pub fn error(code: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            level: DiagnosticLevel::Error,
            code: code.into(),
            message: message.into(),
            primary_span: None,
            secondary_spans: vec![],
            notes: vec![],
            suggestions: vec![],
        }
    }

    #[must_use]
    pub fn with_span(mut self, span: SourceSpan, label: impl Into<String>) -> Self {
        self.primary_span = Some(SpanLabel {
            span,
            label: label.into(),
        });
        self
    }

    #[must_use]
    pub fn with_secondary(mut self, span: SourceSpan, label: impl Into<String>) -> Self {
        self.secondary_spans.push(SpanLabel {
            span,
            label: label.into(),
        });
        self
    }

    #[must_use]
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    #[must_use]
    pub fn with_suggestion(
        mut self,
        message: impl Into<String>,
        replacement: impl Into<String>,
        span: SourceSpan,
    ) -> Self {
        self.suggestions.push(Suggestion {
            message: message.into(),
            replacement: replacement.into(),
            span,
        });
        self
    }
}

/// Build diagnostics from verification results
#[must_use]
pub fn diagnostic_from_counterexample(
    vc: &crate::VerificationCondition,
    cx: &crate::Counterexample,
) -> Diagnostic {
    let name = &vc.name;
    let mut diag = Diagnostic::error("E0900", format!("verification failed: {name}"))
        .with_span(vc.span.clone(), "verification condition declared here");

    // Add counterexample as note
    let mut cx_note = String::from("counterexample:\n");
    for (var, val) in &cx.assignments {
        let _ = writeln!(cx_note, "  {var} = {val:?}");
    }
    diag = diag.with_note(cx_note);

    // Add trace if available
    if let Some(trace) = &cx.trace {
        let mut trace_note = String::from("execution trace:\n");
        for (i, step) in trace.iter().enumerate() {
            let file = &step.location.file;
            let line = step.location.line_start;
            let _ = write!(trace_note, "  [{i}] {file}:{line}");
            if let Some(action) = &step.action {
                let _ = write!(trace_note, " ({action})");
            }
            trace_note.push('\n');
        }
        diag = diag.with_note(trace_note);
    }

    // Add explanation
    diag = diag.with_note(cx.explanation.clone());

    diag
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_error_no_backend_display() {
        let err = VerifyError::NoBackend {
            vc_kind: "temporal".to_string(),
        };
        assert_eq!(
            err.to_string(),
            "no verification backend available for: temporal"
        );
    }

    #[test]
    fn test_verify_error_timeout_display() {
        let err = VerifyError::Timeout {
            backend: "z4".to_string(),
            timeout_ms: 5000,
        };
        assert_eq!(err.to_string(), "verification timed out after 5000ms in z4");
    }

    #[test]
    fn test_verify_error_out_of_memory_display() {
        let err = VerifyError::OutOfMemory {
            backend: "z4".to_string(),
            limit_mb: 1024,
        };
        assert_eq!(
            err.to_string(),
            "verification exceeded 1024MB memory limit in z4"
        );
    }

    #[test]
    fn test_verify_error_backend_error_display() {
        let err = VerifyError::BackendError {
            backend: "z4".to_string(),
            message: "invalid SMT-LIB syntax".to_string(),
        };
        assert_eq!(err.to_string(), "error in z4: invalid SMT-LIB syntax");
    }

    #[test]
    fn test_verify_error_invalid_spec_display() {
        let err = VerifyError::InvalidSpec {
            span: SourceSpan::default(),
            message: "expected predicate".to_string(),
        };
        assert_eq!(err.to_string(), "invalid specification: expected predicate");
    }

    #[test]
    fn test_verify_error_type_error_display() {
        let err = VerifyError::TypeError {
            span: SourceSpan::default(),
            expected: "i32".to_string(),
            found: "bool".to_string(),
        };
        assert_eq!(err.to_string(), "type error: expected i32, found bool");
    }

    #[test]
    fn test_verify_error_unknown_function_display() {
        let err = VerifyError::UnknownFunction {
            span: SourceSpan::default(),
            name: "my_lemma".to_string(),
        };
        assert_eq!(
            err.to_string(),
            "unknown function in specification: my_lemma"
        );
    }

    #[test]
    fn test_verify_error_unsupported_without_suggestion_display() {
        let err = VerifyError::Unsupported {
            feature: "closures".to_string(),
            suggestion: None,
        };
        assert_eq!(err.to_string(), "unsupported: closures");
    }

    #[test]
    fn test_verify_error_unsupported_with_suggestion_display() {
        let err = VerifyError::Unsupported {
            feature: "async functions".to_string(),
            suggestion: Some("use #[trusted] for now".to_string()),
        };
        assert_eq!(
            err.to_string(),
            "unsupported: async functions. Try: use #[trusted] for now"
        );
    }

    #[test]
    fn test_verify_error_cyclic_spec_display() {
        let err = VerifyError::CyclicSpec {
            cycle: vec!["foo".to_string(), "bar".to_string(), "foo".to_string()],
        };
        assert_eq!(
            err.to_string(),
            "cyclic specification dependency: foo -> bar -> foo"
        );
    }

    #[test]
    fn test_diagnostic_error_creation() {
        let diag = Diagnostic::error("E0001", "test error");
        assert_eq!(diag.level, DiagnosticLevel::Error);
        assert_eq!(diag.code, "E0001");
        assert_eq!(diag.message, "test error");
        assert!(diag.primary_span.is_none());
        assert!(diag.secondary_spans.is_empty());
        assert!(diag.notes.is_empty());
        assert!(diag.suggestions.is_empty());
    }

    #[test]
    fn test_diagnostic_with_span() {
        let span = SourceSpan::default();
        let diag = Diagnostic::error("E0002", "error with span").with_span(span.clone(), "here");
        assert!(diag.primary_span.is_some());
        let label = diag.primary_span.unwrap();
        assert_eq!(&*label.span.file, "<unknown>");
        assert_eq!(label.label, "here");
    }

    #[test]
    fn test_diagnostic_with_secondary() {
        let span = SourceSpan::default();
        let diag = Diagnostic::error("E0003", "error")
            .with_secondary(span.clone(), "related")
            .with_secondary(span, "also related");
        assert_eq!(diag.secondary_spans.len(), 2);
        assert_eq!(diag.secondary_spans[0].label, "related");
        assert_eq!(diag.secondary_spans[1].label, "also related");
    }

    #[test]
    fn test_diagnostic_with_note() {
        let diag = Diagnostic::error("E0004", "error")
            .with_note("note 1")
            .with_note("note 2");
        assert_eq!(diag.notes.len(), 2);
        assert_eq!(diag.notes[0], "note 1");
        assert_eq!(diag.notes[1], "note 2");
    }

    #[test]
    fn test_diagnostic_with_suggestion() {
        let span = SourceSpan::default();
        let diag = Diagnostic::error("E0005", "error").with_suggestion(
            "try this instead",
            "replacement_code",
            span,
        );
        assert_eq!(diag.suggestions.len(), 1);
        assert_eq!(diag.suggestions[0].message, "try this instead");
        assert_eq!(diag.suggestions[0].replacement, "replacement_code");
    }

    #[test]
    fn test_diagnostic_builder_chain() {
        let span = SourceSpan::default();
        let diag = Diagnostic::error("E0006", "complex error")
            .with_span(span.clone(), "main location")
            .with_secondary(span.clone(), "related")
            .with_note("important note")
            .with_suggestion("fix", "fixed_code", span);

        assert_eq!(diag.level, DiagnosticLevel::Error);
        assert!(diag.primary_span.is_some());
        assert_eq!(diag.secondary_spans.len(), 1);
        assert_eq!(diag.notes.len(), 1);
        assert_eq!(diag.suggestions.len(), 1);
    }

    #[test]
    fn test_diagnostic_level_equality() {
        assert_eq!(DiagnosticLevel::Error, DiagnosticLevel::Error);
        assert_eq!(DiagnosticLevel::Warning, DiagnosticLevel::Warning);
        assert_eq!(DiagnosticLevel::Note, DiagnosticLevel::Note);
        assert_eq!(DiagnosticLevel::Help, DiagnosticLevel::Help);
        assert_ne!(DiagnosticLevel::Error, DiagnosticLevel::Warning);
    }
}
