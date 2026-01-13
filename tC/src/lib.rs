//! tC: Trusted C Verification
//!
//! C verification layer bridging tRust↔tSwift with ACSL specs
//! and per-compilation translation validation.
//!
//! # Overview
//!
//! tC verifies C code in three ways:
//!
//! 1. **Source Verification**: Proves ACSL specifications hold
//! 2. **Translation Validation**: Proves Clang compilation preserves semantics
//! 3. **FFI Verification**: Proves Swift↔C and Rust↔C boundaries are compatible
//!
//! # Example
//!
//! ```ignore
//! use tc_verify::{verify_file, VerifyOptions};
//!
//! let result = verify_file("example.c", &VerifyOptions::default())?;
//! assert!(result.is_verified());
//! ```

pub mod parser;
pub mod vc_gen;
pub mod ffi;

#[cfg(feature = "translation-validation")]
pub mod tv;

mod error;

pub use error::{TcError, TcResult};

/// Verification options
#[derive(Debug, Clone, Default)]
pub struct VerifyOptions {
    /// Enable translation validation (requires Alive2)
    pub translation_validation: bool,
    /// Check FFI boundaries with Rust
    pub rust_bridge: Option<std::path::PathBuf>,
    /// Check FFI boundaries with Swift
    pub swift_bridge: Option<std::path::PathBuf>,
    /// Backend to use (z4, kani, lean5)
    pub backend: Backend,
    /// Verbosity level
    pub verbose: bool,
}

/// Verification backend
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Backend {
    /// Z4 SMT solver (default)
    #[default]
    Z4,
    /// Kani bounded model checker
    Kani,
    /// Lean5 theorem prover
    Lean5,
}

/// Result of verification
#[derive(Debug, Clone)]
pub struct VerifyResult {
    /// Whether all conditions were verified
    pub verified: bool,
    /// Number of verification conditions
    pub vc_count: usize,
    /// Number of VCs proven
    pub proven_count: usize,
    /// Counterexamples (if any)
    pub counterexamples: Vec<Counterexample>,
    /// Warnings
    pub warnings: Vec<String>,
}

impl VerifyResult {
    /// Returns true if all verification conditions were proven
    pub fn is_verified(&self) -> bool {
        self.verified
    }
}

/// A counterexample showing why a VC failed
#[derive(Debug, Clone)]
pub struct Counterexample {
    /// Name of the function
    pub function: String,
    /// Description of the failed condition
    pub condition: String,
    /// Variable assignments that violate the condition
    pub assignments: Vec<(String, String)>,
    /// Source location
    pub location: SourceLocation,
}

/// Source location for error reporting
#[derive(Debug, Clone, Default)]
pub struct SourceLocation {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

/// Verify a C file
pub fn verify_file(
    path: impl AsRef<std::path::Path>,
    options: &VerifyOptions,
) -> TcResult<VerifyResult> {
    let path = path.as_ref();

    // Phase 1: Parse C with libclang
    let _ast = parser::parse_file(path)?;

    // Phase 2: Extract ACSL specs
    let _specs = parser::extract_specs(path)?;

    // Phase 3: Generate VC IR
    // let vcs = vc_gen::generate_vcs(&ast, &specs)?;

    // Phase 4: Verify with backend
    // let result = backend::verify(&vcs, options.backend)?;

    // Phase 5 (optional): Translation validation
    // if options.translation_validation {
    //     tv::validate_translation(path)?;
    // }

    // Phase 6 (optional): FFI verification
    // if let Some(rust_bridge) = &options.rust_bridge {
    //     ffi::verify_rust_boundary(&specs, rust_bridge)?;
    // }

    // Placeholder result
    Ok(VerifyResult {
        verified: true,
        vc_count: 0,
        proven_count: 0,
        counterexamples: vec![],
        warnings: vec!["tC is not yet implemented - this is a skeleton".to_string()],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verify_options_default() {
        let opts = VerifyOptions::default();
        assert!(!opts.translation_validation);
        assert!(opts.rust_bridge.is_none());
        assert_eq!(opts.backend, Backend::Z4);
    }

    #[test]
    fn test_verify_result() {
        let result = VerifyResult {
            verified: true,
            vc_count: 3,
            proven_count: 3,
            counterexamples: vec![],
            warnings: vec![],
        };
        assert!(result.is_verified());
    }
}
