//! Rust ↔ C FFI boundary verification
//!
//! Verifies that Rust #[requires]/#[ensures] match C ACSL specs.

use crate::error::{TcError, TcResult};
use crate::parser::FunctionSpec;
use std::path::Path;

/// Result of FFI boundary check
#[derive(Debug)]
pub struct FfiBoundaryResult {
    /// Whether all boundaries are compatible
    pub compatible: bool,
    /// List of mismatches
    pub mismatches: Vec<FfiMismatch>,
}

/// A mismatch between C and Rust specs
#[derive(Debug)]
pub struct FfiMismatch {
    /// Function name
    pub function: String,
    /// Kind of mismatch
    pub kind: MismatchKind,
    /// Description
    pub description: String,
}

/// Kind of FFI mismatch
#[derive(Debug)]
pub enum MismatchKind {
    /// C precondition not implied by Rust precondition
    PreconditionWeaker,
    /// Rust postcondition not implied by C postcondition
    PostconditionStronger,
    /// Type layouts don't match
    TypeLayoutMismatch,
    /// Missing spec on one side
    MissingSpec,
}

/// Verify Rust ↔ C boundary
///
/// Checks that:
/// 1. Rust precondition implies C precondition
/// 2. C postcondition implies Rust postcondition
/// 3. Type layouts match
///
/// # Arguments
///
/// * `c_specs` - ACSL specs from C file
/// * `rust_file` - Path to Rust file with extern "C" declarations
#[allow(unused_variables)]
pub fn verify_rust_boundary(
    c_specs: &[FunctionSpec],
    rust_file: &Path,
) -> TcResult<FfiBoundaryResult> {
    if !rust_file.exists() {
        return Err(TcError::FileNotFound(rust_file.display().to_string()));
    }

    // TODO: Implement actual boundary verification
    //
    // This would:
    // 1. Parse Rust file for extern "C" declarations
    // 2. Extract #[requires]/#[ensures] attributes
    // 3. Match Rust and C function specs by name
    // 4. For each pair:
    //    a. Check Rust requires => C requires
    //    b. Check C ensures => Rust ensures
    //    c. Check type layouts match

    tracing::info!(
        "Verifying Rust↔C boundary: {} C specs, Rust file: {}",
        c_specs.len(),
        rust_file.display()
    );

    Ok(FfiBoundaryResult {
        compatible: true,
        mismatches: vec![],
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_verify_rust_boundary_empty() {
        let mut file = NamedTempFile::with_suffix(".rs").unwrap();
        writeln!(file, "// empty rust file").unwrap();

        let result = verify_rust_boundary(&[], file.path()).unwrap();
        assert!(result.compatible);
    }

    #[test]
    fn test_verify_rust_boundary_missing_file() {
        let result = verify_rust_boundary(&[], Path::new("/nonexistent.rs"));
        assert!(matches!(result, Err(TcError::FileNotFound(_))));
    }
}
