//! Error types for tC

use thiserror::Error;

/// Result type for tC operations
pub type TcResult<T> = Result<T, TcError>;

/// Errors that can occur during verification
#[derive(Error, Debug)]
pub enum TcError {
    /// Failed to parse C file
    #[error("Parse error in {file}: {message}")]
    ParseError { file: String, message: String },

    /// Failed to extract ACSL specs
    #[error("ACSL parse error in {file}:{line}: {message}")]
    AcslError {
        file: String,
        line: u32,
        message: String,
    },

    /// Verification condition generation failed
    #[error("VC generation error: {0}")]
    VcGenError(String),

    /// Backend verification failed
    #[error("Backend error ({backend}): {message}")]
    BackendError { backend: String, message: String },

    /// Translation validation failed
    #[error("Translation validation failed: {0}")]
    TranslationValidationError(String),

    /// FFI boundary mismatch
    #[error("FFI boundary mismatch between {lang1} and {lang2}: {message}")]
    FfiBoundaryError {
        lang1: String,
        lang2: String,
        message: String,
    },

    /// File not found
    #[error("File not found: {0}")]
    FileNotFound(String),

    /// IO error
    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),

    /// libclang not available
    #[error("libclang not found. Install LLVM/Clang and set LIBCLANG_PATH.")]
    LibclangNotFound,
}
