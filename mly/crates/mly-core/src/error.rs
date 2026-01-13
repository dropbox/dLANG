//! Error types for Tensor Forge

use thiserror::Error;

/// Result type for Tensor Forge operations
pub type Result<T> = std::result::Result<T, TensorError>;

/// Errors that can occur in Tensor Forge
#[derive(Error, Debug)]
pub enum TensorError {
    #[error("Shape mismatch: expected {expected:?}, got {actual:?}")]
    ShapeMismatch {
        expected: Vec<usize>,
        actual: Vec<usize>,
    },

    #[error("Invalid shape: {0}")]
    InvalidShape(String),

    #[error("Device error: {0}")]
    DeviceError(String),

    #[error("Metal error: {0}")]
    MetalError(String),

    #[error("ANE error: {0}")]
    AneError(String),

    #[error("Bounds error: {0}")]
    BoundsError(String),

    #[error("Verification failed: {0}")]
    VerificationFailed(String),

    #[error("Data type mismatch: expected {expected}, got {actual}")]
    DTypeMismatch { expected: String, actual: String },

    #[error("Out of memory: requested {requested} bytes, available {available}")]
    OutOfMemory { requested: usize, available: usize },

    #[error("Operation not supported: {0}")]
    Unsupported(String),

    #[error("IO error: {0}")]
    IoError(#[from] std::io::Error),
}
