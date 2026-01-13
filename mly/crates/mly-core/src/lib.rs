//! Tensor Forge Core - AI-native tensor types for Apple Silicon
//!
//! This crate provides the foundational tensor types that extend gamma-crown's
//! BoundedTensor with device placement, verification support, and lazy evaluation.

pub mod tensor;
pub mod shape;
pub mod dtype;
pub mod device;
pub mod bounds;
pub mod error;

pub use tensor::Tensor;
pub use shape::Shape;
pub use dtype::DType;
pub use device::Device;
pub use bounds::IntervalBounds;
pub use error::{TensorError, Result};

/// Re-export ndarray for interop
pub use ndarray;
