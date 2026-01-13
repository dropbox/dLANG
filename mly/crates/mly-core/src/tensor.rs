//! Core tensor type for Tensor Forge
//!
//! Extends gamma-crown's BoundedTensor with device placement and lazy evaluation.

use crate::{Device, DType, Shape, IntervalBounds, Result, TensorError};
use ndarray::{ArrayD, IxDyn};
use std::sync::Arc;

/// Device-agnostic tensor with verification support
///
/// # Design
///
/// - `storage`: Raw data on CPU or GPU
/// - `bounds`: Optional interval bounds for verification (gamma-crown integration)
/// - `node`: Graph node ID for lazy evaluation
/// - `device`: Where the data lives
///
/// # Example
///
/// ```rust
/// use mly_core::{Tensor, Device};
///
/// let x = Tensor::<f32>::zeros(&[2, 3], Device::Cpu);
/// let y = Tensor::<f32>::ones(&[2, 3], Device::Metal { device_id: 0 });
/// ```
#[derive(Clone)]
pub struct Tensor<T: TensorElement> {
    /// Tensor shape
    shape: Shape,

    /// Data storage (type-erased for device flexibility)
    storage: Storage<T>,

    /// Optional interval bounds for verification
    bounds: Option<IntervalBounds<T>>,

    /// Device placement
    device: Device,

    /// Lazy evaluation graph node (if part of computation graph)
    node: Option<GraphNodeId>,
}

/// Type constraint for tensor elements
pub trait TensorElement: Clone + Copy + Default + Send + Sync + num_traits::Zero + num_traits::One + 'static {
    fn dtype() -> DType;
}

impl TensorElement for f32 {
    fn dtype() -> DType { DType::F32 }
}

impl TensorElement for f64 {
    fn dtype() -> DType { DType::F64 }
}

impl TensorElement for i32 {
    fn dtype() -> DType { DType::I32 }
}

// TODO: Add f16 support when half crate is configured with num-traits feature
// use half::f16;

/// Storage abstraction - CPU array or GPU buffer reference
#[derive(Clone)]
pub enum Storage<T> {
    /// CPU storage using ndarray
    Cpu(Arc<ArrayD<T>>),

    /// Metal GPU buffer (handle to device memory)
    Metal { buffer_id: u64, len: usize },

    /// ANE storage (CoreML model fragment)
    Ane { model_id: u64 },

    /// Lazy - not yet materialized
    Lazy,
}

/// Graph node ID for lazy evaluation
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GraphNodeId(pub(crate) u64);

impl<T: TensorElement> Tensor<T> {
    /// Create tensor filled with zeros
    pub fn zeros(shape: &[usize], device: Device) -> Self {
        let shape = Shape::Dynamic(shape.to_vec());
        let storage = match device {
            Device::Cpu => {
                let arr = ArrayD::zeros(IxDyn(shape.dims()));
                Storage::Cpu(Arc::new(arr))
            }
            _ => Storage::Lazy, // Will materialize on first use
        };

        Self {
            shape,
            storage,
            bounds: None,
            device,
            node: None,
        }
    }

    /// Create tensor filled with ones
    pub fn ones(shape: &[usize], device: Device) -> Self {
        let shape = Shape::Dynamic(shape.to_vec());
        let storage = match device {
            Device::Cpu => {
                let arr = ArrayD::ones(IxDyn(shape.dims()));
                Storage::Cpu(Arc::new(arr))
            }
            _ => Storage::Lazy,
        };

        Self {
            shape,
            storage,
            bounds: None,
            device,
            node: None,
        }
    }

    /// Create tensor from ndarray (CPU)
    pub fn from_ndarray(arr: ArrayD<T>) -> Self {
        let shape = Shape::Dynamic(arr.shape().to_vec());
        Self {
            shape,
            storage: Storage::Cpu(Arc::new(arr)),
            bounds: None,
            device: Device::Cpu,
            node: None,
        }
    }

    /// Get tensor shape
    pub fn shape(&self) -> &Shape {
        &self.shape
    }

    /// Get tensor device
    pub fn device(&self) -> Device {
        self.device
    }

    /// Get data type
    pub fn dtype(&self) -> DType {
        T::dtype()
    }

    /// Set interval bounds for verification
    pub fn with_bounds(mut self, bounds: IntervalBounds<T>) -> Self {
        self.bounds = Some(bounds);
        self
    }

    /// Get interval bounds (for gamma-crown integration)
    pub fn bounds(&self) -> Option<&IntervalBounds<T>> {
        self.bounds.as_ref()
    }

    /// Move tensor to device
    pub fn to_device(&self, device: Device) -> Result<Self> {
        if self.device == device {
            return Ok(self.clone());
        }

        // TODO: Implement actual device transfer
        Err(TensorError::Unsupported("Device transfer not yet implemented".into()))
    }

    /// Get as ndarray (CPU only)
    pub fn as_ndarray(&self) -> Result<&ArrayD<T>> {
        match &self.storage {
            Storage::Cpu(arr) => Ok(arr.as_ref()),
            _ => Err(TensorError::DeviceError("Tensor not on CPU".into())),
        }
    }

    /// Total number of elements
    pub fn numel(&self) -> usize {
        self.shape.numel()
    }
}

impl<T: TensorElement> std::fmt::Debug for Tensor<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Tensor")
            .field("shape", &self.shape)
            .field("dtype", &T::dtype())
            .field("device", &self.device)
            .field("has_bounds", &self.bounds.is_some())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zeros() {
        let t = Tensor::<f32>::zeros(&[2, 3], Device::Cpu);
        assert_eq!(t.shape().dims(), &[2, 3]);
        assert_eq!(t.numel(), 6);
    }

    #[test]
    fn test_from_ndarray() {
        let arr = ArrayD::from_elem(IxDyn(&[2, 3]), 1.5f32);
        let t = Tensor::from_ndarray(arr);
        assert_eq!(t.device(), Device::Cpu);
    }
}
