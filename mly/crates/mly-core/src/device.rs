//! Device types for Tensor Forge

/// Compute device for tensor operations
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Device {
    /// CPU with optional SIMD
    Cpu,

    /// Metal GPU
    Metal { device_id: u32 },

    /// Apple Neural Engine (via CoreML)
    Ane,
}

impl Device {
    /// Default Metal device
    pub fn metal() -> Self {
        Device::Metal { device_id: 0 }
    }

    /// Check if device is GPU
    pub fn is_gpu(&self) -> bool {
        matches!(self, Device::Metal { .. })
    }

    /// Check if device is ANE
    pub fn is_ane(&self) -> bool {
        matches!(self, Device::Ane)
    }
}

impl Default for Device {
    fn default() -> Self {
        Device::Cpu
    }
}

/// Detected Apple Silicon capabilities
#[derive(Clone, Debug)]
pub struct ChipCapabilities {
    /// Chip family
    pub family: ChipFamily,

    /// GPU core count
    pub gpu_cores: u32,

    /// ANE available
    pub has_ane: bool,

    /// Memory bandwidth (GB/s)
    pub memory_bandwidth_gbps: f32,

    /// Unified memory size (GB)
    pub memory_gb: u32,
}

/// Apple Silicon chip families
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChipFamily {
    // Mac
    M1, M1Pro, M1Max, M1Ultra,
    M2, M2Pro, M2Max, M2Ultra,
    M3, M3Pro, M3Max,
    M4, M4Pro, M4Max,
    // iPhone/iPad
    A14, A15, A16, A17Pro, A18, A18Pro,
    // Unknown
    Unknown,
}

impl ChipCapabilities {
    /// Detect current chip capabilities
    pub fn detect() -> Self {
        // TODO: Use IOKit to detect actual chip
        // For now, return reasonable defaults for M1
        Self {
            family: ChipFamily::Unknown,
            gpu_cores: 8,
            has_ane: true,
            memory_bandwidth_gbps: 68.0,
            memory_gb: 8,
        }
    }
}
