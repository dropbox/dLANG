//! CPU backend with ARM NEON SIMD
//!
//! Fallback for small operations where GPU dispatch overhead exceeds compute time.

// TODO: Phase 2 implementation
// - NEON intrinsics
// - Parallel execution via rayon
