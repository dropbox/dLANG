//! Tensor Forge DSL - AI-friendly kernel language
//!
//! Provides the #[kernel] proc-macro and IR for compiling to Metal/ANE/CPU.

pub mod ir;
pub mod ops;

// TODO: Phase 1 implementation
// - #[kernel] proc-macro
// - IR types (KernelIR, NodeId, etc.)
// - Metal codegen
// - Optimization passes
