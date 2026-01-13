# Tensor Forge: AI-Native ML Framework for Apple Silicon

**Repository:** `github.com/dropbox/dLANG/mly`
**Created:** 2026-01-03
**Status:** Planning/Early Implementation

---

## Executive Summary

**Tensor Forge** replaces MLX with a Rust-first ML framework designed for AI agents to write high-performance tensor operations. Key differentiators:

1. **AI writes high-level DSL** → compiles to optimal Metal/ANE/CPU
2. **gamma-crown verification built-in** - not an afterthought
3. **Zero Python overhead** - pure Rust with Swift bindings
4. **Multi-architecture** - M1, M4, A17 Pro, iPhone support

---

## Why Not MLX?

| Issue | MLX | Tensor Forge |
|-------|-----|--------------|
| Per-call overhead | ~1ms dispatch | <100μs target |
| AI kernel writing | Must write Metal directly | High-level DSL with verification |
| Verification | None | gamma-crown bounds, z4 SMT, tC proofs |
| Language | Python-first | Rust-first (then Swift, then Python) |
| JIT variance | 200-800ms first run | Persistent kernel cache |

---

## Architecture Overview

```
mly/
├── crates/
│   ├── mly-core/      # Tensor types, shapes, devices
│   ├── mly-dsl/       # #[kernel] proc-macro, IR, optimization
│   ├── mly-metal/     # Metal GPU backend
│   ├── mly-ane/       # Apple Neural Engine via CoreML
│   ├── mly-cpu/       # NEON SIMD fallback
│   ├── mly-runtime/   # Adaptive dispatch, lazy eval, caching
│   ├── mly-verify/    # gamma-crown + z4 + tC integration
│   ├── mly-mlx/       # MLX model import bridge
│   └── mly-swift/     # Swift bindings
├── examples/
│   ├── whisper/                # Whisper STT
│   └── kokoro/                 # Kokoro TTS
└── benches/                    # Criterion benchmarks
```

---

## Crate Responsibilities

### mly-core
Core tensor types extending gamma-crown's BoundedTensor:

```rust
/// Device-agnostic tensor with verification support
pub struct Tensor<T> {
    shape: Shape,
    storage: Storage<T>,
    bounds: Option<IntervalBounds<T>>,  // For verification
    device: Device,
    node: Option<GraphNodeId>,          // For lazy eval
}

pub enum Device {
    Cpu,
    Metal { device_id: u32 },
    Ane,
}

pub enum Shape {
    Static(StaticShape),           // Compile-time known
    Hybrid { batch: usize, fixed: StaticShape },
    Dynamic(Vec<usize>),
}
```

### mly-dsl
AI-friendly kernel DSL with proc-macro:

```rust
#[kernel]
fn snake1d(x: Tensor<f32>, alpha: Tensor<f32>) -> Tensor<f32> {
    let sin_val = (alpha * x).sin();
    x + (1.0 / alpha) * sin_val * sin_val
}

// With verification contracts
#[kernel]
#[requires(x.bounds().lower >= -10.0)]
#[ensures(result.bounds().upper <= 100.0)]
fn verified_relu(x: Tensor<f32>) -> Tensor<f32> {
    x.maximum(0.0)
}

// With automatic fusion
#[kernel(fusion = true)]
fn adain_conv(
    x: Tensor<f32>,
    weight: Tensor<f32>,
    gamma: Tensor<f32>,
    beta: Tensor<f32>,
) -> Tensor<f32> {
    let mean = x.mean(axis = 1, keepdims = true);
    let var = x.var(axis = 1, keepdims = true);
    let x_norm = (x - mean) / (var + 1e-5).sqrt();
    let x_styled = gamma.unsqueeze(1) * x_norm + beta.unsqueeze(1);
    x_styled.conv1d(weight, stride = 1, padding = 1)
}
```

**Compilation Pipeline:**
1. Parse DSL → Kernel IR
2. Validate IR
3. Optimization passes (CSE, dead code, fusion)
4. Generate target code (Metal MSL / CoreML / Rust+SIMD)
5. Optional: Verify with gamma-crown/z4/tC

### mly-metal
Metal GPU backend:

- Command queue and buffer management
- MSL code generation from IR
- Architecture-specific optimizations (M1 vs M4)
- Kernel caching (persistent across runs)
- Buffer pooling (avoid per-call allocation)

### mly-ane
Apple Neural Engine backend:

- IR → CoreML model fragments
- ANE-compatible op detection
- Automatic fallback for unsupported ops
- Batch size thresholds (ANE efficient at batch ≥4)

### mly-cpu
CPU fallback with SIMD:

- ARM NEON kernels
- Scalar fallback for non-SIMD platforms
- Used for small ops (<10K flops) to avoid GPU dispatch overhead

### mly-runtime
Adaptive runtime:

```rust
pub struct AdaptiveDispatcher {
    capabilities: ChipCapabilities,
    kernel_cache: KernelCache,
}

impl AdaptiveDispatcher {
    pub fn dispatch(&self, op: &Op, inputs: &[&Tensor]) -> ExecutionPlan {
        match self.profile_op(op, inputs) {
            // ANE for large batch matmul/conv
            p if p.is_ane_compatible() && p.batch_size >= 4
                => ExecutionPlan::Ane,

            // Metal for most tensor ops
            p if p.estimated_flops >= 10_000
                => ExecutionPlan::Metal,

            // CPU for small ops
            _ => ExecutionPlan::Cpu,
        }
    }
}
```

Features:
- Lazy evaluation graph
- Operation fusion
- Persistent kernel cache
- Zero-copy unified memory
- Parallel stream management

### mly-verify
Verification integration:

```
DSL Kernel
    │
    ▼
┌─────────────────────────────────────────────────────────┐
│                    VERIFICATION PIPELINE                 │
├─────────────────────────────────────────────────────────┤
│                                                          │
│  gamma-crown          z4 SMT           tC               │
│  ┌──────────────┐    ┌──────────────┐  ┌──────────────┐ │
│  │ IBP/CROWN    │    │ Overflow     │  │ Metal C      │ │
│  │ bounds       │    │ Array bounds │  │ verification │ │
│  │ Neural net   │    │ Contracts    │  │ FFI safety   │ │
│  └──────────────┘    └──────────────┘  └──────────────┘ │
│                                                          │
└─────────────────────────────────────────────────────────┘
```

### mly-mlx
Migration bridge from existing MLX models:

- Safetensors weight loading
- MLX op compatibility layer
- C++ inference engine bridge (gradual migration)
- Numerical equivalence validation

### mly-swift
Swift bindings for iOS/macOS:

- cbindgen C header generation
- Swift wrapper classes
- Swift Package Manager support

---

## Multi-Architecture Strategy

### Chip Detection

```rust
pub enum ChipFamily {
    // Mac
    M1, M1Pro, M1Max, M1Ultra,
    M2, M2Pro, M2Max, M2Ultra,
    M3, M3Pro, M3Max,
    M4, M4Pro, M4Max,
    // iPhone/iPad
    A14, A15, A16, A17Pro, A18, A18Pro,
}

pub struct ChipCapabilities {
    pub family: ChipFamily,
    pub gpu_cores: u32,
    pub ane: Option<AneCapabilities>,
    pub memory_bandwidth: f32,  // GB/s
    pub memory_size: u32,       // GB
}
```

### Execution Path Selection

| Operation | M1 (8 GPU) | M4 Max (40 GPU) | A17 Pro (iPhone) |
|-----------|------------|-----------------|------------------|
| Small matmul (<1K) | CPU NEON | CPU NEON | CPU NEON |
| Medium matmul | Metal | Metal | Metal |
| Large batch matmul | ANE | Metal (more cores) | ANE |
| Conv2d batch≥4 | ANE | ANE | ANE |
| Custom activation | Metal | Metal | Metal |

---

## Verification Integration

### gamma-crown (Neural Network Bounds)

From existing gamma-crown crate:
- `BoundedTensor` - interval bounds per element
- IBP (Interval Bound Propagation) - fast, loose
- CROWN - linear relaxation, tighter
- α-CROWN - optimized relaxation
- β-CROWN - complete verification via branch-and-bound

### z4 (SMT Solver)

For contract verification:
```rust
#[requires(x.len() == 784)]
#[requires(x.iter().all(|v| *v >= 0.0 && *v <= 1.0))]
#[ensures(result < 10)]
fn classify(model: &Model, x: &[f32; 784]) -> u8
```

### tC (C Verification)

For Metal shader verification:
- ACSL-style annotations on generated MSL
- Verify memory safety, bounds, overflow

---

## Kernel IR

```rust
pub enum KernelIR {
    // Inputs/outputs
    Input { name: String, dtype: DType, shape: Shape },
    Output { name: String, dtype: DType },

    // Operations
    BinOp { op: BinOpKind, lhs: NodeId, rhs: NodeId },
    UnaryOp { op: UnaryOpKind, input: NodeId },
    Reduce { op: ReduceKind, input: NodeId, axis: Vec<i32>, keepdims: bool },
    Conv { input: NodeId, weight: NodeId, config: ConvConfig },
    MatMul { lhs: NodeId, rhs: NodeId, transpose_a: bool, transpose_b: bool },

    // Layout
    Reshape { input: NodeId, shape: Shape },
    Transpose { input: NodeId, perm: Vec<usize> },

    // Constants
    Constant { value: f64 },

    // Optimization result
    Fused { ops: Vec<KernelIR>, fusion_type: FusionType },
}

pub enum FusionType {
    ElementwiseChain,   // x + y * z
    MatMulActivation,   // matmul + relu
    NormScale,          // layernorm + scale (AdaIN)
    ConvActivation,     // conv + activation
}
```

---

## Implementation Phases

### Phase 0: Foundation (10-15 commits, 2-3 hours)

| Step | Description | Status |
|------|-------------|--------|
| 0.1 | Create workspace structure | DONE |
| 0.2 | Core tensor types | IN PROGRESS |
| 0.3 | Basic Metal runtime | TODO |
| 0.4 | Port snake1d kernel | TODO |
| 0.5 | Benchmark vs MLX | TODO |

**Checkpoint:** Snake1D runs on Metal with comparable perf to MLX

### Phase 1: DSL and IR (20-25 commits, 4-5 hours)

| Step | Description |
|------|-------------|
| 1.1 | Define IR types |
| 1.2 | Implement `#[kernel]` proc-macro |
| 1.3 | Metal codegen from IR |
| 1.4 | Optimization passes (CSE, dead code) |
| 1.5 | Operation fusion |
| 1.6 | Port adain_conv as fusion example |

**Checkpoint:** DSL kernels compile to Metal with automatic fusion

### Phase 2: Multi-Architecture (25-30 commits, 5-6 hours)

| Step | Description |
|------|-------------|
| 2.1 | CPU NEON backend |
| 2.2 | Chip detection (M1/M4/A17) |
| 2.3 | Adaptive dispatch logic |
| 2.4 | ANE/CoreML compilation |
| 2.5 | Persistent kernel cache |
| 2.6 | Cross-architecture benchmarks |

**Checkpoint:** Same kernel runs optimally on GPU, ANE, and CPU

### Phase 3: Verification (15-20 commits, 3-4 hours)

| Step | Description |
|------|-------------|
| 3.1 | gamma-crown BoundedTensor integration |
| 3.2 | Interval bound propagation for DSL ops |
| 3.3 | `#[requires]`/`#[ensures]` contract macros |
| 3.4 | z4 SMT verification |
| 3.5 | Optional tC Metal verification |

**Checkpoint:** Verified kernel with proven numerical bounds

### Phase 4: MLX Migration (20-25 commits, 4-5 hours)

| Step | Description |
|------|-------------|
| 4.1 | Safetensors weight loading |
| 4.2 | MLX op compatibility layer |
| 4.3 | Port Whisper model |
| 4.4 | Port Kokoro TTS model |
| 4.5 | Numerical equivalence validation |

**Checkpoint:** Production models running on Tensor Forge

### Phase 5: Swift Bindings (10-15 commits, 2-3 hours)

| Step | Description |
|------|-------------|
| 5.1 | cbindgen C headers |
| 5.2 | Swift wrapper classes |
| 5.3 | Swift Package Manager |
| 5.4 | iOS example app |

**Checkpoint:** Swift app running model on iPhone

### Phase 6: Optimization (20-30 commits, 4-6 hours)

| Step | Description |
|------|-------------|
| 6.1 | Lazy evaluation graph |
| 6.2 | Zero-copy unified memory |
| 6.3 | Persistent kernel cache |
| 6.4 | Parallel stream management |
| 6.5 | Comprehensive benchmarks |
| 6.6 | Documentation |

**Checkpoint:** <100μs dispatch, MLX parity or better

---

## Dependencies

### External Crates

| Crate | Version | Purpose |
|-------|---------|---------|
| ndarray | 0.16 | N-dimensional arrays |
| metal | 0.29 | Metal API bindings |
| half | 2.4 | float16/bfloat16 |
| safetensors | 0.4 | Weight loading |
| rayon | 1.10 | Parallelism |
| serde | 1.0 | Serialization |

### Internal Dependencies (sibling repos)

| Repo | Purpose | Maturity |
|------|---------|----------|
| gamma-crown | BoundedTensor, IBP/CROWN | 20% |
| z4 | SMT verification | 10% |
| tC | C/Metal verification | 75% |

**Risk:** z4 and gamma-crown are not production-ready. Verification features may need to be optional/staged.

---

## Migration Path from model_mlx_migration

### Existing Assets to Port

| Asset | Location | Priority |
|-------|----------|----------|
| Custom Metal kernels | `tools/metal_kernels/` | HIGH |
| Whisper MLX model | `tools/whisper_mlx/` | HIGH |
| Kokoro MLX model | `tools/pytorch_to_mlx/.../kokoro.py` | HIGH |
| C++ inference engine | `src/mlx_inference_engine/` | MEDIUM |
| CosyVoice3 model | `tools/pytorch_to_mlx/.../cosyvoice3.py` | LOW |

### Migration Strategy

1. **Port custom kernels to DSL** (snake1d, adain_conv, instance_norm_style)
2. **Import model weights** via safetensors (same format)
3. **Bridge C++ engine** for gradual migration (can call either)
4. **Validate** numerical equivalence with gamma-crown

---

## Success Criteria

| Criterion | Target | Measurement |
|-----------|--------|-------------|
| Dispatch overhead | <100μs | Benchmark vs MLX ~1ms |
| Throughput | ≥MLX | tok/s, RTF for TTS |
| Verification | All kernels bounded | gamma-crown passes |
| Portability | M1, M4, iPhone | Same model runs everywhere |
| AI-native | No Metal expertise needed | AI writes DSL, not MSL |

---

## Open Questions

1. **How deep should verification go?** Compile-time only? Runtime checks? Both?
2. **ANE op coverage** - Which ops are actually worth sending to ANE vs just using Metal?
3. **z4/gamma-crown maturity** - Should verification be optional feature flag initially?
4. **CoreML integration** - Direct ANE access vs CoreML wrapper?
5. **Python bindings** - PyO3 priority relative to Swift?

---

## References

- gamma-crown: `~/gamma-crown/` or `github.com/dropbox/gamma-crown`
- model_mlx_migration: `~/model_mlx_migration/`
- tC: `~/tC/`
- MLX: https://github.com/ml-explore/mlx
- Metal Best Practices: https://developer.apple.com/metal/
