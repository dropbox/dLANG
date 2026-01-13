# Tensor Forge

| Director | Status |
|:--------:|:------:|
| LANG | ACTIVE |

**AI-native ML framework for Apple Silicon.**

Rust-first. Verification built-in. Maximum performance.

## Vision

Replace MLX with something better for AI agents:

| Problem with MLX | Tensor Forge Solution |
|------------------|----------------------|
| ~1ms dispatch overhead | <100μs target |
| Python-first | Rust-first |
| Write Metal directly | High-level DSL |
| No verification | gamma-crown built-in |

## Quick Example

```rust
// AI writes this:
#[kernel]
fn snake1d(x: Tensor<f32>, alpha: Tensor<f32>) -> Tensor<f32> {
    let sin_val = (alpha * x).sin();
    x + (1.0 / alpha) * sin_val * sin_val
}

// Framework generates optimal Metal/ANE/CPU code
// gamma-crown proves numerical bounds
```

## Architecture

```
mly/
├── mly-core      # Tensor, Shape, Device, Bounds
├── mly-dsl       # #[kernel] DSL → IR → codegen
├── mly-metal     # Metal GPU backend
├── mly-ane       # Apple Neural Engine
├── mly-cpu       # ARM NEON SIMD
├── mly-runtime   # Adaptive dispatch
├── mly-verify    # gamma-crown integration
├── mly-mlx       # MLX model import
└── mly-swift     # Swift bindings
```

## Status

**MVP initialized.** Ready for Phase 0 implementation.

See `TENSOR_FORGE_PLAN.md` for detailed roadmap.

## Building

```bash
cargo build
cargo test
```

## License

MIT OR Apache-2.0
