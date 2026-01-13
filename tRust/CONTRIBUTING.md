# Contributing to tRust

Thank you for your interest in contributing to tRust! This guide covers the development workflow for contributors.

## Development Setup

### Prerequisites

- **Rust 1.75+**: `rustup update stable`
- **CMake and Ninja**: `brew install cmake ninja` (macOS) or equivalent
- **Git submodules**: Run `git submodule update --init --recursive`

### Building

```bash
# Build the stage 1 compiler
./rebuild.sh

# This produces ./bin/trustc
```

### Pre-commit Hook

Install the pre-commit hook to catch issues before committing:

```bash
./scripts/install-hooks.sh
```

The hook runs:
1. Submodule SHA validation (ensures submodules are pushed)
2. `rustc_vc` build check
3. Workspace unit tests (~1,316 tests)

Skip with `TRUST_SKIP_HOOKS=1` for emergency commits.

## Testing

### Running Tests

```bash
# Integration tests (examples/*_test.rs)
./run_tests.sh

# Unit tests
cargo test --workspace

# Clippy
cargo clippy --workspace

# Documentation tests (book)
cd book && mdbook test
```

### Test Format

**Single-file tests**: `examples/*_test.rs`
- Compiled with `-Zverify`
- Expected outcomes specified via comments (`// @expect: VERIFIED`, `// @expect: DISPROVEN`, etc.)

> **Note**: Integration tests require `-Zverify` flag which is not yet implemented in the stage1 compiler. Run unit tests with `cargo test --workspace` (~1,316 tests) to verify the VC infrastructure.

**Cross-crate tests**: `examples/*_crate_case/`
- Multi-file tests with `dep.rs` (dependency) and `main.rs` (consumer)
- Tests cross-crate contract verification

### Adding Tests

1. Create `examples/your_feature_test.rs`
2. Add expected outcome comment: `// @expect: VERIFIED`
3. Run `./run_tests.sh` to verify the test passes

## Code Style

- Run `cargo clippy --workspace` before committing
- Fix all warnings to maintain code quality
- Use standard Rust formatting (`cargo fmt`)
- Follow existing patterns in the codebase

## Project Structure

```
tRust/
  bin/trustc           # Main compiler wrapper
  compiler/rustc_vc/   # Verification condition generation
  vc_ir/               # Verification Condition IR (backend-agnostic)
  backends/z4/         # Z4 SMT solver bindings
  deps/kani_fast/      # CHC-optimized Kani fork
  proofs/lean5/        # Formal soundness proofs (Lean5)
  trust_macros/        # Procedural macros for specs
  crates/tla-extract/  # TLA+ temporal logic extraction
  examples/            # Integration tests
  book/                # User documentation (mdbook)
  docs/                # Internal documentation
```

### Key Components

| Component | Location | Purpose |
|-----------|----------|---------|
| Verification core | `compiler/rustc_vc/src/verify.rs` | Main verification logic |
| VC IR | `vc_ir/src/` | Backend-agnostic verification condition representation |
| Weakest precondition | `compiler/rustc_vc/src/weakest_precondition.rs` | WP calculus implementation |
| Spec encoding | `compiler/rustc_vc/src/encoder.rs` | SMT encoding of specs |
| CHC solving | `deps/kani_fast/crates/kani-fast-chc/` | Loop invariant synthesis |
| SMT backend | `backends/z4/` | Z4 solver integration |
| Formal proofs | `proofs/lean5/MirSemantics/` | Soundness proofs in Lean5 |

## Pull Requests

1. Fork the repository
2. Create a feature branch: `git checkout -b feature/my-feature`
3. Make your changes with tests
4. Ensure all tests pass: `./run_tests.sh && cargo test --workspace`
5. Commit with a descriptive message
6. Push and create a pull request

### Commit Message Format

```
Short summary (50 chars max)

Longer description if needed. Explain what and why,
not how (the code shows how).

Fixes #123
```

## Reporting Issues

When reporting bugs:

1. Include the Rust code that triggers the issue
2. Include the exact command run (e.g., `./bin/trustc --no-cache file.rs`)
3. Include the full output (verification messages, errors)
4. Include your environment (`rustc --version`, OS)

## Architecture Overview

tRust extends rustc with verification:

1. **Parse specs**: Custom attributes `#[requires]`, `#[ensures]` etc. are parsed
2. **Generate VCs**: MIR is analyzed to generate verification conditions
3. **Solve**: Z4/Z3 SMT solvers prove or disprove VCs
4. **Report**: Results integrated into compiler diagnostics

For detailed architecture, see:
- `docs/ARCHITECTURE_INTENT.md`
- `docs/VERIFIED_COMPILER_VISION.md`
- `ROADMAP.md`

## Questions

- Check existing documentation in `docs/` and `book/`
- Review `docs/GETTING_STARTED.md` for user-facing features
- Open an issue for questions not covered

## License

Contributions are subject to the project's license. By contributing, you agree to license your contributions under the same terms.
