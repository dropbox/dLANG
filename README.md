# dLANG - Verified Compilers

![Status](https://img.shields.io/badge/status-preview-orange)
![License](https://img.shields.io/badge/license-Apache%202.0-blue)

Verified compiler tooling.

*All d* projects are entirely AI generated.*

## Thesis

**Compilation should be proof.** Every runtime check is an admission that the compiler didn't do its job. These compilers generate code with machine-checkable correctness guarantees—memory safety, bounds checking, invariant preservation—all verified at compile time, not hoped for at runtime. When tRust compiles, you don't just get a binary; you get a proof.

## Projects

| Project | Description | Status |
|---------|-------------|--------|
| **tRust** | Trusted Rust. Compilation = proof. Transpiles to verified Rust with z4 backend. | Preview |
| **tSwift** | Trusted Swift. Same approach for iOS/macOS. Coordinates FFI with tRust. | Preview |
| **tC** | Trusted C. ACSL specs + Clang translation validation. | Preview |
| **tcore** | Shared verification core for tRust/tSwift/tC ecosystem. | Planned |
| **rustc-index-verified** | Formally verified rustc_index. Proving Rust compiler internals correct. | Preview |
| **mly** | Verified PyTorch for Apple Silicon. tRust code, gamma-crown NN verification. | Planned |

## License

Apache 2.0 - See [LICENSE](LICENSE) for details.

## Release History

See [RELEASES.md](RELEASES.md) for version history.
