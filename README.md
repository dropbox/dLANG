# dLANG - Verified Compilers

![Status](https://img.shields.io/badge/status-preview-orange)
![License](https://img.shields.io/badge/license-Apache%202.0-blue)

Verified compiler tooling from Dropbox.

## Thesis

**Compilation should be proof.** Every runtime check is an admission that the compiler didn't do its job. These compilers generate code with machine-checkable correctness guarantees—memory safety, bounds checking, invariant preservation—all verified at compile time, not hoped for at runtime. When tRust compiles, you don't just get a binary; you get a proof.

## Projects

| Project | Description | Status |
|---------|-------------|--------|
| **tRust** | Trusted Rust. Compilation = proof. Transpiles to verified Rust with z4 backend. | Planned |
| **tSwift** | Trusted Swift. Same approach for iOS/macOS. Coordinates FFI with tRust. | Planned |
| **tC** | Trusted C. ACSL specs + Clang translation validation. | Planned |
| **tcore** | Shared verification core for tRust/tSwift/tC ecosystem. | Planned |
| **rustc-index-verified** | Formally verified rustc_index. Proving Rust compiler internals correct. | Planned |
| **tensor-forge** | Verified tensor ops for Apple Silicon. | Planned |

## License

Apache 2.0 - See [LICENSE](LICENSE) for details.

## Release History

See [RELEASES.md](RELEASES.md) for version history.
