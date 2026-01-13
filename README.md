# dLANG - Verified Compilers

Verified compiler tooling from Dropbox.

## Thesis

Compilation should be proof. These compilers don't just generate code—they generate code with machine-checkable guarantees. No runtime checks needed when the compiler proves correctness at build time.

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
