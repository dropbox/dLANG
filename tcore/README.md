# tcore (Trust Core)

| Director | Status |
|:--------:|:------:|
| LANG | ACTIVE |

**The foundation for verified software.**

tcore is the shared verification infrastructure that powers the t[LANG] family of verified compilers (tRust, tSwift, tC). It provides the common IR, SMT solver, and proof backends that make "if it compiles, it's proven" possible.

**Author:** Andrew Yates
**Copyright:** 2026 Dropbox, Inc.
**License:** Apache 2.0

---

## Vision

**If it compiles, it's proven.**

The t[LANG] system makes verification the default for mainstream languages. No separate tools. No opt-in. Compilation IS verification.

### The AI Trust Problem

| AI Strength | AI Weakness |
|-------------|-------------|
| Write small, focused code | Monitor running systems |
| Write formal proofs | Scan huge codebases for side effects |
| Reason locally | Track global runtime behavior |

**Solution:** Move verification to compile time where AI can participate effectively.

```
AI writes:              tcore verifies:           Result:
─────────────────────────────────────────────────────────────
• Code                  • Auto-VCs                PROVEN
• Contracts             • Contract satisfaction   or
• Lean proofs           • Proof validity          REJECTED + why
```

**AI doesn't need to be trusted. The compiler verifies mechanically.**

---

## Architecture

```
                         tcore
                           │
          ┌────────────────┼────────────────┐
          │                │                │
          ▼                ▼                ▼
    ┌───────────┐    ┌───────────┐    ┌───────────┐
    │    Z4     │    │   Kani    │    │   Lean    │
    │           │    │           │    │           │
    │ Automatic │    │ Bounded   │    │ AI writes │
    │ SMT       │    │ model     │    │ proof,    │
    │ solving   │    │ checking  │    │ Lean      │
    │           │    │           │    │ checks it │
    └───────────┘    └───────────┘    └───────────┘
          ▲                ▲                ▲
          │                │                │
          └────────────────┼────────────────┘
                           │
         ┌─────────────────┼─────────────────┐
         │                 │                 │
         ▼                 ▼                 ▼
      tRust             tSwift              tC
    (Rust MIR)        (Swift SIL)       (LLVM IR)
```

### Components

| Component | Purpose |
|-----------|---------|
| `tcore-ir` | Verification Condition IR - common format all languages translate to |
| `tcore-z4` | SMT solver for automatic proofs |
| `tcore-kani` | Bounded model checking backend (future) |
| `tcore-lean` | Interactive theorem prover for complex proofs (future) |

---

## Ecosystem

tcore is the foundation. Language-specific tools depend on it:

```
~/tcore/              # This repo - shared infrastructure
├── ir/               # Verification Condition IR
├── z4/               # SMT solver
└── backends/         # kani, lean (future)

~/tRust/              # Rust verification (depends on tcore)
├── bin/trustv        # Rust verifier
└── bin/trustc        # Rust compiler

~/tSwift/             # Swift verification (depends on tcore)
├── bin/tswiftv       # Swift verifier
└── bin/tswiftc       # Swift compiler

~/tC/                 # C verification (depends on tcore)
├── bin/tcv           # C verifier
└── bin/tcc           # C compiler

~/tbridge/            # FFI verification (depends on tcore)
└── bin/tbridge       # Cross-language verification
```

---

## Tool Naming Convention

| Suffix | Tool Type | tRust | tC | tSwift |
|--------|-----------|-------|-----|--------|
| `-v` | Verifier | `trustv` | `tcv` | `tswiftv` |
| `-c` | Compiler | `trustc` | `tcc` | `tswiftc` |
| `-lsp` | Language Server | `trust-lsp` | `tc-lsp` | `tswift-lsp` |
| `-lint` | Contract Linter | `trustlint` | `tclint` | `tswiftlint` |
| `-doc` | Doc Generator | `trustdoc` | `tcdoc` | `tswiftdoc` |

---

## Status

| Component | Status |
|-----------|--------|
| tcore-ir | Extracting from tRust |
| tcore-z4 | Extracting from tRust |
| tcore-kani | Planned |
| tcore-lean | Planned |

---

## Related Projects

- [tRust](https://github.com/dropbox/tRust) - Verified Rust compiler
- [tSwift](https://github.com/dropbox/tSwift) - Verified Swift compiler
- tC - Verified C compiler (planned)
- tbridge - FFI verification (planned)

---

## License

Apache 2.0 - See [LICENSE](LICENSE)
