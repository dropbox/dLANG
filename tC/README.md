# tC: Trusted C

| Director | Status |
|:--------:|:------:|
| LANG | ACTIVE |

**C verification layer bridging tRust↔tSwift with ACSL specs and per-compilation translation validation.**

> *Verify the source, validate the compilation, keep the performance.*

**Author:** Andrew Yates
**Copyright:** 2026 Dropbox, Inc.
**License:** Apache 2.0

---

## tC is NOT a Compiler

Despite the similar naming, **tC is fundamentally different from tRust and tSwift**:

| Project | What it is | Compiles code? |
|---------|------------|----------------|
| **tRust** | Fork of rustc (Rust compiler) | Yes - Rust → binary |
| **tSwift** | Fork of swiftc (Swift compiler) | Yes - Swift → binary |
| **tC** | Verification tool (NOT a compiler) | No - just verifies |

```
tRust  = rustc  + verification    ← IS a compiler
tSwift = swiftc + verification    ← IS a compiler
tC     = verification tool        ← NOT a compiler, works WITH Clang/GCC
```

### Why the difference?

- **Rust/Swift**: One compiler each (rustc, swiftc). Must fork to add verification.
- **C**: Multiple compilers (GCC, Clang, MSVC). Users won't switch. Forking is impractical (GCC = 15M lines, CompCert took 10 years).

**tC's approach**: Verify source code externally, let Clang/GCC compile it, optionally validate the compilation.

---

## What tC Does

```
┌─────────────────────────────────────────────────────────────────┐
│  Your C code                                                    │
│  (with ACSL specs)                                              │
│       │                                                         │
│       ├────────────► tC ────────────► ✓ Verified (or ✗ error)  │
│       │           (verification)                                │
│       │                                                         │
│       └────────────► Clang -O3 ─────► binary                   │
│                    (compilation)         │                      │
│                                          │                      │
│                    Alive2 ◄──────────────┘                      │
│                (validates compilation)                          │
└─────────────────────────────────────────────────────────────────┘
```

1. **Verifies source code** against ACSL specifications
2. **Validates compilation** using translation validation (Alive2)
3. **Checks FFI boundaries** between Swift↔C and Rust↔C
4. **Preserves performance** - full Clang -O3 optimization

---

## Why Not Fork Clang/GCC?

| | Fork Clang | tC approach |
|---|------------|-------------|
| **Codebase** | 3M+ lines C++ | ~10K lines Rust |
| **Maintenance** | Track every Clang release | Decoupled |
| **Performance** | Must re-verify optimizations | Use Clang's optimizations |
| **User adoption** | Must switch compilers | Works with any compiler |
| **Precedent** | CompCert: 10 years, 80% perf | - |

**Translation validation** gives us the best of both worlds: full Clang performance + per-compilation correctness proof.

---

## The tRust/tSwift/tC Family

All three share **VC IR** and verification backends, but differ in implementation:

```
tRust (compiler)     tSwift (compiler)      tC (tool)
      │                    │                    │
      ▼                    ▼                    ▼
     MIR                  SIL               Clang AST
      │                    │                    │
      └────────────────────┼────────────────────┘
                           │
                           ▼
                        VC IR (shared)
                           │
                           ▼
                   z4 / kani / lean5
```

**tC is the FFI hub**: Swift calls C, Rust calls C. Verify C boundaries for transitive Swift↔Rust trust.

---

## Quick Start

```bash
# Verify a C file with ACSL specs
tc-verify verify example.c

# Check FFI boundary with Rust
tc-verify ffi-check --c bridge.c --rust bridge.rs

# Full pipeline with translation validation
tc-verify verify --translate-validate example.c
```

## Example

```c
/*@ requires \valid(buf + (0..len-1));
    requires len > 0;
    ensures \result >= 0 ==> buf[\result] == target;
*/
int find(int *buf, int len, int target) {
    for (int i = 0; i < len; i++) {
        if (buf[i] == target) return i;
    }
    return -1;
}
```

```bash
$ tc-verify verify find.c
Parsing find.c... OK
Extracting ACSL specs... 1 function
Generating VC IR... 3 verification conditions
Verifying with z4...
  ✓ Precondition valid
  ✓ Loop invariant maintained
  ✓ Postcondition proven
Result: VERIFIED

$ clang -O3 find.c -o find    # Compile separately with any compiler
```

---

## Documentation

- [DESIGN.md](docs/DESIGN.md) - Architecture and design decisions
- [CLAUDE.md](CLAUDE.md) - AI worker instructions

## Sister Projects

| Project | Type | Description |
|---------|------|-------------|
| [tRust](https://github.com/dropbox/tRust) | Compiler | Rust compiler with built-in verification |
| [tSwift](https://github.com/dropbox/tSwift) | Compiler | Swift compiler with built-in verification |
| [tC](https://github.com/dropbox/dLANG/tC) | Tool | C verification tool (this project) |
| [z4](https://github.com/dropbox/z4) | Backend | SMT solver for all three |

## License

Apache 2.0 - see [LICENSE](LICENSE) for details.
