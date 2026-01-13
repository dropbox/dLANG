# tC: Trusted C - Design Document

**Author:** Claude (AI Worker) + Andrew Yates
**Date:** 2026-01-02
**Status:** DRAFT
**Related:** tRust, tSwift, VC IR, z4, kani_fast, lean5

---

## Executive Summary

tC is a verification layer for C code that acts as the **verified interop hub** between tRust and tSwift. Unlike CompCert (which replaces the compiler), tC verifies source code and validates compilation while preserving full Clang/GCC optimization.

**One-liner:** *Verify the source, validate the compilation, keep the performance.*

**Key Insights:**
1. C is the lingua franca of systems interop. Swift calls C, Rust calls C. Verify C boundaries for **transitive verification**: Swift ↔ C ↔ Rust.
2. Translation validation proves each compilation correct without sacrificing optimizations.

---

## Design Goals

| Goal | Rationale |
|------|-----------|
| **Preserve Performance** | CompCert's verified compiler is slower than Clang/GCC. We verify source, not compilation. |
| **Share VC IR** | Same backend infrastructure as tRust/tSwift enables unified verification. |
| **FFI Hub** | Verify contracts at language boundaries: tSwift↔tC and tRust↔tC. |
| **Incremental Adoption** | Legacy C code gets `assumed` trust; new code can be verified. |
| **Industry Standard Specs** | Support ACSL (Frama-C's spec language) for compatibility. |

---

## Architecture

```
                    ┌─────────────────────────────────────────────┐
                    │               Source Languages              │
                    │                                             │
                    │   ┌───────┐    ┌───────┐    ┌───────┐      │
                    │   │ Swift │    │  C    │    │ Rust  │      │
                    │   │ (SIL) │    │ (AST) │    │ (MIR) │      │
                    │   └───┬───┘    └───┬───┘    └───┬───┘      │
                    │       │            │            │          │
                    └───────┼────────────┼────────────┼──────────┘
                            │            │            │
                            ▼            ▼            ▼
                    ┌───────────────────────────────────────────┐
                    │              VC IR (Shared)               │
                    │                                           │
                    │  • Predicates, Effects, Temporal          │
                    │  • Trust Levels (Verified/Assumed/Audited)│
                    │  • FFI Contract Verification              │
                    └─────────────────────┬─────────────────────┘
                                          │
                    ┌─────────────────────┼─────────────────────┐
                    │                     │                     │
                    ▼                     ▼                     ▼
              ┌──────────┐        ┌──────────────┐       ┌──────────┐
              │    z4    │        │  kani_fast   │       │  lean5   │
              │   (SMT)  │        │    (BMC)     │       │ (Proofs) │
              └──────────┘        └──────────────┘       └──────────┘
```

---

## What tC IS and IS NOT

### tC IS:
- **A verification tool** that analyzes C source code
- **A spec parser** that extracts contracts from ACSL annotations or attributes
- **An FFI verifier** that checks Swift/C and Rust/C boundaries
- **A VC IR generator** that feeds our shared backend infrastructure

### tC IS NOT:
- **A replacement for Clang/GCC** - We verify, they compile
- **CompCert** - We don't prove the compiler correct; we prove the source correct
- **A complete Frama-C replacement** - We focus on verification, not full static analysis

---

## Prior Art Analysis

### CompCert
- **Approach:** Verified C compiler written/proven in Coq
- **Strength:** Guarantees compilation doesn't introduce bugs
- **Weakness:** Slower than Clang/GCC, limited optimizations
- **Our Take:** Don't replace compiler; verify source instead

### VST (Verified Software Toolchain)
- **Approach:** Separation logic proofs for C on top of CompCert
- **Strength:** Machine-checked proofs of functional correctness
- **Weakness:** Requires Coq expertise, manual proof effort
- **Our Take:** Use automated SMT/BMC instead of manual proofs

### Frama-C
- **Approach:** Plugin-based C analysis platform with WP/Eva plugins
- **Strength:** ACSL spec language is well-designed, good tooling
- **Weakness:** Not integrated with Rust/Swift, separate ecosystem
- **Our Take:** Support ACSL syntax, integrate with our ecosystem

---

## Specification Language

tC supports two specification syntaxes:

### 1. ACSL-style (Frama-C compatible)

```c
/*@ requires \valid(buf + (0..len-1));
    requires len > 0;
    ensures \result >= 0 ==> \result < len;
    ensures \result >= 0 ==> buf[\result] == target;
    ensures \result < 0 ==> (\forall integer i; 0 <= i < len ==> buf[i] != target);
*/
int find(int *buf, int len, int target);
```

### 2. Attribute-style (consistent with tRust/tSwift)

```c
__attribute__((requires("valid_range(buf, len)")))
__attribute__((requires("len > 0")))
__attribute__((ensures("result >= 0 ? buf[result] == target : true")))
int find(int *buf, int len, int target);
```

Both syntaxes lower to the same VC IR representation.

---

## C → VC IR Translation

### Phase 1: Parse C with Clang

Use libclang to parse C into Clang AST. This ensures:
- Full C11/C17 support
- Same parsing as actual compilation
- Access to type information

### Phase 2: Extract Specifications

```c
// Input: ACSL comment or __attribute__
/*@ requires x > 0; ensures \result == x * 2; */
int double_it(int x) { return x + x; }

// Output: FunctionSpec
FunctionSpec {
    name: "double_it",
    requires: [Predicate::Gt(Var("x"), Int(0))],
    ensures: [Predicate::Eq(Var("result"), Mult(Var("x"), Int(2)))],
}
```

### Phase 3: Generate VC IR

```rust
// Generated VC IR (in Rust, shared with tRust)
FunctionVcs {
    name: "double_it",
    requires: vec![VerificationCondition {
        condition: VcKind::Predicate(x > 0),
        ..
    }],
    ensures: vec![VerificationCondition {
        condition: VcKind::Predicate(result == x * 2),
        ..
    }],
}
```

### Phase 4: Verify with Backends

- z4 for decidable arithmetic, arrays, bitvectors
- kani_fast for bounded model checking
- lean5 for complex proofs requiring induction

---

## FFI Verification: The Core Feature

### Swift ↔ C

Swift calls C directly through bridging headers.

```swift
// Swift side (tSwift)
@requires("!buffer.isEmpty")
@ensures("result != nil ? result!.pointee != 0 : true")
func findNonZero(_ buffer: UnsafeBufferPointer<Int32>) -> UnsafePointer<Int32>?
```

```c
// C side (tC)
/*@ requires \valid(buf + (0..len-1));
    requires len > 0;
    ensures \result != NULL ==> *\result != 0;
*/
int32_t* find_non_zero(int32_t* buf, size_t len);
```

**Verification conditions:**
1. Swift precondition implies C precondition
2. C postcondition implies Swift postcondition
3. Type layouts match (size, alignment)

### Rust ↔ C

Rust calls C through `extern "C"` and `#[link]`.

```rust
// Rust side (tRust)
#[requires(buf.len() > 0)]
#[ensures(result.is_some().implies(buf[result.unwrap()] != 0))]
fn find_non_zero(buf: &[i32]) -> Option<usize> {
    let ptr = unsafe { ffi::find_non_zero(buf.as_ptr(), buf.len()) };
    // ...
}

extern "C" {
    fn find_non_zero(buf: *const i32, len: usize) -> *const i32;
}
```

```c
// C side (tC)
/*@ requires \valid(buf + (0..len-1));
    requires len > 0;
    ensures \result != NULL ==> *\result != 0;
*/
int32_t* find_non_zero(int32_t* buf, size_t len);
```

**Verification conditions:**
1. Rust precondition implies C precondition
2. C postcondition implies Rust postcondition
3. Pointer safety: Rust slice → C pointer is valid
4. No undefined behavior in the C implementation

---

## Trust Levels (Shared with tRust/tSwift)

```c
// Fully verified - must prove all specs
__attribute__((trust_level("verified")))
int verified_function(int x);

// Assumed correct - no verification
__attribute__((trust_level("assumed")))
int legacy_function(int x);

// Audited - specs trusted without proof
__attribute__((trust_level("audited")))
int third_party_function(int x);
```

---

## Build Integration

### Cargo (Rust calling C)

```toml
# Cargo.toml
[build-dependencies]
tc-verify = "0.1"

# build.rs
fn main() {
    tc_verify::verify_c_files(&["src/ffi.c"])
        .with_rust_bridge("src/ffi.rs")
        .fail_on_error()
        .run();
}
```

### Xcode (Swift calling C)

```bash
# Build phase script
tc-verify \
    --c-files "${SRCROOT}/bridge/*.c" \
    --swift-files "${SRCROOT}/Sources/*.swift" \
    --check-ffi
```

### CMake

```cmake
find_package(tC REQUIRED)

tc_verify(
    TARGET mylib
    C_SOURCES src/impl.c
    SPECS src/specs.h
    FFI_BRIDGE rust::mylib_ffi swift::MyLibBridge
)
```

---

## Implementation Plan

### Phase 1: C Parser + Spec Extraction (2 weeks)
- Use libclang for C parsing
- Parse ACSL comments into specs
- Parse __attribute__ specs
- Generate basic VC IR

### Phase 2: VC IR Integration (1 week)
- Connect to existing tRust VC IR crate
- Implement C-specific type mappings
- Test with z4 backend

### Phase 3: FFI Verification (2 weeks)
- Implement Swift↔C contract checking
- Implement Rust↔C contract checking
- Type layout verification
- Pointer validity reasoning

### Phase 4: Build Integration (1 week)
- Cargo build.rs integration
- Xcode build phase script
- CMake module

### Phase 5: Testing & Hardening (2 weeks)
- Real-world C codebases
- FFI boundary stress tests
- Performance benchmarks

### Phase 6: Translation Validation (3 weeks)
- Integrate Alive2 for LLVM IR validation
- Build VC IR → LLVM IR semantic comparison
- Implement compilation rejection on validation failure
- Add fallback to -O0 when -O3 fails validation

---

## Translation Validation: Best of Both Worlds

### The Problem

CompCert verifies the compiler once, but:
- Limited optimizations (~80% of GCC performance)
- Massive verification effort for any compiler change
- Still has unverified components (parser, linker, assembler)

Trusting Clang/GCC is practical, but:
- Compiler bugs exist (Alive2 found hundreds in LLVM)
- For safety-critical code, "well-tested" isn't enough

### The Solution: Validate Each Compilation

```
┌─────────────────────────────────────────────────────────────────┐
│                    tC Verification Pipeline                      │
│                                                                  │
│  ┌──────────┐     ┌──────────┐     ┌──────────────────────────┐ │
│  │ C Source │────►│   tC     │────►│ Source Verified ✓        │ │
│  │ + ACSL   │     │ Verifier │     │ (specs proven correct)   │ │
│  └──────────┘     └──────────┘     └──────────────────────────┘ │
│       │                                                          │
│       ▼                                                          │
│  ┌──────────┐     ┌──────────┐     ┌──────────────────────────┐ │
│  │  Clang   │────►│ LLVM IR  │────►│ Optimized Code           │ │
│  │   -O3    │     │          │     │ (fast, but trusted?)     │ │
│  └──────────┘     └──────────┘     └──────────────────────────┘ │
│       │                │                                         │
│       │                ▼                                         │
│       │         ┌──────────────┐                                 │
│       │         │   Alive2 /   │                                 │
│       │         │  TV Module   │                                 │
│       │         └──────┬───────┘                                 │
│       │                │                                         │
│       │         ┌──────┴───────┐                                 │
│       │         ▼              ▼                                 │
│       │    ✓ Valid        ✗ Invalid                              │
│       │    (ship it)      (reject or -O0)                        │
│       ▼                                                          │
│  ┌──────────┐                                                    │
│  │ Machine  │  ← Only if translation validated                   │
│  │  Code    │                                                    │
│  └──────────┘                                                    │
└─────────────────────────────────────────────────────────────────┘
```

### What Translation Validation Checks

| Property | How Verified |
|----------|--------------|
| **Arithmetic** | Same results for all inputs |
| **Memory** | Same loads/stores, same aliasing |
| **Control Flow** | Same reachable states |
| **Undefined Behavior** | Not exploited by optimizer |

### Existing Tools We'll Leverage

| Tool | What It Does | Integration |
|------|--------------|-------------|
| **Alive2** | Validates LLVM IR transformations | Direct - already production-ready |
| **LLVM-TV** | Translation validation framework | Reference implementation |
| **CompCertSSA** | SSA validation | Techniques, not code |

### Why This Is Better Than CompCert

| Aspect | CompCert | tC + Translation Validation |
|--------|----------|----------------------------|
| **Compiler** | Custom (verified) | Clang (industry standard) |
| **Optimizations** | Limited subset | Full -O3 |
| **Performance** | ~80% of Clang | 100% of Clang |
| **Verification Cost** | Once per compiler version | Per compilation (cheap) |
| **Trust Model** | Trust verified compiler | Trust per-compilation proof |
| **Failure Mode** | N/A | Fall back to -O0 or reject |

### Build Integration

```bash
# Normal build (source verification only)
tc-verify --check src/*.c

# Full verification (source + translation validation)
tc-verify --check --validate-translation src/*.c

# CI mode (reject on any validation failure)
tc-verify --check --validate-translation --strict src/*.c
```

```cmake
tc_verify(
    TARGET mylib
    C_SOURCES src/impl.c
    TRANSLATION_VALIDATION ON      # Enable TV
    TV_FALLBACK_O0 ON              # Fall back to -O0 on failure
    TV_STRICT OFF                  # Don't fail build, just warn
)
```

---

## Key Design Decisions

### Decision 1: Don't Replace Clang

**Rationale:** CompCert proves the compiler correct but loses performance. Users won't accept 2x slower compilation and 20% slower code. By verifying source and letting Clang compile, we get both correctness and performance.

**Trade-off:** We don't verify the compiler itself. A bug in Clang could still introduce issues.

**Solution:** Translation Validation (Phase 6) closes this gap by validating each compilation. This gives us:
1. Full Clang -O3 performance
2. Per-compilation correctness proof
3. Fallback to -O0 if validation fails

### Decision 2: ACSL Compatibility

**Rationale:** ACSL is a well-designed spec language with 15+ years of evolution. Supporting it means:
- Existing Frama-C specs work
- Community familiarity
- Documentation and tools exist

**Trade-off:** ACSL has some C-specific constructs that don't map cleanly to VC IR. We support a subset.

### Decision 3: C as FFI Hub (Not Direct Swift↔Rust)

**Rationale:**
- Swift has excellent C interop (bridging headers)
- Rust has excellent C interop (bindgen, extern "C")
- Swift↔Rust direct interop is immature
- C is the universal ABI

**Verification Flow:**
```
Swift ─verify→ C ←verify─ Rust
       tSwift↔tC   tC↔tRust

By transitivity: Swift ↔ Rust verified through C
```

---

## File Structure

```
tC/
├── DESIGN.md              # This document
├── CLAUDE.md              # Worker instructions
├── Cargo.toml             # Rust crate for tc-verify
├── src/
│   ├── lib.rs             # Main library
│   ├── parser/
│   │   ├── clang.rs       # libclang integration
│   │   └── acsl.rs        # ACSL spec parser
│   ├── vc_gen/
│   │   ├── c_to_vcir.rs   # C AST → VC IR
│   │   └── types.rs       # C type mappings
│   ├── ffi/
│   │   ├── swift.rs       # Swift↔C verification
│   │   └── rust.rs        # Rust↔C verification
│   └── cli.rs             # tc-verify command
├── tests/
│   ├── basic/             # Basic C verification
│   ├── ffi/               # FFI boundary tests
│   └── acsl/              # ACSL parsing tests
└── examples/
    ├── swift_bridge/      # Swift↔C example
    └── rust_bridge/       # Rust↔C example
```

---

## Success Criteria

### Milestone 1: "Hello, Verified C"
- Parse simple C function with ACSL spec
- Generate VC IR
- Verify with z4
- Pass/fail based on spec

### Milestone 2: FFI Verification
- Verify Rust↔C boundary contract
- Verify Swift↔C boundary contract
- Detect mismatched specs at boundary

### Milestone 3: Real-World Integration
- Integrate with a real Rust/Swift project using C
- Verify 100+ functions across boundaries
- No false positives on correct code

---

## Open Questions

1. **Memory Model:** How do we handle C's complex memory model (pointer aliasing, volatile, etc.)?
   - Start simple: require restrict/const annotations for verification
   - Expand to handle more cases over time

2. **Undefined Behavior:** C has many UB cases. Which do we check?
   - Start with: null derefs, buffer overflows, integer overflow
   - Later: aliasing violations, uninitialized reads

3. **Inline Assembly:** Many C projects use inline asm.
   - Mark as `trusted` by default
   - Allow manual specs for asm blocks

4. **Preprocessor:** Specs before or after preprocessing?
   - After preprocessing (analyze what compiler sees)
   - But preserve source locations for error messages

---

## References

- [CompCert](https://compcert.org/) - Verified C compiler
- [VST](https://vst.cs.princeton.edu/) - Verified Software Toolchain
- [Frama-C](https://frama-c.com/) - C analysis platform
- [ACSL](https://frama-c.com/acsl.html) - ANSI/ISO C Specification Language
- [tRust VC IR](../tRust/vc_ir/) - Shared verification condition IR
