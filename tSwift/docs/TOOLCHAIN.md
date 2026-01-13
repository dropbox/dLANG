# t[LANG] Toolchain Specification

**Version:** 1.0
**Date:** 2026-01-03
**Applies to:** tRust, tC, tSwift (and future t[LANG] projects)

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
AI writes:              t[LANG] verifies:         Result:
─────────────────────────────────────────────────────────────
• Code                  • Auto-VCs                PROVEN
• Contracts             • Contract satisfaction   or
• Lean proofs           • Proof validity          REJECTED + why
```

**AI doesn't need to be trusted. The compiler verifies mechanically.**

### Proof Backends

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
    │ "Easy"    │    │ "Finite"  │    │ "Hard"    │
    └───────────┘    └───────────┘    └───────────┘
```

When Z4 returns UNKNOWN, AI can write a Lean proof. The proof is mechanically verified - no trust required.

### Role in AI Singularity

```
AI writes verified tools (using t[LANG])
              │
              ▼
Verified tools help AI write better code
              │
              ▼
AI uses better tools to write more verified tools
              │
              ▼
Each iteration: more capability, same trust level (PROVEN)
```

The verification system is infrastructure for AI to build reliable software at scale.

---

## Overview

The t[LANG] family provides formal verification tooling for multiple languages, sharing a common architecture and naming convention.

```
┌─────────────────────────────────────────────────────────────┐
│                      Applications                            │
└──────────┬──────────────────┬──────────────────┬────────────┘
           │                  │                  │
           ▼                  ▼                  ▼
    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
    │   tSwift    │    │    tRust    │    │     tC      │
    │   (Swift)   │    │   (Rust)    │    │   (C/C++)   │
    └──────┬──────┘    └──────┬──────┘    └──────┬──────┘
           │                  │                  │
           └────────────┬─────┴─────┬────────────┘
                        │           │
                        ▼           ▼
                 ┌─────────┐  ┌──────────┐
                 │ tbridge │  │  VC IR   │
                 │  (FFI)  │  │ (shared) │
                 └─────────┘  └────┬─────┘
                                   │
                              ┌────┴────┐
                              │   Z4    │
                              │   SMT   │
                              └─────────┘
```

---

## Naming Convention

### Pattern: `t[LANG][suffix]`

### Complete Tool Matrix

| Suffix | Tool Type | tRust | tC | tSwift | Purpose |
|--------|-----------|-------|-----|--------|---------|
| `-v` | Verifier | `trustv` | `tcv` | `tswiftv` | Standalone verification, JSON output, suggestions |
| `-c` | Compiler | `trustc` | `tcc`* | `tswiftc` | Compile with verification (drop-in replacement) |
| `-lsp` | Language Server | `trust-lsp` | `tc-lsp` | `tswift-lsp` | IDE integration, real-time verification feedback |
| `-lint` | Contract Linter | `trustlint` | `tclint` | `tswiftlint` | Contract hygiene, suggest missing specs, syntax check |
| `-doc` | Doc Generator | `trustdoc` | `tcdoc` | `tswiftdoc` | Extract contracts to API docs, verification reports |

*Note: `tcc` collides with Tiny C Compiler; acceptable given different installation contexts.

### Cross-Language Tools

| Tool | Purpose |
|------|---------|
| `tbridge` | FFI verification across language boundaries |

### Shared Infrastructure: tcore (Trust Core)

| Component | Location | Purpose |
|-----------|----------|---------|
| `tcore` | `~/tcore/` | Shared verification infrastructure |
| `tcore-ir` | `~/tcore/ir/` | Verification Condition IR |
| `tcore-z4` | `~/tcore/z4/` | SMT solver backend |
| `tcore-kani` | `~/tcore/backends/kani/` | Bounded model checking (future) |
| `tcore-lean` | `~/tcore/backends/lean/` | Interactive theorem prover (future) |

**tcore** is the Trust Core - the foundation all t[LANG] projects build on. Lives in its own repo so AI agents can work independently.

Currently lives in `~/tRust/vc_ir/` - to be extracted to `~/tcore/`.

### Repository Structure

```
~/tcore/              # Trust Core - shared verification infrastructure
├── ir/               # Verification Condition IR
├── z4/               # SMT solver
└── backends/         # kani, lean (future)

~/tRust/              # Rust verification (depends on tcore)
├── bin/
│   ├── trustv        # Rust verifier
│   └── trustc        # Rust compiler
└── ...

~/tSwift/             # Swift verification (depends on tcore)
├── bin/
│   ├── tswiftv       # Swift verifier
│   └── tswiftc       # Swift compiler
└── ...

~/tC/                 # C verification (depends on tcore)
├── bin/
│   ├── tcv           # C verifier
│   └── tcc           # C compiler
└── ...

~/tbridge/            # Cross-language FFI verification (depends on tcore)
└── bin/
    └── tbridge
```

Dependency graph:
```
           tcore
             │
    ┌────────┼────────┐
    │        │        │
    ▼        ▼        ▼
  tRust   tSwift     tC
    │        │        │
    └────────┼────────┘
             │
             ▼
          tbridge
```

Each repo is independently owned. AI agents work on one repo at a time without conflicts.

### Tool Descriptions

#### Verifier (`t[LANG]v`)
Standalone verification tool. Parses source/IR, extracts contracts, generates Auto-VCs, proves via SMT, reports results with counterexamples and fix suggestions. JSON internally, pretty-print for TTY.

#### Compiler (`t[LANG]c`)
Drop-in replacement for standard compiler. Runs verification first; if it passes, compiles normally. Accepts all standard compiler flags. Can be wrapper (current) or fork (future).

#### Language Server (`t[LANG]-lsp`)
IDE integration via LSP protocol. Provides real-time verification errors as diagnostics, hover info with inferred contracts, code actions for fixes, inline counterexamples.

#### Contract Linter (`t[LANG]lint`)
Static analysis for contract hygiene (not bug-finding—that's the verifier). Warns about missing contracts, malformed specs, suggests proof strategies, checks contract syntax.

#### Doc Generator (`t[LANG]doc`)
Extracts contracts into API documentation. Generates verification coverage reports. Shows which functions are verified, trusted, or unverified.

#### FFI Bridge (`tbridge`)
Verifies contracts match across language boundaries. Ensures Swift's `@_requires` matches Rust's `#[requires]`, type mappings are correct, memory safety preserved across FFI.

### Standard Tools (No t[LANG] Version Needed)

| Tool | Use instead |
|------|-------------|
| `t[LANG]fmt` | Standard formatters (`rustfmt`, `swift-format`, `clang-format`) |

### Verification vs Traditional Tools

**Verification replaces bug-finding lint** - the verifier catches bugs with mathematical certainty, not heuristics. Traditional linters find "maybe bugs"; verification proves actual bugs exist.

| What | Traditional linter | Verifier |
|------|-------------------|----------|
| Force unwrap of nil | "Warning: force unwrap detected" | "FAILED: nil possible. Counterexample: x = nil" |
| Array out of bounds | "Warning: unchecked index" | "FAILED: bounds violation. Counterexample: i = -1" |
| Dead code | Sometimes detected | Proven unreachable |

**Verification does NOT replace:**
- Style checking (naming conventions, formatting) → use `swift-format`, `swiftlint`
- Complexity metrics (function length, cyclomatic complexity) → use standard linters

### Potential Future Tools

| Tool | Purpose | When needed |
|------|---------|-------------|
| `t[LANG]lint` | Contract hygiene linting | Recommend missing contracts, check contract syntax, suggest proof strategies |
| `t[LANG]doc` | Contract-aware documentation | Extract contracts into API docs, generate verification reports |

These would extend (not replace) standard tools:
- `tswiftlint` could warn: "Function `foo` calls `bar` which has @requires, but `foo` has no contract"
- `tswiftdoc` could generate: API docs with contracts inline, coverage reports of what's verified

---

## Verifier Specification (`t[LANG]v`)

### Purpose

The verifier is the core tool. It:
1. Parses source code (or IR)
2. Extracts contracts (`@requires`, `@ensures`, etc.)
3. Generates automatic verification conditions (Auto-VCs)
4. Proves or disproves each condition via SMT solver
5. Reports results with counterexamples and suggestions

### Output Design

**Principle: JSON internally, pretty-print for humans.**

```
┌─────────────────────────────────────────────────┐
│              t[LANG]v internals                  │
│                                                  │
│  Verification → VerificationResult (JSON)        │
│                    │                             │
│         ┌─────────┴─────────┐                   │
│         │                   │                   │
│         ▼                   ▼                   │
│    TTY detected?      Piped/redirected?         │
│         │                   │                   │
│         ▼                   ▼                   │
│   Pretty output        Raw JSON                 │
│   (colors, icons)      (for AI/tools)           │
└─────────────────────────────────────────────────┘
```

### Output Always Includes

Every verification result contains:

| Field | Description |
|-------|-------------|
| `status` | `verified`, `failed`, `unknown`, `trusted` |
| `location` | File, line, column, function name |
| `vc_type` | What was checked (overflow, bounds, contract, etc.) |
| `counterexample` | Concrete values that violate the condition (if failed) |
| `suggestions` | How to fix the failure |

**Suggestions are not optional.** The point of t[LANG]v is to help write verified code.

### JSON Schema

```json
{
  "file": "main.swift",
  "results": [
    {
      "function": "divide",
      "location": { "line": 5, "column": 12 },
      "status": "failed",
      "vc_type": "div_by_zero",
      "message": "Division by zero possible",
      "counterexample": {
        "a": 42,
        "b": 0
      },
      "suggestions": [
        {
          "type": "add_requires",
          "code": "@_requires(\"b != 0\")",
          "explanation": "Require caller to ensure b is non-zero"
        },
        {
          "type": "add_guard",
          "code": "guard b != 0 else { return 0 }",
          "explanation": "Handle zero case explicitly"
        }
      ]
    }
  ],
  "summary": {
    "verified": 5,
    "failed": 1,
    "unknown": 0,
    "trusted": 2
  }
}
```

### Pretty Output (TTY)

```
=== main.swift ===

  ✓ add (line 2) - verified
  ✓ multiply (line 8) - verified
  ✗ divide (line 14) - FAILED

    div by zero: b can be 0
    Counterexample: a = 42, b = 0

    Fix options:
      1. Add precondition:
         @_requires("b != 0")

      2. Add guard:
         guard b != 0 else { return 0 }

  ⊘ trusted_func (line 20) - trusted (skipped)

Summary: 5 verified, 1 failed, 0 unknown, 2 trusted
```

### CLI Flags

| Flag | Purpose |
|------|---------|
| `--format=json` | Force JSON output |
| `--format=pretty` | Force pretty output |
| `--quiet` | Exit code only (for CI) |
| `--verbose` | Show per-VC progress |
| (none) | Auto-detect: TTY → pretty, pipe → JSON |

---

## Compiler Specification (`t[LANG]c`)

### Purpose

The compiler is a drop-in replacement for the standard compiler that:
1. Runs verification first
2. If verification passes, compiles normally
3. If verification fails, reports errors (no output binary)

### Relationship to Standard Compiler

| Approach | Description | Status |
|----------|-------------|--------|
| **Wrapper** | Calls standard compiler, adds verification step | Current |
| **Fork** | Modified compiler with integrated verification | Future |

### CLI Compatibility

`t[LANG]c` accepts all flags of the standard compiler:

```bash
# These are equivalent (when verification passes):
tswiftc main.swift -o main
swiftc main.swift -o main

# tswiftc-specific flags:
tswiftc --no-verify main.swift    # Skip verification
tswiftc --verify-only main.swift  # Same as tswiftv
```

---

## Language Server Specification (`t[LANG]-lsp`)

### Purpose

IDE integration providing real-time verification feedback:
- Verification errors as diagnostics (red squiggles)
- Hover shows inferred contracts
- Code actions suggest fixes
- Inline display of counterexamples

### Architecture

```
┌─────────────┐     LSP Protocol     ┌─────────────┐
│    IDE      │◄───────────────────►│ t[LANG]-lsp │
│  (VS Code,  │                      │             │
│   Cursor,   │                      │  Wraps:     │
│   Xcode*)   │                      │  - t[LANG]v │
└─────────────┘                      │  - standard │
                                     │    LSP      │
                                     └─────────────┘
```

*Xcode integration requires SourceKit plugin

---

## FFI Verification (`tbridge`)

### Purpose

Verify contracts match across language boundaries:

```
┌─────────────────┐                    ┌─────────────────┐
│     tSwift      │                    │     tRust       │
│                 │                    │                 │
│ @_requires("x") │◄─── tbridge ────►│ #[requires(x)]  │
│ @_ensures("y")  │   verifies match   │ #[ensures(y)]   │
└─────────────────┘                    └─────────────────┘
```

### CLI

```bash
tbridge rust-swift ./rust_core ./swift_ui
tbridge rust-c ./rust_lib ./c_headers
tbridge swift-c ./swift_lib ./c_code
```

### What tbridge Checks

1. **Contract compatibility**: Swift's `@_requires` matches Rust's `#[requires]`
2. **Type mapping**: Types translate correctly across FFI
3. **Memory safety**: Ownership/borrowing rules respected
4. **Error handling**: Failure modes match

---

## Auto-VCs (Automatic Verification Conditions)

All t[LANG]v tools automatically check these without user annotations:

| Auto-VC | Description |
|---------|-------------|
| **Overflow** | Integer overflow/underflow |
| **DivByZero** | Division by zero |
| **BoundsCheck** | Array/buffer index in bounds |
| **NilCheck** | Null/nil/nullptr dereference |
| **CastCheck** | Type cast validity |
| **Truncation** | Integer narrowing overflow |
| **RangeBounds** | Range start ≤ end |

---

## Contract Annotations

### By Language

| Annotation | tSwift | tRust | tC |
|------------|--------|-------|-----|
| Precondition | `@_requires("...")` | `#[requires(...)]` | `__requires(...)` |
| Postcondition | `@_ensures("...")` | `#[ensures(...)]` | `__ensures(...)` |
| Invariant | `@_invariant("...")` | `#[invariant(...)]` | `__invariant(...)` |
| Skip verification | `@_trusted` | `#[trusted]` | `__trusted` |

---

## Implementation Status

### tSwift

| Tool | Status | Location |
|------|--------|----------|
| `tswiftv` | **Exists** | `bin/tswiftv` |
| `tswiftc` | Planned | Same binary, compiles+verifies |
| `tswift-lsp` | Not started | - |

### tRust

| Tool | Status | Location |
|------|--------|----------|
| `trustv` | Exists (wrapper) | `~/tRust/` |
| `trustc` | Wrapper | `~/tRust/` |
| `trust-lsp` | Not started | - |

### tC

| Tool | Status | Location |
|------|--------|----------|
| `tcv` | Not started | - |
| `tcc` | Not started | - |
| `tc-lsp` | Not started | - |

### Cross-Language

| Tool | Status |
|------|--------|
| `tbridge` | Not started |

---

## File Locations

```
~/tRust/
├── bin/
│   ├── trustv          # Rust verifier
│   └── trustc          # Rust compiler (wrapper)
├── vc_ir/              # Shared VC IR (used by all t[LANG])
└── ...

~/tSwift/
├── bin/
│   ├── tswiftv         # Swift verifier
│   └── tswiftc         # Swift compiler (wrapper)
├── vc-ir-swift/        # Swift VC IR bindings
└── ...

~/tC/
├── bin/
│   ├── tcv             # C verifier
│   └── tcc             # C compiler (wrapper)
└── ...

~/tbridge/              # Or could live in tRust
├── bin/
│   └── tbridge         # FFI verifier
└── ...
```

---

## Design Principles

1. **Suggestions are default** - The point is to help write verified code
2. **JSON internally** - One source of truth, display adapts to context
3. **Drop-in replacement** - `t[LANG]c` accepts all standard compiler flags
4. **Verification IS the lint** - No separate linter needed
5. **Contracts ARE the docs** - No separate doc generator needed
6. **AI-friendly output** - JSON for machine consumption, structured for parsing
