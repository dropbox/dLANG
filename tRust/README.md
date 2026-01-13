# tRust

| Director | Status |
|:--------:|:------:|
| LANG | ACTIVE |

**Rust where compilation is verification.**

A fork of rustc that integrates formal verification directly into the compiler. No external tools. No separate proof languages. Write Rust with specifications, and the compiler proves your code correct or gives you a counterexample.

> *"Proofs are the ultimate documentation. They're complete, correct, and they fit in context."*

> *"Tests are humans remembering to check. Proofs are math remembering forever."*

## Motivation

### The Problem

Current verification tools are fragmented:

| Tool | What | Problem |
|------|------|---------|
| Kani | Bounded model checking | External tool, CBMC backend, slow feedback |
| Creusot | Deductive verification | Requires Why3, separate proof language |
| Prusti | Pre/post conditions | Viper backend, limited integration |
| Verus | Verified Rust subset | Research project, not upstream |
| TLA+ | Temporal specs | Completely separate from implementation |
| proptest | Property testing | Runtime only, not proof |

You write Rust. Then separately write specs. Then run a separate tool. Then map failures back to code. The feedback loop is broken.

### How tRust Compares to Kani

Kani is the closest existing tool to tRust. Here's the difference:

| Aspect | Kani | tRust |
|--------|------|-------|
| Integration | External tool (`cargo kani`) | **Built into rustc** |
| Opt-in | Write `#[kani::proof]` per function | **Every function verified by default** |
| Requires | Write `#[kani::requires(...)]` | **Inferred from types/branches** |
| Ensures | Write `#[kani::ensures(...)]` | **Inferred or checked automatically** |
| Compiler access | Parses MIR dumps | **Full AST/MIR/types native** |
| Borrow checker | Can't see it | **Leverages existing proofs** |
| Incremental | Re-analyzes everything | **Uses rustc's incremental cache** |

**Kani (opt-in, manual specs):**
```rust
#[kani::proof]
#[kani::unwind(10)]
fn check_sum() {
    let n: u32 = kani::any();
    kani::assume(n < 100);
    let result = sum(n);
    kani::assert(result <= 5050);
}
```

**tRust (automatic, zero specs):**
```rust
fn sum(n: u32) -> u32 {
    let mut s = 0u32;
    let mut i = 0u32;
    while i < n {
        i += 1;
        s += i;
    }
    s
}
// Just compile. tRust verifies no overflow, infers loop invariant.
```

**tRust = Kani everywhere, automatically, with zero boilerplate.**

tRust uses Kani Fast (our CHC-optimized fork) as a backend for complex proofs like loop invariants, while handling simple cases directly in the compiler with full type information.

### The Solution

```rust
fn sort<T: Ord>(input: Vec<T>) -> Vec<T>
where
    ensures: permutation(input, return),
    ensures: forall |i, j| i < j < return.len() => return[i] <= return[j],
{
    // Implementation
}
```

The compiler rejects this if it cannot prove the postconditions. No separate tool. No optional analysis. **Proof is compilation.**

### Why Now

AI agents are writing code. They don't care about:
- Syntactic sugar
- Short keywords
- "Ergonomic" APIs
- Low learning curves

They care about:
- Unambiguous grammar
- Provable correctness
- Tight feedback loops
- Rich error messages with counterexamples

An AI writes code with specs. The compiler proves it or returns a counterexample. The AI iterates until it compiles. **Compiles = correct.**

## Vision: The AI-First Verified Language

See [VISION.md](VISION.md), [TRUST_MODEL.md](TRUST_MODEL.md), [EVOLUTION.md](EVOLUTION.md), and [ROADMAP.md](ROADMAP.md) for the full story.

### The Problem at Scale

As AI agents build larger systems:
- **Tests don't scale**: 1000 components × 1000 interactions = combinatorial explosion
- **Context doesn't scale**: AI can't hold million-line codebases in context
- **Code review is gone**: No human is reading every line
- **Runtime code generation**: AI writes code at runtime that executes immediately - no second chances

### Why Proofs Scale

Each component specifies its contract. The compiler proves the implementation. When components compose, the compiler proves the composition is valid. **The AI focuses only on its local piece - the types and specs guarantee the global picture.**

```
Traditional: Write → Test → Debug → Ship → Hope
tRust:       Write spec → Write code → Compiler proves → Ship (correct by construction)
```

### Spec Quality Enforcement

AI can't game the system with weak specs:

```rust
#[ensures(true)]  // REJECTED: trivial spec
#[ensures(sorted(result) && permutation(input, result))]  // ACCEPTED: meaningful
```

The compiler enforces that specs are non-trivial and actually constrain the result.

### Third-Party Trust

**A compiled tRust binary is proven correct. No audit required.**

```
TRUST CERTIFICATE
-----------------
Binary: my_app (sha256:a1b2c3...)
Guarantees:
  ✓ All specs satisfied and non-trivial
  ✓ No memory safety violations
  ✓ No undefined behavior
Trust Boundaries: 3 #[trusted] extern calls (listed)
```

### The Language Evolves

**Every crash that escapes verification is a bug in tRust, not the application.**

When verified code fails:
1. Failure reveals a gap in verification
2. tRust is patched to catch that class of bugs
3. That bug class becomes **impossible forever**
4. All programs become safer (recompile to upgrade)

This is how Rust eliminated memory bugs. tRust eliminates ALL bugs, one class at a time.

## Architecture

```
                              rustc pipeline
┌──────────────────────────────────────────────────────────────────────────┐
│                                                                          │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌──────────────────────┐  │
│  │ Parser  │ -> │   HIR   │ -> │   MIR   │ -> │  Verification Pass   │  │
│  │ + specs │    │ + specs │    │ + specs │    │  (NEW)               │  │
│  └─────────┘    └─────────┘    └─────────┘    └──────────┬───────────┘  │
│                                                          │              │
│                                    ┌─────────────────────┴────────────┐ │
│                                    │     Verification Condition IR    │ │
│                                    └─────────────────────┬────────────┘ │
│                                                          │              │
│        ┌─────────────┬─────────────┬─────────────┬───────┴───────┐     │
│        ▼             ▼             ▼             ▼               ▼     │
│   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐ │
│   │   Z4    │   │  Kani   │   │   TLA   │   │  Lean5  │   │  CROWN  │ │
│   │  (SMT)  │   │  (BMC)  │   │ (temp)  │   │ (proof) │   │  (NN)   │ │
│   └─────────┘   └─────────┘   └─────────┘   └─────────┘   └─────────┘ │
│                                                                        │
│                         Proof Backend Pool                             │
│                                                                        │
│                                    │                                   │
│                                    ▼                                   │
│                             ┌──────────────┐                           │
│                             │     LLVM     │                           │
│                             │   Codegen    │                           │
│                             └──────────────┘                           │
│                                                                        │
└──────────────────────────────────────────────────────────────────────────┘
```

## Contract Elision

tRust enhances upstream Rust's experimental `#[feature(contracts)]` rather than replacing it. When tRust can prove a contract at compile time, the runtime check is **elided** (removed entirely). When it can't prove, the upstream runtime check remains as a fallback.

### Example

```rust
#[requires(x > 0)]
fn increment(x: i32) -> i32 {
    x + 1
}
```

**Upstream Rust generates a runtime check:**
```rust
// Executes every call - has runtime cost
if !(x > 0) {
    panic!("precondition violated");
}
```

**tRust, when it proves the contract:**
```rust
// Check completely removed - zero runtime cost
// The proof guarantees x > 0 for all callers
```

### Three Outcomes

| tRust Result | What Happens | Runtime Cost |
|--------------|--------------|--------------|
| **PROVEN** | Runtime check **elided** | Zero |
| **UNKNOWN** | Runtime check kept | Same as upstream |
| **DISPROVEN** | Compiler error + counterexample | N/A |

### Why This Matters

- **No language divergence**: Same `#[requires]`/`#[ensures]` syntax as upstream
- **Strict improvement**: Proven contracts are faster than upstream (zero overhead)
- **Safe fallback**: Unproven contracts still get runtime protection
- **Better errors**: Disproven contracts caught at compile time, not runtime

## Verification Backends

### Core Backends

| Backend | Purpose | Strength |
|---------|---------|----------|
| **Z4** | SMT solving | Fast decidable theories (arithmetic, arrays, bitvectors) |
| **Kani** | Bounded model checking | Exhaustive exploration up to bounds, finds counterexamples |
| **TLA** | Temporal logic | Distributed systems, liveness, fairness properties |
| **Lean5** | Theorem proving | Inductive proofs, complex mathematical properties |

### Specialized Backends

| Backend | Purpose | Strength |
|---------|---------|----------|
| **Prusti** | Separation logic | Heap reasoning, pointer aliasing, data structures |
| **Verus** | Functional correctness | Ghost code, proof assistants, complex invariants |
| **proptest** | Property-based testing | Fast feedback, edge case discovery, fuzzing |
| **CROWN** | Neural network verification | Certified bounds on NN outputs, adversarial robustness |

## Specification Language

### Function Specifications

```rust
#[requires(n > 0)]
#[ensures(result >= n)]
#[ensures(result % n == 0)]
#[decreases(val)]  // termination measure
fn next_multiple(n: u32, val: u32) -> u32 {
    ((val / n) + 1) * n
}
```

### Type Invariants

```rust
#[invariant(self.balance >= 0)]
#[invariant(self.balance <= self.limit)]
struct Account {
    balance: i64,
    limit: i64,
}
```

### Refinement Types

```rust
type NonEmpty<T> = Vec<T> where self.len() > 0;
type Percentage = f64 where 0.0 <= self && self <= 100.0;
type Sorted<T: Ord> = Vec<T> where forall |i, j| i < j => self[i] <= self[j];
```

### Temporal Properties (Distributed Systems)

```rust
#[temporal(eventually(lock.released))]
#[temporal(always(implies(lock.held_by(a), not(lock.held_by(b)))))]
async fn acquire(lock: &Mutex<T>) -> Guard<T> { ... }

#[protocol]
mod consensus {
    invariant: eventually(all_nodes_agree),
    invariant: always(agreed_value_was_proposed),
    invariant: always(at_most_one_value_agreed),
}
```

### Neural Network Specifications

```rust
#[certified_robust(epsilon = 0.1, norm = Linf)]
#[ensures(forall |perturbation| norm(perturbation) < epsilon =>
          classify(input + perturbation) == classify(input))]
fn classify(input: Tensor<f32, [1, 28, 28]>) -> Class {
    model.forward(input)
}
```

## Error Messages

Verification failures are compiler errors with counterexamples:

```
error[E0900]: postcondition not satisfied
  --> src/lib.rs:15:5
   |
12 | #[ensures(result > 0)]
   |           ----------- postcondition declared here
...
15 |     if x == 0 { return 0; }
   |                        ^ counterexample: x = 0 yields result = 0
   |
   = note: postcondition `result > 0` violated
   = help: consider adding `#[requires(x > 0)]` or handling x == 0 specially

error[E0901]: termination not proven
  --> src/lib.rs:28:1
   |
28 | fn collatz(n: u32) -> u32 {
   | ^^^^^^^^^^^^^^^^^^^^^^^^^ cannot prove this function terminates
   |
   = note: decreases measure `n` may not decrease in recursive call at line 31
   = help: add explicit #[decreases(...)] or mark as #[may_diverge]

error[E0902]: temporal property violated
  --> src/distributed.rs:45:5
   |
42 | #[temporal(eventually(response_sent))]
   |            -------------------------- property declared here
...
45 |     if condition { return; }  // early return without sending response
   |                    ^^^^^^ execution path never satisfies `eventually(response_sent)`
   |
   = note: trace: condition=true -> return -> (no response_sent)
```

## Project Structure

```
tRust/
├── compiler/
│   └── rustc_vc/              # Verification condition generation and encoding
│
├── backends/
│   ├── z3/                    # Z3 SMT solver bindings
│   ├── z4/                    # Z4 SMT solver bindings (default)
│   └── crown/                 # Neural network verification (CROWN)
│
├── deps/
│   └── kani_fast/             # CHC-optimized Kani fork
│
├── crates/
│   └── tla-extract/           # TLA+ temporal logic extraction
│
├── vc_ir/                     # Verification Condition IR
│   ├── src/
│   │   ├── lib.rs
│   │   ├── expr.rs            # VC expressions
│   │   ├── pred.rs            # Predicates
│   │   ├── temporal.rs        # Temporal operators
│   │   └── nn.rs              # Neural network specs
│   └── Cargo.toml
│
├── proofs/
│   └── lean5/                 # Formal soundness proofs (~14.2k lines, 1,323 theorems, 0 sorries)
│       └── MirSemantics/      # MIR operational semantics + WP calculus
│
├── examples/                  # Integration tests and examples
│   ├── sorting/               # Sorting algorithm verification
│   ├── neural_networks/       # Neural network verification examples
│   ├── real_validation/       # Real-world crate validations (subtle, hex, base64)
│   └── *_test.rs              # Individual test cases
│
├── book/                      # User documentation (mdbook)
│
└── docs/                      # Internal documentation
```

## Roadmap

See [ROADMAP.md](ROADMAP.md) for detailed status and completion criteria.

See [VALIDATION_PLAN.md](VALIDATION_PLAN.md) for the rigorous certification plan to prove tRust is a drop-in replacement for rustc.

### Phase 1-2: Core Verification - COMPLETE
- [x] Fork rustc, establish build infrastructure
- [x] VC IR crate with specs, expressions, predicates
- [x] Kani Fast integration (CHC-optimized SMT backend)
- [x] `#[requires]` / `#[ensures]` parsing and verification
- [x] Modular verification (caller uses callee contracts)
- [x] Cross-crate contract verification
- [x] Error reporting with counterexamples

### Phase 2.7: Developer Experience - COMPLETE
- [x] `trustc` wrapper with auto sysroot detection
- [x] `cargo-trust` subcommand integration
- [x] JSON output mode for AI agents
- [x] Incremental verification (file/function caching)
- [x] Global verification cache

### Phase 3-4: Advanced Properties - COMPLETE
- [x] Refinement types with `#[param_type]` / `#[return_type]`
- [x] Loop invariants with `#[invariant]` and CHC synthesis
- [x] Termination proofs with `#[decreases]`
- [x] Effect system with `#[effects]` and `#[pure]`

### Phase 5-7: Specialized Domains - COMPLETE
- [x] Temporal logic with `#[temporal]` attribute
- [x] Wiring verification with `#[wire_start]`, `#[wire_state]`, etc.
- [x] Neural network verification (CROWN backend with IBP, alpha-CROWN, Beta-CROWN)
- [x] Lean5 integration for proof certificates

### Phase N2: Formal Soundness - COMPLETE
- [x] MIR operational semantics formalization in Lean5
- [x] Weakest precondition calculus with soundness proofs
- [x] SMT interface formalization with encoding soundness
- [x] End-to-end soundness theorem: verified programs satisfy their specs
- [x] Zero `sorry` axioms (only SMT solver trust boundary)

### Current Test Status
- 259 integration tests passing (via `./run_tests.sh`)
- 575 vc_ir unit tests passing
- 361 rustc_vc unit tests passing
- 242 trust_crown unit tests passing
- 53 trust_z4 unit tests passing
- 34 trust_z3 unit tests passing
- 27 tla-extract unit tests passing
- 15 trust_macros unit tests passing
- 5 sorting_example unit tests passing
- 4 trust-upstream unit tests passing
- Total: **1,316 unit tests** verified via `cargo test --workspace`

> **Note**: Integration tests verify the complete verification pipeline including VC generation, SMT solving, and contract checking. Unit tests verify all internal components work correctly.

## Dependencies

tRust builds on these forks (all ported to Rust):

| Upstream | Fork | Purpose |
|----------|------|---------|
| Z3 | [Z4](https://github.com/dropbox/z4) | SMT solving |
| Lean4 | [Lean5](https://github.com/dropbox/lean5) | Theorem proving |
| Kani | [Kani-tRust](https://github.com/dropbox/kani) | Model checking |
| TLA+ | [TLA-Rust](https://github.com/dropbox/tla) | Temporal logic |
| alpha-beta-CROWN | [CROWN-Rust](https://github.com/dropbox/crown) | NN verification |

## Tools

tRust provides two main command-line tools:

| Tool | Purpose | Description |
|------|---------|-------------|
| `trustv` | Standalone verifier | Verify Rust code without compiling |
| `trustc` | Verifying compiler | Compile with verification (drop-in `rustc` replacement) |

### trustv - Standalone Verifier

```bash
# Verify a file (no compilation)
trustv hello.rs

# Verbose output with timing
trustv --verbose --profile hello.rs

# JSON output for AI agents
trustv --output-format=json hello.rs

# Explain verification error
trustv --explain E0900
```

### trustc - Verifying Compiler

```bash
# Compile with verification (default)
trustc hello.rs -o hello

# Compile without verification
trustc --no-verify hello.rs -o hello

# All rustc flags work
trustc -O -C lto hello.rs -o hello
```

### cargo-trust - Cargo Integration

```bash
# Verify entire project
cargo trust check

# Build with verification
cargo trust build

# Run tests with verification
cargo trust test
```

## Building

```bash
# Clone with submodules
git clone --recursive git@github.com:dropbox/dLANG/tRust.git
cd tRust

# Build stage 1 compiler
./x.py build --stage 1

# Run tests
./x.py test --stage 1

# Build with all backends
./x.py build --stage 2 --features "z4,kani,tla,lean5,crown"
```

## Philosophy

1. **Compilation = Verification**: If it compiles, it's correct
2. **Proofs are not optional**: Unproven code doesn't compile
3. **Counterexamples, not mysteries**: Every failure shows why
4. **AI-first ergonomics**: Optimize for machine generation, not human typing
5. **One language**: No separate spec language, no external tools

## License

MIT OR Apache-2.0 (same as Rust)
