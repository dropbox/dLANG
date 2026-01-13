# Verification Template for rustc Components

Template for formally verifying rustc crate modules. Use this as a starting point for rustc-arena-verified or similar projects.

## Project Structure

```
rustc-<component>-verified/
├── CLAUDE.md           ← AI worker instructions
├── ROADMAP.md          ← Verification plan with phases
├── Cargo.toml          ← Crate configuration
├── rust-toolchain.toml ← Toolchain requirements (if nightly needed)
├── src/
│   ├── lib.rs          ← Main module (exports)
│   └── <modules>.rs    ← Module files with specifications
└── docs/
    └── VERIFICATION_STATUS.md  ← Progress tracking
```

## Files to Create

### 1. Cargo.toml

```toml
[package]
name = "rustc-<component>-verified"
version = "0.1.0"
edition = "2021"
description = "Formally verified rustc_<component>"
license = "Apache-2.0"
repository = "https://github.com/dropbox/rustc-<component>-verified"

# Exclude from parent tRust workspace
[workspace]

[dependencies]
# tRust verification macros
trust_macros = { path = "../../trust_macros" }
# Add other dependencies as needed

[dev-dependencies]

[features]
default = []
verify = []

[lib]
name = "rustc_<component>_verified"
path = "src/lib.rs"

# Suppress warnings for trust_verify cfg
[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = ["cfg(trust_verify)"] }
```

### 2. rust-toolchain.toml (if nightly features needed)

```toml
[toolchain]
channel = "nightly"
components = ["rust-src", "rustfmt", "clippy"]
```

### 3. ROADMAP.md Template

```markdown
# ROADMAP - rustc-<component>-verified

Verification plan for rustc_<component>.

## Overview

| Module | Lines | Functions | Priority | Status |
|--------|-------|-----------|----------|--------|
| `<mod1>.rs` | ~X | ~Y | P0 | Not started |
| `<mod2>.rs` | ~X | ~Y | P1 | Not started |

**Estimated effort**: X-Y AI commits

---

## Phase 0: Project Setup

- [ ] Fork baseline from upstream/rustc
- [ ] Create project structure
- [ ] Copy initial module with docs
- [ ] Add unit tests
- [ ] Verify cargo test passes

---

## Phase N: <Module Name>

**Goal**: Verify <module> operations
**Effort**: X-Y AI commits

### N.1 <Category>
- [ ] `function_name()` - <property>
- [ ] `function_name()` - <property>

**Deliverable**: All methods have specs, key invariants documented.

---

## Success Criteria

1. **<mod>.rs**: 100% function coverage, specs documented
2. Tests passing
3. Documentation complete
```

### 4. VERIFICATION_STATUS.md Template

```markdown
# Verification Status

Tracking progress for rustc-<component>-verified.

## Summary

| Module | Functions | Spec Documented | Attributed | Verified |
|--------|-----------|-----------------|------------|----------|
| <mod>.rs | X | 0 | 0 | 0 |

**Total**: 0/X functions with specs, 0 with attributes, 0 verified

---

## <module>.rs (Phase N - STATUS)

### <Category>

| Function | Status | Property | Notes |
|----------|--------|----------|-------|
| `fn_name()` | PENDING | <property> | - |

Status values: PENDING → SPEC_DOCUMENTED → ATTRIBUTED → VERIFIED

---

## Notes

- Project initialized: YYYY-MM-DD
- Verification tool: tRust/trustc
- Baseline: rustc 1.94.0-dev rustc_<component>
```

### 5. CLAUDE.md Template

```markdown
# CLAUDE.md - rustc-<component>-verified

Formally verified rustc_<component>: <brief description>.

**Location:** `~/tRust/deps/rustc-<component>-verified/`
**Baseline:** `~/tRust/upstream/rustc/compiler/rustc_<component>/`
**Parent:** tRust

---

## Workers and Managers

[Copy worker/manager instructions from rustc-index-verified/CLAUDE.md]

---

## Behavior

**You are an expert Rust and formal verification engineer.**

### Project-Specific Rules

- **VERIFICATION IS THE GOAL**: Add formal specs and prove them
- **USE tRust FOR VERIFICATION**: `~/tRust/tools/trustc src/lib.rs -Zverify`
- **BASELINE IS REFERENCE**: Don't modify upstream
- **PROVE, DON'T TEST**: Prefer proving over testing

---

## Project Structure

[List actual files]

---

## Verification Workflow

1. Copy baseline function
2. Add specifications
3. Run trustc
4. If fails: examine counterexample
5. If succeeds: document
6. Commit with status

---

## Testing

```bash
# Run verification
RUSTC=~/tRust/bin/trustc RUSTC_WRAPPER=./scripts/trust-workspace-wrapper.sh cargo check
```
```

## Example: rustc-arena-verified

For rustc_arena, the verification priorities would be:

### Phase 0: Setup
- Fork `upstream/rustc/compiler/rustc_arena/`
- Create project structure
- Focus on `TypedArena<T>` and `DroplessArena`

### Phase 1: TypedArena Core
Key functions to verify:
- `TypedArena::new()` - ensures empty arena
- `TypedArena::alloc(value)` - ensures value is stored, returns valid ref
- `TypedArena::alloc_slice(slice)` - ensures all values stored
- `TypedArena::clear()` - ensures all objects dropped

### Phase 2: DroplessArena
- `DroplessArena::alloc(value)` - value stored (no drop needed)
- `DroplessArena::alloc_slice(slice)` - all values stored
- Memory alignment guarantees

### Phase 3: ArenaChunk Internals
- `ArenaChunk::new(capacity)` - memory allocated
- `ArenaChunk::start()/end()` - pointer validity
- Safety invariants for `destroy()`

### Key Properties for Arena Verification

```rust
// TypedArena::alloc postcondition
#[ensures(result points to valid T)]
#[ensures(result lifetime tied to arena)]

// TypedArena::clear postcondition
#[ensures(forall allocated T: T::drop() called)]

// DroplessArena guarantees
#[requires(!needs_drop::<T>())]  // Precondition for alloc
```

### Challenges Specific to rustc_arena

1. **Unsafe code**: Heavy use of raw pointers, needs `#[trusted]` for some functions
2. **Drop safety**: `#[may_dangle]` interactions with verification
3. **Intrinsics**: Uses `core_intrinsics` feature
4. **Alignment**: Complex memory layout guarantees

## Verification Attribute Reference

| Attribute | Purpose | Example |
|-----------|---------|---------|
| `#[requires(expr)]` | Precondition | `#[requires(idx < len)]` |
| `#[ensures(expr)]` | Postcondition | `#[ensures(result > 0)]` |
| `#[invariant(expr)]` | Loop invariant | `#[invariant(i <= n)]` |
| `#[trusted]` | Skip verification | For FFI, unsafe |
| `#[pure]` | No side effects | For spec helpers |
| `#[ghost]` | Spec-only code | Erased at runtime |

## Common Patterns

### Length Preservation

```rust
#[ensures(result.len() == old(self.len()))]
fn as_slice(&self) -> &[T] { &self.raw }
```

### Bounds Checking

```rust
#[requires(idx < self.len())]
fn get(&self, idx: usize) -> &T { &self.raw[idx] }
```

### Option Returns

```rust
#[ensures(idx < self.len() => result.is_some())]
#[ensures(idx >= self.len() => result.is_none())]
fn get(&self, idx: usize) -> Option<&T>
```

### Mutation

```rust
#[ensures(self.len() == old(self.len()) + 1)]
fn push(&mut self, val: T)
```

## Estimated Effort by Component

| Component | Lines | Complexity | Estimate |
|-----------|-------|------------|----------|
| rustc_arena | ~800 | High (unsafe) | 15-25 commits |
| rustc_data_structures | ~5000 | High (many types) | 40-60 commits |
| rustc_span | ~2000 | Medium | 20-30 commits |
| rustc_errors | ~3000 | Medium | 25-35 commits |

Complexity factors:
- **Low**: Simple data structures, few edge cases
- **Medium**: Some unsafe, moderate invariants
- **High**: Heavy unsafe, complex invariants, lifetimes
