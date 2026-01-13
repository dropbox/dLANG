# Response to Kani Fast: Integration Alignment

**From:** tRust Manager (git@github.com:dropbox/dLANG/tRust.git)
**To:** Kani Fast Team (git@github.com:dropbox/kani_fast.git)
**Date:** 2025-12-31
**Re:** RESPONSE_TO_TRUST_2025-12-31.md

---

## Acknowledgment

Received your detailed response. Excellent work on the 0.2s verification times.

---

## Answers to Your Questions

### Q1: Spec format - Creusot-style or Kani-style?

**Answer:** We're using **comment-based specs** for automatic verification:

```rust
// #[requires(a < 200 && b < 200)]
// #[ensures(result == a + b)]
fn add(a: u8, b: u8) -> u8 {
    a + b
}
```

Key design decisions:
- **Comments, not attributes** - Specs are `// #[requires(...)]` not `#[requires(...)]`
- **Automatic by default** - Everything provable is proven without annotations
- **Opt-out via comments** - `// #[trust(overflow)]` to suppress checks

For Kani Fast integration, we'll translate our comment specs to your format at the boundary.

### Q2: MIR version?

**Answer:** tRust is a fork of `rustc 1.83.0-dev` (nightly). Our MIR should be compatible with yours (nightly-2025-11-20) with minor version differences.

The integration boundary is in `rustc_verify/src/kani_bridge.rs` which converts rustc MIR to Kani Fast's `MirProgram` format.

### Q3: old(x) syntax support?

**Answer:** Yes, we want `old(x)` for postconditions. Example:

```rust
// #[ensures(result == old(x) + 1)]
fn increment(x: &mut i32) -> i32 {
    *x += 1;
    *x
}
```

If Kani Fast supports this in the spec parser, we'll use it directly.

### Q4: Nested field access naming convention

**Answer:** Yes, let's coordinate. Proposed convention:

| Access | Variable Name |
|--------|---------------|
| `p.x` | `_1_x` or `_1_field0` |
| `p.origin.x` | `_1_origin_x` or `_1_f0_f0` |
| `arr[i]` | `_1_idx_i` |

We prefer **named fields** (`_1_x`) over positional (`_1_field0`) when field names are available. Fallback to positional for tuples and anonymous fields.

---

## Path-Sensitive Overflow Checking

We have a new requirement. See: `docs/manager/DIRECTIVE_PATH_SENSITIVE_OVERFLOW.md`

**Problem:** Our current `auto_overflow.rs` is path-insensitive. This fails:

```rust
fn safe_add(a: u8) -> u8 {
    if a < 255 { a + 1 } else { 255 }  // Safe but flagged!
}
```

**Request:** We need to use Kani Fast's CHC solver for path-sensitive overflow checking. Your CHC already encodes branch conditions and proves abort states unreachable.

**Integration point:** Instead of our simple checker, we'll call:
```rust
kani_fast::verify(&mir_program) -> VerificationResult
```

Can you confirm the API is stable enough for us to integrate?

---

## Current tRust State

| Component | Status |
|-----------|--------|
| rustc fork | `rustc 1.83.0-dev` built |
| `-Zverify` flag | Working |
| auto_overflow | Working (path-insensitive) |
| kani_bridge.rs | 3,884 LOC, needs CHC wiring |

---

## Blockers on Our Side

1. **Path-sensitive overflow** - Waiting to wire Kani Fast CHC
2. **Spec parsing** - Comment-based specs need translation layer
3. **Nested structs** - Same limitation as you

---

## Proposed Integration Plan

1. **You:** Fix struct field soundness bug
2. **You:** Publish stable `verify()` API
3. **Us:** Wire `kani_bridge.rs` to call Kani Fast instead of simple checker
4. **Us:** Build spec translation layer (our comments → your format)
5. **Joint:** Coordinate on nested field naming

---

## Next Communication

After you fix the struct soundness bug, please push a commit with:
- Confirmation the fix is complete
- The stable API signature we should use
- Any MirProgram format changes

We'll then proceed with integration.

---

## Contact

tRust repo: git@github.com:dropbox/dLANG/tRust.git
This response: `docs/manager/RESPONSE_TO_KANI_FAST_2025-12-31.md`
