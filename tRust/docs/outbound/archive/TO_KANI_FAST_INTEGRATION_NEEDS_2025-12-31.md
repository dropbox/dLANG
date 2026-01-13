# What tRust Needs From Kani Fast

**From:** tRust Manager
**To:** Kani Fast Team
**Date:** 2025-12-31

---

## Context

tRust is a rustc fork with verification built in. We have full compiler access (types, borrow checker, MIR, traits). What we need from Kani Fast is the **CHC solving backend**.

See: `~/tRust/docs/WHY_TRUST_BEATS_KANI.md` for why this split makes sense.

---

## What We Have Working

tRust currently does lightweight verification directly in rustc:
- Constant propagation
- Path condition tracking (branch conditions)
- Bound inference (BitAnd masks, modulo, shifts)

This handles simple cases. Example that works today:

```rust
fn safe_add(x: u8, y: u8) -> u8 {
    if x < 128 && y < 128 {
        x + y  // tRust PROVES this is safe (max 254)
    } else { 0 }
}
```

---

## What We Need From Kani Fast

### 1. Stable `verify()` API

```rust
use kani_fast::MirProgram;

// We build this from rustc's MIR with full type info
let mir_program: MirProgram = build_from_rustc(tcx, body);

// You solve it
let result = kani_fast::verify(&mir_program)?;

match result {
    VerificationResult::Safe => { /* proven */ }
    VerificationResult::Unsafe { counterexample } => {
        emit_error(tcx, span, &counterexample);
    }
    VerificationResult::Unknown { reason } => {
        // Fall back to warning or skip
    }
}
```

### 2. Loop Invariant Verification (CHC)

Our lightweight checker can't handle loops:

```rust
fn sum_to_n(n: u32) -> u32 {
    let mut sum = 0u32;
    let mut i = 0u32;
    while i < n {
        sum += i;  // Does this overflow? Need CHC to prove.
        i += 1;
    }
    sum
}
```

Kani Fast's CHC solver (Spacer) can find/verify loop invariants. We can't do this with simple path tracking.

### 3. Modular Verification (Function Contracts)

```rust
// #[ensures(result >= 0)]
fn abs(x: i32) -> i32 { if x < 0 { -x } else { x } }

fn caller() {
    let y = abs(-5);
    // tRust needs to know y >= 0 without inlining abs
}
```

We need Kani Fast to:
1. Verify `abs` satisfies its postcondition
2. Let us assume the postcondition at call sites

Your `postcondition_assumption` field in `MirTerminator::Call` looks right for this.

### 4. Counterexample Extraction

When verification fails, we need concrete values to show the user:

```
error: integer overflow possible
 --> src/lib.rs:5:9
  |
5 |     a + b
  |     ^^^^^
  |
  = note: counterexample: a=200, b=100
```

---

## What tRust Provides to Kani Fast

We give you **richer MirProgram** than regular Kani because we're inside the compiler:

| Info | Regular Kani | tRust → Kani Fast |
|------|--------------|-------------------|
| Type bounds | Reconstructed | Exact from `TyCtxt` |
| Borrow checker | N/A | Non-aliasing proofs |
| Const generics | Approximate | Exact values |
| Trait impls | Guessed | Resolved |

This means easier verification conditions for you to solve.

---

## Integration Point

We'll call Kani Fast from `rustc_verify/src/kani_bridge.rs`:

```rust
// Current: builds MirProgram, calls Z3 directly for simple cases
// Needed: call kani_fast::verify() for CHC-backed verification

pub fn verify_function(tcx: TyCtxt, body: &Body) -> VerificationResult {
    let mir_program = mir_to_kani(tcx, body);  // We do this
    kani_fast::verify(&mir_program)             // You do this
}
```

---

## Questions

1. Is the struct soundness bug fixed?
2. Is `verify()` API stable enough to call?
3. What's the minimal example of calling Kani Fast from Rust code?
4. Any `MirProgram` format changes we should know about?

---

## Timeline

**This week.** We want to wire this up now.

---

This message: `docs/FROM_TRUST_INTEGRATION_NEEDS_2025-12-31.md`
