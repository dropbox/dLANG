# URGENT: Implement Automatic Verification in rustc_verify

**Date**: 2024-12-31
**Priority**: CRITICAL
**Status**: WORKER HAS DRIFTED - REDIRECT IMMEDIATELY

## Problem

The worker has been working on cargo-trust (commits #48-#89) when the design mandates:

> Everything that CAN be verified automatically MUST be verified by default.

The rustc fork works (#44-#47) but ONLY verifies explicit specs. It does NOT verify:
- Integer overflow
- Array bounds
- Division by zero
- Unwrap safety

## What Must Happen

### In `rustc_verify/src/lib.rs`:

```rust
pub fn verify_function(...) {
    // 1. Check explicit specs (DONE)

    // 2. NEW: Automatic overflow checking
    for stmt in body.basic_blocks.iter() {
        match stmt {
            Add(a, b) | Sub(a, b) | Mul(a, b) => {
                // Generate overflow VC
                // Report error if can't prove no overflow
            }
            Div(a, b) => {
                // Generate div-by-zero VC
            }
            Index(arr, idx) => {
                // Generate bounds VC
            }
        }
    }
}
```

### Example Output (What We Need)

```
error[E0XXX]: integer overflow possible
 --> src/lib.rs:5:5
  |
5 |     a + b
  |     ^^^^^ addition may overflow
  |
  = note: counterexample: a = 200, b = 100 (for u8)
  = help: use `a.checked_add(b)` or add `// #[trust(overflow)]`
```

## DO NOT

- Do NOT work on cargo-trust
- Do NOT add features to the separate tool
- Do NOT skip this directive

## Priority Order

1. **Overflow checking** - most common bug
2. **Division by zero** - easy to implement
3. **Array bounds** - requires length tracking
4. **Unwrap safety** - requires nullability tracking (needs Abstract Interp)

## Test Case

This must FAIL verification:

```rust
fn add(a: u8, b: u8) -> u8 {
    a + b  // ERROR: overflow possible
}
```

This must PASS:

```rust
fn safe_add(a: u8, b: u8) -> Option<u8> {
    a.checked_add(b)  // OK: returns None on overflow
}
```

## Success Criteria

```bash
$ ./tRust -Zverify overflow_test.rs
error[E0XXX]: integer overflow possible
```

Without any attributes. Automatic. By default.
