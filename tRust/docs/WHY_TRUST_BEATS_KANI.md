# Why tRust Beats Regular Kani

tRust is a rustc fork with verification built in. Regular Kani is an external tool. This gives tRust fundamental advantages.

## Comparison

| Aspect | Regular Kani | tRust |
|--------|-------------|-------|
| Access | External tool, parses MIR dumps | **Inside rustc**, full AST/MIR/types |
| Type info | Reconstructed | **Native** - exact bounds, traits, lifetimes |
| Borrow checker | Can't see it | **Integrated** - leverage existing proofs |
| Incremental | Re-analyzes everything | **Compiler's incremental cache** |
| Spans/errors | Mapped back awkwardly | **Native diagnostics** |
| Const eval | Separate implementation | **Use rustc's MIRI** |
| Trait resolution | Approximate | **Exact** |

## What This Unlocks

### 1. Borrow Checker as Free Proof

```rust
fn foo(x: &mut i32, y: &mut i32) {
    // Compiler already proved x != y (aliasing)
    // tRust gets this for FREE - no annotation needed
}
```

The borrow checker proves non-aliasing. tRust can use this in verification without re-proving it.

### 2. Exact Type Bounds

```rust
let x: u8 = ...;
// tRust knows 0 <= x <= 255 from the type system
// Kani has to encode this separately
```

Type information is native. No reconstruction needed.

### 3. Const Generics

```rust
fn process<const N: usize>(arr: [u8; N]) {
    // tRust knows arr.len() == N at compile time
    // Can verify bounds without runtime checks
}
```

Const generics give compile-time size information that tRust can use directly.

### 4. Lifetime Information

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    // tRust knows result lifetime is bounded by inputs
    // Can reason about validity without annotation
}
```

Lifetimes encode temporal properties that tRust can leverage.

### 5. Trait Bounds as Constraints

```rust
fn sum<T: Into<i64>>(items: &[T]) -> i64 {
    // tRust knows T converts to i64
    // Can reason about bounds through trait impls
}
```

Trait resolution is exact - tRust knows exactly which impls apply.

### 6. Incremental Verification

```rust
// Change one function
fn foo() { ... }  // Modified

// tRust only re-verifies foo and dependents
// Regular Kani re-analyzes entire crate
```

Rustc's incremental compilation cache tells tRust what changed.

### 7. Native Error Messages

```
error: integer addition may overflow
 --> src/lib.rs:42:5
  |
42 |     a + b
  |     ^^^^^
  |
  = note: counterexample: a=200, b=100
  = help: use `a.checked_add(b)` or constrain inputs
```

Errors use rustc's native diagnostic system - same format developers know.

## The Key Insight

Regular Kani rebuilds compiler knowledge from scratch. tRust has it natively.

This means:
- **Faster** - no reconstruction overhead
- **More precise** - exact compiler semantics
- **Better integrated** - native errors, incremental builds
- **More powerful** - can leverage borrow checker, lifetimes, traits

## Architecture

```
Regular Kani:
  rustc → MIR dump → Kani parses → CBMC → Result
         ↑ information lost here

tRust:
  rustc + verification pass → Result
         ↑ full compiler context available
```

tRust verification runs as a compiler pass with full access to:
- `TyCtxt` (type context)
- `Body` (MIR)
- `DefId` (definitions)
- Trait solver
- Const evaluator
- Borrow checker results

## Implications for Kani Fast

Kani Fast provides the CHC/SMT backend. tRust provides:
- Rich type information
- Borrow checker results
- Exact trait resolution
- Incremental analysis

Together: tRust extracts verification conditions with full compiler context, Kani Fast solves them efficiently.
