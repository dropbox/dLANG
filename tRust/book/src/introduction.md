# Introduction

**tRust** is a fork of the Rust compiler that integrates formal verification directly into the compilation process. When you compile with tRust, the compiler doesn't just check types and lifetimes - it mathematically proves that your code meets its specifications.

## The Problem

As AI agents build larger systems, traditional quality assurance breaks down:

- **Tests don't scale**: 1000 components with 1000 interactions create a combinatorial explosion
- **Context doesn't scale**: AI can't hold million-line codebases in context
- **Code review is gone**: No human is reading every line
- **Integration is the bottleneck**: Each component works in isolation, but together they fail

## The Solution

**Correctness by construction.**

Each function specifies its contract - what it requires from callers and what it ensures to callers. The compiler proves the implementation satisfies the contract. When functions compose, the compiler proves the composition is valid.

```text
Traditional:
  Write code -> Write tests -> Run tests -> Debug failures -> Ship (hope it works)

tRust:
  Write spec -> Write code -> Compiler proves -> Ship (proven correct)
```

## A Simple Example

```rust,ignore
#[requires("n > 0")]
#[ensures("result >= 1")]
#[ensures("result <= n")]
fn clamp_positive(n: i32, val: i32) -> i32 {
    if val < 1 { 1 }
    else if val > n { n }
    else { val }
}
```

When you compile this with tRust:

```console
$ trustc clamp.rs
Verifying clamp_positive...
  requires(n > 0): assumed
  ensures(result >= 1): PROVEN
  ensures(result <= n): PROVEN

Verification: 1/1 functions verified
```

The compiler mathematically proves that:
- If `n > 0` (the precondition), then `result >= 1` and `result <= n` (the postconditions)
- This proof covers all possible inputs, not just test cases

## What tRust Can Verify

tRust can prove properties about:

- **Integer overflow**: Arithmetic operations won't overflow
- **Array bounds**: Array accesses are within bounds
- **Null safety**: Option unwraps won't panic
- **Custom invariants**: Your domain-specific properties
- **Loop termination**: Loops will eventually terminate
- **Effects**: Functions don't have unexpected side effects

## When Verification Fails

When tRust can't prove a property, it provides a counterexample:

```rust,ignore
#[ensures("result >= 0")]
fn bad_abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }  // Bug: -(-2147483648) overflows!
}
```

```console
$ trustc bad_abs.rs
Verifying bad_abs...
  ensures(result >= 0): DISPROVEN
    Counterexample: x = -2147483648

Verification: 0/1 functions verified
```

The counterexample shows exactly which input violates the specification.

## How It Works

tRust uses:

1. **SMT Solving**: Translates verification conditions to SMT-LIB format and uses the Z4 theorem prover (a custom fork of Z3)
2. **Weakest Precondition Calculus**: Generates precise logical conditions that must hold
3. **Modular Verification**: Uses function contracts to verify callers and callees separately
4. **Constrained Horn Clauses (CHC)**: Synthesizes loop invariants automatically

## Getting Started

Ready to write verified Rust? Head to [Installation](./getting-started/installation.md) to set up tRust, then follow [Your First Verified Program](./getting-started/first-program.md) for a hands-on tutorial.
