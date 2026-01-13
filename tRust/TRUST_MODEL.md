# tRust Trust Model

## The Spec Gaming Problem

An AI can cheat:

```rust
// Trivially passes verification - useless spec
#[ensures(true)]
fn sort(input: Vec<i32>) -> Vec<i32> {
    input  // Wrong! But spec is satisfied.
}
```

Or write incomplete specs:

```rust
// Missing the permutation requirement
#[ensures(sorted(result))]
fn sort(input: Vec<i32>) -> Vec<i32> {
    vec![]  // Empty is sorted! But wrong.
}
```

**Weak specs are worse than no specs.** They create false confidence.

---

## Solution: Spec Quality Enforcement

### 1. Mandatory Spec Coverage

```rust
#![trust_level(verified)]
#![spec_coverage(full)]  // All public functions need complete specs

// Compiler ERROR: missing ensures clause for return value
pub fn sort(input: Vec<i32>) -> Vec<i32> {
    // ...
}
```

The compiler requires:
- Every input has a precondition (even if `true`)
- Every output has a postcondition describing its value
- Every side effect is specified
- Every panic condition is documented or proven impossible

### 2. Spec Strength Requirements

```rust
#![spec_strength(meaningful)]

// Compiler ERROR: ensures(true) is a trivial spec
#[ensures(true)]
pub fn sort(input: Vec<i32>) -> Vec<i32>

// Compiler ERROR: ensures doesn't mention result
#[ensures(input.len() > 0)]  // True but doesn't specify what result IS
pub fn sort(input: Vec<i32>) -> Vec<i32>

// Compiler OK: spec mentions result and input relationship
#[ensures(result.len() == input.len())]
#[ensures(sorted(result))]
#[ensures(permutation(input, result))]
pub fn sort(input: Vec<i32>) -> Vec<i32>
```

Rules for meaningful specs:
- `ensures` must reference `result`
- `ensures` must constrain `result` relative to inputs
- `ensures(true)` is forbidden
- `ensures(trivially_derivable_from_requires)` is forbidden

### 3. Spec Templates for Common Patterns

```rust
// Compiler provides spec templates that must be satisfied

#[collection_transform]  // Template: must preserve, transform, or filter
pub fn sort(input: Vec<i32>) -> Vec<i32> {
    // Template expands to:
    // #[ensures(permutation(input, result) ||
    //           subset(result, input) ||
    //           superset(result, input))]
    // AI must satisfy at least one
}

#[search]  // Template: must either find or prove absence
pub fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    // Template expands to:
    // #[ensures(result.is_some() => arr[result.unwrap()] == target)]
    // #[ensures(result.is_none() => forall |i| arr[i] != target)]
}

#[state_mutation]  // Template: must specify what changes and what's preserved
pub fn withdraw(&mut self, amount: i64) -> Result<(), Error> {
    // Template expands to:
    // #[ensures(result.is_ok() => SOMETHING_CHANGED)]
    // #[ensures(result.is_ok() => INVARIANTS_PRESERVED)]
    // #[ensures(result.is_err() => self == old(self))]  // Rollback
}
```

### 4. Spec Fuzzing / Property Discovery

```rust
// Compiler attempts to infer stronger specs

fn sort(input: Vec<i32>) -> Vec<i32> {
    // ... implementation ...
}

// Compiler: "I can prove these additional properties.
//            Did you mean to specify them?"
//
// Inferred:
//   - permutation(input, result): PROVABLE
//   - sorted(result): PROVABLE
//   - result.len() == input.len(): PROVABLE
//
// Warning: Function has stronger properties than specified.
//          Consider adding them to the spec.
```

### 5. Spec Mutation Testing

The compiler attempts to weaken specs and checks if implementation still passes:

```rust
#[ensures(result > 0)]
#[ensures(result <= input)]
fn clamp_positive(input: i32) -> i32 {
    input.max(1)
}

// Compiler tries mutations:
//   - Remove ensures(result > 0): impl STILL passes → spec might be incomplete
//   - Remove ensures(result <= input): impl FAILS → spec is necessary
//   - Weaken to ensures(result >= 0): impl STILL passes → spec could be stronger
//
// Warning: Spec may be weaker than implementation guarantees
```

---

## Third-Party Trust: Compilation as Proof

### The Guarantee

When a tRust binary exists:

```
┌────────────────────────────────────────────────────────────────┐
│                    TRUST CERTIFICATE                            │
│                                                                │
│  Binary: my_app                                                │
│  Hash: sha256:a1b2c3...                                        │
│                                                                │
│  Verification Level: FULL                                      │
│                                                                │
│  Guarantees:                                                   │
│    ✓ All specs are satisfied                                  │
│    ✓ All specs are non-trivial (spec_strength: meaningful)    │
│    ✓ No memory safety violations possible                     │
│    ✓ No undefined behavior                                     │
│    ✓ All panic conditions documented or impossible            │
│                                                                │
│  Trust Boundaries:                                             │
│    - 3 #[trusted] extern calls (audit recommended)            │
│    - 2 #[assumed] dependencies (serde, tokio)                 │
│                                                                │
│  Compiler: tRust 1.0.0                                        │
│  Verified: 2025-12-29T18:30:00Z                               │
└────────────────────────────────────────────────────────────────┘
```

If it compiled, it's correct. The certificate is the proof.

### Reproducible Verification

```bash
# Anyone can verify the binary
$ trust verify ./my_app --source ./src

Reproducing build...
  Source hash: matches
  Dependencies: all verified or declared trusted
  Specs: all non-trivial
  Proofs: all reproduced

VERIFIED: Binary matches source and all proofs check.
```

### Trust Levels in Practice

```rust
// Level 1: Fully Verified
#![trust_level(verified)]
#![spec_coverage(full)]
#![spec_strength(meaningful)]
// No #[trusted] calls allowed
// Zero trust boundaries
// Third parties can deploy without audit

// Level 2: Verified with Boundaries
#![trust_level(verified)]
#![allow_trusted(max = 5)]
// Limited #[trusted] calls
// Each boundary documented
// Third parties audit only the boundaries

// Level 3: Audited Specs
#![trust_level(audited)]
// Specs present but not compiler-enforced strength
// Trust the spec author
// Recommend manual review

// Level 4: Assumed Correct
#![trust_level(assumed)]
// Legacy code, no specs
// Full manual audit required
// Isolation recommended
```

### Supply Chain Security

```toml
# Cargo.toml
[dependencies]
# Only allow verified dependencies
serde = { version = "1.0", trust = "verified" }  # Has full specs, proven

# Or explicitly trust without verification
tokio = { version = "1.0", trust = "assumed", audit = "2025-01-15" }

[trust-policy]
# Fail build if any dependency is unverified without explicit trust
require-explicit-trust = true
# Maximum depth of assumed dependencies
max-assumed-depth = 2
```

---

## The Enforcement Stack

```
┌─────────────────────────────────────────────────────────────────┐
│                         Human Intent                             │
│                  "I want a correct sort function"               │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      Spec Templates                              │
│            "A sort must preserve and order elements"            │
│                                                                 │
│  #[collection_transform(preserve_elements, establish_order)]    │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                     Spec Strength Checker                        │
│              "Does this spec constrain the result?"             │
│                                                                 │
│  ✗ ensures(true) - rejected                                    │
│  ✗ ensures(input.len() > 0) - rejected, doesn't mention result │
│  ✓ ensures(sorted(result) && permutation(input, result))       │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                       Spec Completeness                          │
│              "Are all behaviors specified?"                     │
│                                                                 │
│  ✗ Missing: what if input is empty?                            │
│  ✗ Missing: does it allocate?                                  │
│  ✓ All paths covered                                           │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                      Implementation Verifier                     │
│              "Does the code satisfy the spec?"                  │
│                                                                 │
│  VC 1: sorted(result) .............. PROVEN                    │
│  VC 2: permutation(input, result) .. PROVEN                    │
│  VC 3: no panic .................... PROVEN                    │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                        Trust Certificate                         │
│                   "This binary is correct"                      │
│                                                                 │
│  ✓ VERIFIED - No review required by third parties              │
└─────────────────────────────────────────────────────────────────┘
```

---

## Preventing AI Spec Gaming: Summary

| Attack | Defense |
|--------|---------|
| `ensures(true)` | Rejected by spec strength checker |
| Spec doesn't mention result | Rejected by relevance checker |
| Spec is subset of requires | Rejected as trivially derivable |
| Incomplete spec | Caught by mandatory coverage |
| Spec weaker than impl | Warned by mutation testing |
| Missing edge cases | Caught by spec templates |

**The AI cannot game the system because the compiler enforces spec quality, not just spec satisfaction.**

---

## Why This Creates Real Trust

Traditional code review:
- Human reads code
- Human might miss bugs
- Human might not understand all interactions
- Trust = faith in reviewer

tRust verification:
- Compiler checks all paths
- Compiler never misses specified properties
- Compiler verifies composition
- Trust = mathematical proof

**A tRust binary with a clean certificate is more trustworthy than any human-reviewed code.**

This is how you get:
- Autonomous AI code generation without human review
- Third-party deployment without audits
- Runtime code execution without testing
- Systems of arbitrary scale without integration failures

The compiler is the auditor. The proof is the trust.
