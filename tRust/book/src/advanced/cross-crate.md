# Cross-Crate Verification

tRust supports verification across crate boundaries. When your code calls functions from dependencies, tRust uses their contracts.

## How It Works

When you depend on a crate compiled with tRust:
1. Contracts are preserved in the compiled `.rlib` metadata
2. When you call a function, tRust loads its contracts
3. Your code is verified against those contracts

## Example Setup

### Dependency Crate (mylib)

```rust,ignore
// mylib/src/lib.rs
#[requires("x >= 0")]
#[ensures("result >= 0")]
pub fn sqrt(x: i32) -> i32 {
    // implementation
}

#[ensures("result == a + b")]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

### Your Crate

```rust,ignore
// main.rs
extern crate mylib;

#[ensures("result >= 0")]
fn distance(x: i32, y: i32) -> i32 {
    // tRust checks: x*x + y*y >= 0
    // tRust assumes: sqrt returns >= 0
    mylib::sqrt(x * x + y * y)
}
```

## Trust Levels

Control verification behavior with trust levels:

```rust,ignore
#![trust_level = "verified"]   // Full verification (default)
#![trust_level = "assumed"]    // Skip verification, trust contracts
#![trust_level = "audited"]    // Has specs, from external audit
```

### `verified` (Default)

- All functions are verified
- Preconditions must be provably satisfied
- Postconditions must be provably correct

### `assumed`

- Verification is skipped
- Contracts are trusted without proof
- Useful for legacy code or external libraries

```rust,ignore
#![trust_level = "assumed"]

// These contracts are assumed true without verification
#[ensures("result >= 0")]
pub fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

### `audited`

- Like `assumed`, but indicates human review
- Contracts come from security audit or manual review
- Logged differently for compliance

## Spec Lockfiles

Track contract changes across dependency versions:

```bash
# Write current spec hashes to lockfile
TRUST_WRITE_SPEC_LOCKFILE=trust-specs.lock trustc main.rs

# Verify specs haven't changed
TRUST_SPEC_LOCKFILE=trust-specs.lock trustc main.rs
```

The lockfile contains hashes of all external contracts. If a dependency updates and changes its contracts, tRust warns you.

### Lockfile Format

```json
{
  "specs": {
    "mylib::sqrt": "abc123...",
    "mylib::add": "def456..."
  }
}
```

## External Contract Tracking

tRust reports which external contracts are used:

```json
{
  "external_contracts": [
    {
      "function": "mylib::sqrt",
      "crate": "mylib",
      "spec_hash": "abc123...",
      "trust_level": "verified",
      "preconditions": 1,
      "postconditions": 1,
      "used_by": ["distance"]
    }
  ]
}
```

## Adding Specs to Dependencies

For dependencies without tRust specs, you can:

### 1. Use Builtin Contracts

tRust provides contracts for standard library functions:

```rust,ignore
use std::cmp::min;

fn example(a: i32, b: i32) -> i32 {
    // tRust knows: min(a, b) <= a && min(a, b) <= b
    min(a, b)
}
```

### 2. Create Wrapper Functions

```rust,ignore
// external_lib has no specs
extern crate external_lib;

#[requires("x >= 0")]
#[ensures("result >= 0")]
pub fn safe_external_sqrt(x: i32) -> i32 {
    // We trust external_lib::sqrt satisfies our contract
    external_lib::sqrt(x)
}
```

### 3. Use `extern` Specs (Future)

```rust,ignore
// Planned: declare specs for external functions
#[extern_spec]
mod external_lib {
    #[requires("x >= 0")]
    #[ensures("result >= 0")]
    fn sqrt(x: i32) -> i32;
}
```

## Verification Workflow

1. **Compile dependencies with tRust**: Embeds contracts in metadata
2. **Develop your crate**: Write code using dependencies
3. **Verify your crate**: tRust checks your code against all contracts
4. **Lock specs**: Generate lockfile for reproducible builds
5. **CI/CD**: Re-verify if dependency specs change

## Best Practices

1. **Verify core dependencies**: Use `verified` for critical libraries
2. **Use lockfiles in production**: Detect contract drift
3. **Audit external specs**: Review `assumed` contracts carefully
4. **Wrap unverified code**: Create verified wrappers around unsafe dependencies

## Debugging Cross-Crate Issues

### Contract Not Found

```console
error: no contract found for external_lib::foo
```

The dependency wasn't compiled with tRust or has no specs.

### Precondition Violation

```console
error: precondition of mylib::sqrt might not hold
  requires(x >= 0)
  at call site: sqrt(a - b)
  counterexample: a = 0, b = 1
```

Your code might call the function with invalid arguments.

### Spec Hash Mismatch

```console
warning: spec hash mismatch for mylib::sqrt
  expected: abc123 (from lockfile)
  found: xyz789 (from compiled crate)
```

The dependency was updated and contracts changed.

## Current Status

tRust's cross-crate verification includes:
- Automatic contract loading from rlib metadata
- Trust level configuration
- Spec hash computation and lockfile support
- External contract tracking in JSON output

## Next Steps

- [VS Code Extension](../tooling/vscode.md) - IDE support for cross-crate verification
- [Builtin Contracts](../reference/builtins.md) - Contracts for standard library
