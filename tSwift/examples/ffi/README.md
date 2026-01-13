# FFI Verification Examples

This directory demonstrates tSwift's cross-language FFI verification.

## Files

| File | Description |
|------|-------------|
| `secure_buffer.rs` | Rust FFI exports with `#[ffi_requires]` / `#[ffi_ensures]` |
| `secure_buffer_import.swift` | Swift imports with matching (stronger) contracts |
| `weak_import_fail.swift` | Swift imports with WEAK contracts that FAIL verification |

## Quick Start

```bash
cd /path/to/tSwift

# Verify compatible contracts (PASS)
./bin/tswift-ffi-verify --swift examples/ffi/secure_buffer_import.swift \
    --rust examples/ffi/secure_buffer.rs --z4 --verbose

# Verify incompatible contracts (FAIL)
./bin/tswift-ffi-verify --swift examples/ffi/weak_import_fail.swift \
    --rust examples/ffi/secure_buffer.rs --z4 --verbose
```

## How FFI Verification Works

### The Safety Rule

When Swift calls Rust:
- **Swift's precondition must IMPLY Rust's precondition**
  - Swift can be MORE restrictive (stronger)
  - Swift cannot be LESS restrictive (weaker)
- **Rust's postcondition must IMPLY Swift's expectation**
  - Rust can guarantee MORE than Swift expects
  - Rust cannot guarantee LESS than Swift expects

### Example: secure_alloc

```
Rust requires:  size > 0 && size <= 1073741824
Swift requires: size >= 16 && size <= 1073741824  (STRONGER)

Check: (size >= 16 && size <= 1GB) => (size > 0 && size <= 1GB)
Result: PROVEN (16 > 0, so the implication holds)
```

### Example: unsafeAlloc (FAIL)

```
Rust requires:  size > 0 && size <= 1073741824
Swift requires: size > -100  (TOO WEAK!)

Check: (size > -100) => (size > 0 && size <= 1GB)
Result: COUNTEREXAMPLE: size = -50
        -50 > -100 is TRUE, but -50 > 0 is FALSE
```

## Verification Modes

### Unified Mode (Rust source available)

```bash
tswift-ffi-verify --swift imports.swift --rust lib.rs --z4
```

### Contract Mode (Rust contract file)

```bash
# Step 1: Generate contract from Rust
tswift-ffi-verify --emit-contract lib.ffi.json --rust lib.rs

# Step 2: Verify Swift against contract
tswift-ffi-verify --swift imports.swift --ffi-contract lib.ffi.json --z4
```

Contract mode is useful when:
- Rust source is in a separate repo
- You want to cache/version the contract
- CI needs deterministic verification

## Output Explanation

```
[OK] secure_alloc (Swift -> Rust)
      pass precondition: caller_requires => callee_requires (Z4 proved)
      pass postcondition: callee_ensures => caller_expects (Z4 proved)
      pass type layout: All types compatible
```

- **Z4 proved**: The SMT solver mathematically proved the implication
- **counterexample**: Z4 found a value that violates the implication
- **structural check**: Quick syntactic check (no SMT)

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All FFI bindings compatible |
| 1 | One or more incompatible bindings |
| 2 | Error (missing files, parse error) |
