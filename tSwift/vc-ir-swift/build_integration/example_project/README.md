# Example: FFI Verification Integration

This example demonstrates automatic FFI verification between Swift and Rust.

## Project Structure

```
example_project/
├── rust_core/           # Rust library with FFI exports
│   ├── Cargo.toml
│   ├── build.rs         # Build script with FFI verification
│   └── src/lib.rs       # FFI-exported functions
└── swift_app/           # Swift app importing Rust functions
    └── Sources/
        ├── FFI.swift    # FFI import declarations
        └── main.swift   # Example usage
```

## Building

### 1. Build tswift-ffi-verify

```bash
cd /path/to/tSwift/vc-ir-swift
cargo build --release --bin tswift-ffi-verify
```

### 2. Build the Rust core

```bash
cd rust_core

# Standard build (FFI verification as warnings)
cargo build

# With Z4 semantic proofs
FFI_VERIFY_Z4=1 cargo build

# Strict mode (fail on mismatch)
FFI_VERIFY_STRICT=1 cargo build
```

### 3. Build the Swift app

Link against the Rust library and build:
```bash
cd swift_app
swiftc -L ../rust_core/target/debug -lexample-core Sources/*.swift -o example_app
./example_app
```

## What Gets Verified

The build script checks:

1. **Type compatibility**: Swift `Int64` matches Rust `i64`
2. **Signature match**: Parameter counts and names align
3. **Precondition implication**: Swift requires ⊇ Rust requires
4. **Postcondition implication**: Rust ensures ⊇ Swift ensures

## Expected Output

```
cargo:warning=Running FFI verification...
cargo:warning=FFI: [OK] factorial (Swift -> Rust)
cargo:warning=FFI: [OK] safe_divide (Swift -> Rust)
cargo:warning=FFI: [OK] clamp (Swift -> Rust)
cargo:warning=FFI:
cargo:warning=FFI: Summary: 3 compatible, 0 incompatible, 0 unknown
cargo:warning=FFI verification passed
```

## Creating Incompatibilities

Try modifying `FFI.swift` to create a mismatch:

```swift
// Change requires to something incompatible
@_ffi_import(
    rust_name: "factorial",
    requires: "n >= -10",  // Weaker than Rust's "n >= 0"
    ensures: "result >= 1"
)
```

Build with strict mode to see the failure:
```bash
FFI_VERIFY_STRICT=1 FFI_VERIFY_Z4=1 cargo build
```
