# FFI Verification Build Integration

Automatically verify FFI compatibility between Swift and Rust during your build process.

## Overview

These templates integrate `tswift-ffi-verify` into your build workflow to catch FFI mismatches early:

| File | Use Case |
|------|----------|
| `cargo_ffi_verify.rs` | Rust/Cargo projects calling Swift or being called from Swift |
| `xcode_ffi_verify.sh` | Xcode/Swift projects calling Rust via FFI |

## Installation

### 1. Install tswift-ffi-verify

```bash
cargo install --git https://github.com/dropbox/dLANG/tSwift --bin tswift-ffi-verify
```

Verify installation:
```bash
tswift-ffi-verify --help
```

### 2. Choose Your Integration

## Cargo Integration (Rust Projects)

For Rust libraries that expose FFI to Swift:

1. **Add the FFI macros crate** to annotate your Rust functions:
   ```toml
   [dependencies]
   tswift-ffi-macros = { git = "https://github.com/dropbox/dLANG/tSwift", path = "vc-ir-swift/tswift-ffi-macros" }
   ```

2. **Annotate your FFI functions:**
   ```rust
   use tswift_ffi_macros::{ffi_export, ffi_requires, ffi_ensures, ffi_trusted};

   #[ffi_export]
   #[ffi_requires("x > 0")]
   #[ffi_ensures("result >= x")]
   #[no_mangle]
   pub extern "C" fn increment(x: i64) -> i64 {
       x + 1
   }
   ```

3. Copy `cargo_ffi_verify.rs` to your project as `build.rs` (or merge with existing)

4. Edit the configuration section in `build.rs`:
   ```rust
   const SWIFT_FILES: &[&str] = &[
       "../ios/Sources/FFI.swift",
   ];

   const RUST_FILES: &[&str] = &[
       "src/ffi.rs",
   ];

   const GENERATED_FILES: &[&str] = &[
       "../ios/Generated/Bridge.swift",
   ];
   ```

5. Add to `Cargo.toml`:
   ```toml
   [package]
   build = "build.rs"

   [build-dependencies]
   home = "0.5"
   which = "6"
   ```

6. Build your project:
   ```bash
   cargo build
   ```

### FFI Annotation Attributes

| Attribute | Purpose |
|-----------|---------|
| `#[ffi_export]` | Mark function as FFI export (optional: `#[ffi_export("custom_name")]`) |
| `#[ffi_requires("cond")]` | Precondition the caller must satisfy |
| `#[ffi_ensures("cond")]` | Postcondition the callee guarantees |
| `#[ffi_trusted]` | Skip verification for this function |

### Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `FFI_VERIFY_ENABLE` | `1` | Set to `0` to disable verification |
| `FFI_VERIFY_Z4` | `0` | Set to `1` for semantic proofs |
| `FFI_VERIFY_STRICT` | `0` | Set to `1` to fail build on mismatch |
| `FFI_VERIFY_SWIFT_FILES` | - | Override Swift files (comma-separated) |
| `FFI_VERIFY_RUST_FILES` | - | Override Rust files (comma-separated) |
| `FFI_VERIFY_GENERATED_FILES` | - | Override generated files (comma-separated) |
| `TSWIFT_FFI_VERIFY_BIN` | - | Custom path to tswift-ffi-verify |

Example:
```bash
FFI_VERIFY_Z4=1 FFI_VERIFY_STRICT=1 cargo build
```

## Xcode Integration (Swift Projects)

For Swift apps that call Rust via FFI:

1. In Xcode, select your target and go to "Build Phases"

2. Click "+" → "New Run Script Phase"

3. Name it "Verify FFI" and move it BEFORE "Compile Sources"

4. Either:
   - Copy contents of `xcode_ffi_verify.sh` into the script box
   - Or reference the script: `${SRCROOT}/scripts/xcode_ffi_verify.sh`

5. Edit the configuration variables at the top:
   ```bash
   SWIFT_FILES="${SRCROOT}/Sources/FFI/*.swift"
   GENERATED_FILES="${SRCROOT}/Generated/*.swift"
   RUST_FILES="${SRCROOT}/../rust/src/ffi/*.rs"
   ```

### Build Settings (optional)

Add these as custom build settings in your target:

| Setting | Default | Description |
|---------|---------|-------------|
| `FFI_VERIFY_ENABLE` | `1` | Set to `0` to disable |
| `FFI_VERIFY_Z4` | `0` | Set to `1` for semantic proofs |
| `FFI_VERIFY_STRICT` | `0` | Set to `1` to fail build on mismatch |

### Per-Configuration

For Debug builds only:
```bash
if [ "$CONFIGURATION" = "Debug" ]; then
    # ... verification script ...
fi
```

## CI Integration

Both integrations work seamlessly in CI. The JSON output is useful for CI reporting:

```yaml
# GitHub Actions example
- name: Verify FFI
  run: |
    tswift-ffi-verify \
      --swift Sources/FFI/*.swift \
      --rust ../rust/src/ffi.rs \
      --z4 --json > ffi-report.json
```

## Verification Modes

| Mode | Speed | Use Case |
|------|-------|----------|
| Structural (default) | Fast | Type signature matching |
| Z4 (`--z4`) | Slower | Semantic pre/postcondition implication proofs |

Use structural checks for rapid iteration, Z4 for release builds or CI.

## Troubleshooting

### "tswift-ffi-verify not found"

Ensure the binary is in your PATH:
```bash
export PATH="$HOME/.cargo/bin:$PATH"
```

Or set `TSWIFT_FFI_VERIFY_BIN` to the full path.

### "No FFI files found"

Check your glob patterns. Use absolute paths or `${SRCROOT}`-relative paths in Xcode.

### Build succeeds but FFI mismatched at runtime

Enable strict mode:
```bash
FFI_VERIFY_STRICT=1 cargo build
```

Or in Xcode build settings: `FFI_VERIFY_STRICT = 1`

## Testing

Both integration templates include comprehensive test suites:

### Running Tests

```bash
# Run all tests (including build integration tests) via cargo
cd vc-ir-swift && cargo test

# Run Xcode build phase tests directly
bash build_integration/test_xcode_ffi_verify.sh

# Run Cargo build.rs tests directly
bash build_integration/test_cargo_ffi_verify.sh
```

### Test Coverage

| Test Script | Tests |
|-------------|-------|
| `test_xcode_ffi_verify.sh` | 10 tests covering disable flag, missing binary, file patterns, Z4 flag, strict mode, etc. |
| `test_cargo_ffi_verify.sh` | 11 tests covering env overrides, strict/non-strict modes, Z4 flag, rerun-if-changed, etc. |

### Example Project

The `example_project/` directory contains a working Rust/Swift FFI project for testing:
- `rust_core/` - Rust library with `#[ffi_export]` annotated functions
- `swift_app/` - Swift declarations with `@_ffi_import` annotations
