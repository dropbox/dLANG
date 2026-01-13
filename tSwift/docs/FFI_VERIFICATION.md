# FFI Verification Layer: tRust ↔ tSwift ↔ tKotlin

**Verifying boundaries between languages**

---

## The Problem

Cross-language calls are trust gaps:

```
┌──────────────────┐          ┌──────────────────┐
│    Rust Code     │   ???    │   Swift Code     │
│   (verified)     │ ──────── │   (verified)     │
└──────────────────┘          └──────────────────┘
    tRust proves                  tSwift proves

    But who proves the BOUNDARY is correct?
```

---

## Solution: Unified FFI Specs

Both sides declare compatible specifications:

### Rust Side

```rust
#[swift_bridge::bridge]
mod ffi {
    #[requires(buffer.len() > 0)]
    #[ensures(!result.is_ok() || result.unwrap().bytes_consumed <= buffer.len())]
    extern "Rust" {
        fn parse_escape(buffer: &[u8]) -> Result<ParseResult, ParseError>;
    }
}
```

### Swift Side

```swift
@requires("!buffer.isEmpty")
@ensures("!result.isSuccess || result.value.bytesConsumed <= buffer.count")
func parseEscape(_ buffer: Data) -> ParseResult {
    return RustFFI.parse_escape(buffer)
}
```

### Kotlin Side (JNI)

```kotlin
@Requires("buffer.isNotEmpty()")
@Ensures("result.bytesConsumed <= buffer.size")
fun parseEscape(buffer: ByteArray): ParseResult {
    return nativeParseEscape(buffer)
}

private external fun nativeParseEscape(buffer: ByteArray): ParseResult
```

---

## Verification Conditions

### 1. Precondition Compatibility

```
VC: caller_requires => callee_requires
```

Stricter caller is OK. Weaker caller is UNSAFE.

### 2. Postcondition Compatibility

```
VC: callee_ensures => caller_expects
```

Stronger callee is OK. Weaker callee is UNSAFE.

### 3. Type Compatibility

```
VC: sizeof(rust::T) == sizeof(swift::T)
VC: alignof(rust::T) == alignof(swift::T)
```

### 4. Ownership Transfer

```
VC: lifetime(ptr) transferred correctly
VC: no double-free, no leak
```

---

## Type Mappings

### Rust ↔ Swift

| Rust | Swift | Verified |
|------|-------|----------|
| `bool` | `Bool` | Layout ✓ |
| `i32` | `Int32` | Layout ✓ |
| `&str` | `String` (borrowed) | Lifetime ✓ |
| `String` | `String` (owned) | Ownership ✓ |
| `Option<T>` | `T?` | Semantics ✓ |
| `Result<T,E>` | `throws` / custom | Semantics ✓ |

### Rust ↔ Kotlin (JNI)

| Rust | Kotlin | Verified |
|------|--------|----------|
| `bool` | `Boolean` | Layout ✓ |
| `i32` | `Int` | Layout ✓ |
| `&str` | `String` | Lifetime ✓ |
| `Vec<u8>` | `ByteArray` | Ownership ✓ |
| `Option<T>` | `T?` | Semantics ✓ |
| `Result<T,E>` | `Result<T>` / throws | Semantics ✓ |

---

## Condition Normalization (FFI)

FFI specs are written in each language’s surface syntax, but verified using a shared condition parser.
To make common Rust idioms compatible with Swift-style conditions, tSwift normalizes a small set of
Rust-only patterns before parsing:

| Rust condition idiom | Normalized form |
|---|---|
| `x.len()` | `x.count` |
| `x.iter().count()` | `x.count` |
| `x.into_iter().count()` | `x.count` |
| `x.iter_mut().count()` | `x.count` |
| `x.chars().count()` | `x.count` |
| `x.bytes().count()` | `x.utf8.count` |
| `x.lines().count()` | `x.lines.count` |
| `x.split(delim).count()` | `x.split(delim).count` |
| `x.iter().take(n).count()` | `x.take(n).count` |
| `x.iter().skip(n).count()` | `x.skip(n).count` |
| `(a..b).len()` / `(a..=b).len()` | `(b - a)` / `((b - a) + 1)` |
| `(a..b).count()` / `(a..=b).count()` | `(b - a)` / `((b - a) + 1)` |
| `(a..b).contains(&i)` / `(a..=b).contains(&i)` | `(i >= a && i < b)` / `(i >= a && i <= b)` |
| `x.is_empty()` / `!x.is_empty()` | `x.count == 0` / `x.count > 0` |
| `x.first().is_some()` / `x.first().is_none()` | `x.count > 0` / `x.count == 0` |
| `x.get(i).is_some()` / `x.get(i).is_none()` | `i < x.count` / `i >= x.count` |
| `opt.is_some()` / `opt.is_none()` | `opt != nil` / `opt == nil` |
| `res.ok().is_some()` / `res.ok().is_none()` | `res.isSuccess` / `!res.isSuccess` |
| `res.err().is_some()` / `res.err().is_none()` | `!res.isSuccess` / `res.isSuccess` |
| `res.is_ok()` / `res.is_err()` | `res.isSuccess` / `!res.isSuccess` |
| `x.unwrap()` / `x.unwrap_err()` | `x.value` / `x.error` |
| `expr as T` | `expr` |

---

## Example: Voice FFI

### Rust Core

```rust
#[swift_bridge::bridge]
#[jni_bridge]
mod voice_ffi {
    #[requires(sample_rate == 16000 || sample_rate == 48000)]
    #[ensures(result.is_ok() => session_active())]
    extern "Rust" {
        fn start_stt(sample_rate: u32) -> Result<SessionId, VoiceError>;
    }

    #[requires(!text.is_empty())]
    #[ensures(result.is_valid_uuid())]
    extern "Rust" {
        fn queue_tts(text: &str) -> Uuid;
    }
}
```

### Swift Caller

```swift
@requires("AVAudioSession.sharedInstance().recordPermission == .granted")
func startRecording() {
    let result = RustFFI.start_stt(sampleRate: 48000)  // Verified
    // ...
}
```

### Kotlin Caller

```kotlin
@Requires("hasRecordPermission()")
fun startRecording() {
    val result = RustFFI.startStt(sampleRate = 48000)  // Verified
    // ...
}
```

---

## Verification Output

```
$ trust build --verify-ffi

Verifying FFI: voice_ffi
  ├─ start_stt
  │   ├─ Swift requires ⊇ Rust requires: ✓
  │   ├─ Kotlin requires ⊇ Rust requires: ✓
  │   └─ Type layouts match: ✓
  └─ queue_tts
      ├─ Swift requires ⊇ Rust requires: ✓
      ├─ Kotlin requires ⊇ Rust requires: ✓
      └─ Type layouts match: ✓

FFI verification: 2/2 functions verified
```

---

## Implementation

### Spec Registry

```rust
pub struct FfiSpecs {
    rust_exports: HashMap<String, FfiFunction>,
    swift_imports: HashMap<String, FfiFunction>,
    kotlin_imports: HashMap<String, FfiFunction>,
}
```

### Compatibility Checker

```rust
pub fn verify_ffi_compatibility(specs: &FfiSpecs) -> Vec<VerifyResult> {
    let mut results = vec![];

    for (name, rust_fn) in &specs.rust_exports {
        // Check Swift compatibility
        if let Some(swift_fn) = specs.swift_imports.get(name) {
            results.push(verify_pre_post_compat(rust_fn, swift_fn));
            results.push(verify_type_layout(rust_fn, swift_fn));
        }

        // Check Kotlin compatibility
        if let Some(kotlin_fn) = specs.kotlin_imports.get(name) {
            results.push(verify_pre_post_compat(rust_fn, kotlin_fn));
            results.push(verify_type_layout(rust_fn, kotlin_fn));
        }
    }

    results
}
```

---

## Build Integration

FFI verification can run automatically during your build process.

### Cargo Projects (Rust)

Add a `build.rs` that runs `tswift-ffi-verify`:

```rust
// build.rs - FFI verification during cargo build
const SWIFT_FILES: &[&str] = &["../swift/Sources/FFI.swift"];
const RUST_FILES: &[&str] = &["src/ffi.rs"];

// See vc-ir-swift/build_integration/cargo_ffi_verify.rs for full template
```

Environment variables:
- `FFI_VERIFY_ENABLE=0` - Disable verification
- `FFI_VERIFY_Z4=1` - Enable semantic proofs
- `FFI_VERIFY_STRICT=1` - Fail build on mismatch

### Xcode Projects (Swift)

Add a Run Script build phase:

```bash
#!/bin/bash
tswift-ffi-verify \
    --swift "${SRCROOT}/Sources/FFI/*.swift" \
    --rust "${SRCROOT}/../rust/src/ffi.rs" \
    --verbose
```

See `vc-ir-swift/build_integration/` for complete templates:
- `cargo_ffi_verify.rs` - Cargo build.rs template
- `xcode_ffi_verify.sh` - Xcode build phase script
- `example_project/` - Working example with both Swift and Rust

### CI Integration

```yaml
# GitHub Actions
- name: Verify FFI
  run: |
    tswift-ffi-verify \
      --swift Sources/FFI/*.swift \
      --rust ../rust/src/ffi.rs \
      --z4 --json > ffi-report.json
```

---

## Tools

- **swift-bridge**: https://github.com/chinedufn/swift-bridge
- **uniffi-rs**: https://github.com/aspect-dev/uniffi-rs (multi-language)
- **jni-rs**: https://github.com/jni-rs/jni-rs
