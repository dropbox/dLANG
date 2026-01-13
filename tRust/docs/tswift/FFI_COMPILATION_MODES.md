# FFI Compilation Modes

**Three modes for cross-language verification. Use the strongest one possible.**

---

## What is FFI?

**FFI = Foreign Function Interface**

The mechanism for one language to call functions in another language.

```
Swift ──FFI──► Rust    (Swift calls Rust function)
Rust  ──FFI──► Swift   (Rust calls Swift callback)
Kotlin ─FFI──► Rust    (Kotlin calls Rust via JNI)
```

---

## Three Compilation Modes

| Mode | Bugs Caught | Use Case |
|------|-------------|----------|
| **Unified** | **Most** | Same repo, full control |
| **Contract Files** | Many | Separate repos, teams |
| **One-Sided** | Some | External libraries |

**Rule: Catching bugs is the priority. Default depends on your role:**

| Your Role | Default Mode |
|-----------|--------------|
| Building an app (control both sides) | **Unified** |
| Publishing a library (don't control consumers) | **Contract** (generate for consumers) |
| Consuming a library (don't control source) | **Contract** or **One-Sided** |

---

## Mode 1: Unified Compilation (Strongest)

Both languages compiled together. Full cross-language verification.

```
┌─────────────────────────────────────────────────────────────────┐
│                      trust build                                 │
│                                                                  │
│  ┌─────────────┐         ┌─────────────┐                        │
│  │   Rust      │         │   Swift     │                        │
│  │   Sources   │         │   Sources   │                        │
│  └──────┬──────┘         └──────┬──────┘                        │
│         │                       │                                │
│         ▼                       ▼                                │
│  ┌─────────────┐         ┌─────────────┐                        │
│  │   tRust     │         │   tSwift    │                        │
│  │   Parse     │         │   Parse     │                        │
│  └──────┬──────┘         └──────┬──────┘                        │
│         │                       │                                │
│         └───────────┬───────────┘                                │
│                     ▼                                            │
│         ┌─────────────────────┐                                  │
│         │   Unified VC IR     │                                  │
│         │                     │                                  │
│         │  • Rust VCs         │                                  │
│         │  • Swift VCs        │                                  │
│         │  • FFI boundary VCs │                                  │
│         └──────────┬──────────┘                                  │
│                    │                                             │
│                    ▼                                             │
│         ┌─────────────────────┐                                  │
│         │   Joint Verification │                                 │
│         │                     │                                  │
│         │  • Type compatibility│                                 │
│         │  • Pre/post compat  │                                  │
│         │  • Ownership xfer   │                                  │
│         │  • Callback safety  │                                  │
│         └──────────┬──────────┘                                  │
│                    │                                             │
│                    ▼                                             │
│         ┌─────────────────────┐                                  │
│         │   Native Binaries   │                                  │
│         └─────────────────────┘                                  │
└─────────────────────────────────────────────────────────────────┘
```

### What Unified Mode Catches

```swift
// Swift side
func processData(_ data: Data) {
    let result = RustCore.parse(data)  // Call to Rust
    handleResult(result)
}

// Rust side
#[requires(data.len() > 0)]
#[ensures(result.is_valid())]
fn parse(data: &[u8]) -> ParseResult { ... }
```

**Unified mode verifies:**
- ✓ Swift caller satisfies `data.len() > 0`
- ✓ Swift correctly handles `result.is_valid()` guarantee
- ✓ `Data` and `&[u8]` have compatible layouts
- ✓ Ownership transfers correctly (no double-free, no leak)
- ✓ If Swift passes callback to Rust, callback specs match

### Bugs Unified Catches That Contract Mode Misses

| Bug Type | Example | Why Contract Misses It |
|----------|---------|------------------------|
| **Contract drift** | Contract says `ensures(x > 0)` but Rust code was changed to return 0 | Contract file is stale, not regenerated |
| **Callback round-trip** | Swift passes callback → Rust calls it → Swift state changes → Rust uses stale data | Contract only checks one direction at a time |
| **Transitive specs** | Rust `parse()` calls `validate()` which has stricter ensures | Contract only exports top-level specs |
| **Shared mutable state** | Both Swift and Rust modify a shared buffer | Contract can't express cross-language aliasing |
| **Spec under-approximation** | Rust actually returns `[1, 100]` but contract only says `> 0` | Contract is weaker than implementation |
| **Timing/ordering** | Swift expects callback before return, Rust calls after | Temporal properties need joint analysis |

**Example: Contract Drift**

```rust
// Rust v1.0 - contract generated
#[ensures(result.len() <= 1024)]
fn compress(data: &[u8]) -> Vec<u8> { ... }

// Rust v1.1 - code changed, forgot to regenerate contract
#[ensures(result.len() <= 2048)]  // CHANGED!
fn compress(data: &[u8]) -> Vec<u8> { ... }
```

```swift
// Swift - still using old contract
let compressed = RustCore.compress(data)
var buffer = [UInt8](repeating: 0, count: 1024)
buffer[0..<compressed.count] = compressed  // 💥 Buffer overflow if > 1024
```

- **Contract mode**: Passes (Swift trusts stale contract)
- **Unified mode**: Fails (sees actual Rust code, catches mismatch)

**Example: Callback Round-Trip**

```rust
// Rust
fn process_with_callback<F: FnMut(i32)>(data: &[i32], mut callback: F) {
    for item in data {
        callback(*item);  // Calls Swift
    }
    // Rust continues using `data` here...
}
```

```swift
// Swift
var items = [1, 2, 3]
RustCore.processWithCallback(&items) { value in
    items.append(value)  // Mutates while Rust iterating!
}
```

- **Contract mode**: Can't see Swift mutates during callback
- **Unified mode**: Detects aliasing violation

### When to Use

- Same repository (monorepo)
- Same team controls both Rust and Swift
- Maximum safety required
- New projects

### Command

```bash
# Unified build
trust build --unified

# Or in Cargo.toml / Package.swift
[package.metadata.trust]
ffi-mode = "unified"
```

---

## Mode 2: Contract Files (Strong)

Separate compilation with contract exchange.

```
┌─────────────────────────────────────────────────────────────────┐
│                     RUST COMPILATION                             │
│                                                                  │
│  ┌─────────────┐                                                │
│  │   Rust      │                                                │
│  │   Sources   │                                                │
│  └──────┬──────┘                                                │
│         │                                                        │
│         ▼                                                        │
│  ┌─────────────┐         ┌─────────────────┐                    │
│  │   tRust     │────────►│  core.ffi.json  │ (contract file)    │
│  │   Compile   │         └────────┬────────┘                    │
│  └──────┬──────┘                  │                             │
│         │                         │                             │
│         ▼                         │                             │
│  ┌─────────────┐                  │                             │
│  │  libcore.a  │                  │                             │
│  └─────────────┘                  │                             │
└───────────────────────────────────┼─────────────────────────────┘
                                    │
                                    ▼
┌───────────────────────────────────┼─────────────────────────────┐
│                     SWIFT COMPILATION                            │
│                                    │                             │
│  ┌─────────────┐         ┌────────┴────────┐                    │
│  │   Swift     │         │  core.ffi.json  │ (imported)         │
│  │   Sources   │         └────────┬────────┘                    │
│  └──────┬──────┘                  │                             │
│         │                         │                             │
│         └────────────┬────────────┘                             │
│                      ▼                                           │
│         ┌─────────────────────┐                                  │
│         │   tSwift Compile    │                                  │
│         │                     │                                  │
│         │  Verifies Swift     │                                  │
│         │  against contract   │                                  │
│         └──────────┬──────────┘                                  │
│                    │                                             │
│                    ▼                                             │
│         ┌─────────────────────┐                                  │
│         │      App.app        │                                  │
│         └─────────────────────┘                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Contract File Format

```json
{
  "version": "1.0",
  "crate": "dterm-core",
  "hash": "sha256:abc123...",
  "functions": {
    "parse_escape": {
      "symbol": "_dterm_parse_escape",
      "params": [
        {"name": "buffer", "type": "slice<u8>", "ownership": "borrow"}
      ],
      "returns": {"type": "Result<ParseResult, Error>", "ownership": "owned"},
      "requires": [
        "buffer.len() > 0",
        "buffer.len() <= 1024"
      ],
      "ensures": [
        "result.is_ok() => result.unwrap().bytes_consumed <= buffer.len()"
      ],
      "panics": false,
      "thread_safe": true
    }
  },
  "types": {
    "ParseResult": {
      "layout": {"size": 16, "align": 8},
      "fields": [
        {"name": "bytes_consumed", "type": "usize", "offset": 0},
        {"name": "action", "type": "Action", "offset": 8}
      ]
    }
  },
  "callbacks": {
    "on_output": {
      "params": [{"name": "data", "type": "slice<u8>"}],
      "requires": ["data.len() <= 4096"],
      "ensures": []
    }
  }
}
```

### What Contract Mode Catches

- ✓ Swift satisfies Rust preconditions
- ✓ Type layouts match (size, alignment)
- ✓ Ownership correctly transferred
- ✓ Callbacks implemented with correct specs
- ✗ Cannot verify Rust internal changes (trusts contract)

### When to Use

- Separate repositories
- Rust library published as package
- Different teams for Rust and Swift
- CI/CD pipelines separate

### Commands

```bash
# Rust side: generate contract
trust build --emit-ffi-contract

# Swift side: verify against contract
tswift build --ffi-contract=path/to/core.ffi.json
```

---

## Mode 3: One-Sided Contracts (Basic)

Trust the library, verify your usage only.

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                  │
│  External Library (no source access)                            │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │                                                          │    │
│  │   libexternal.a  +  external.ffi.json                   │    │
│  │                                                          │    │
│  │   (You trust this. Cannot verify internals.)            │    │
│  │                                                          │    │
│  └─────────────────────────────────────────────────────────┘    │
│                              │                                   │
│                              ▼                                   │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │   Your Code                                              │    │
│  │                                                          │    │
│  │   Verified that YOU call the library correctly.         │    │
│  │   Library internals assumed correct.                    │    │
│  │                                                          │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Hand-Written Contract

When library doesn't provide a contract, write one yourself:

```swift
// MyContracts.swift - Hand-written specs for external library

@ffi_contract("libcrypto")
enum CryptoContracts {
    @requires("key.count == 32")
    @ensures("result.count == plaintext.count + 16")
    static func encrypt(plaintext: Data, key: Data) -> Data

    @requires("key.count == 32")
    @requires("ciphertext.count >= 16")
    static func decrypt(ciphertext: Data, key: Data) -> Data?
}
```

### What One-Sided Mode Catches

- ✓ Your code satisfies stated preconditions
- ✗ Cannot verify library implements postconditions
- ✗ Cannot verify type layouts (trust documentation)
- ✗ Library bugs will not be caught

### When to Use

- Third-party closed-source libraries
- System libraries (Apple frameworks, Win32)
- Legacy code you can't modify
- Gradual adoption

### Trust Boundary

```swift
// Explicitly mark as trusted
@trusted("Apple framework - assumed correct")
import UIKit

// Your code verified against UIKit's documented behavior
// UIKit internals not verified
```

---

## Mode Selection Logic

```
┌─────────────────────────────────────────────────────────────┐
│                  CHOOSE FFI MODE                             │
│                                                              │
│  Do you have source code for both sides?                    │
│                    │                                         │
│           ┌───────┴───────┐                                 │
│           ▼               ▼                                 │
│          YES              NO                                │
│           │               │                                 │
│           ▼               ▼                                 │
│  Same build system?    Does library provide                 │
│           │            .ffi.json contract?                  │
│    ┌──────┴──────┐            │                             │
│    ▼             ▼     ┌──────┴──────┐                      │
│   YES            NO    ▼             ▼                      │
│    │             │    YES            NO                     │
│    ▼             ▼     │             │                      │
│ ┌──────┐   ┌──────────┐│        ┌────┴────┐                │
│ │UNIFIED│  │ CONTRACT ││        │ONE-SIDED│                │
│ │ MODE  │  │  FILES   │◄────────│  MODE   │                │
│ └──────┘   └──────────┘         └─────────┘                │
│                                                              │
│ Strongest    Strong           Basic                         │
└─────────────────────────────────────────────────────────────┘
```

---

## Hybrid: Mixed Modes in One Project

Real projects use multiple modes:

```
┌─────────────────────────────────────────────────────────────────┐
│                        dterm iOS App                             │
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │  UNIFIED MODE                                              │  │
│  │                                                            │  │
│  │  dterm-core (Rust) ◄──────► dterm-ios (Swift)             │  │
│  │                                                            │  │
│  │  Same repo, full verification                             │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │  CONTRACT MODE                                             │  │
│  │                                                            │  │
│  │  voice-engine (Rust) ────► voice.ffi.json                 │  │
│  │  (separate repo)           (published contract)           │  │
│  │                                                            │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │  ONE-SIDED MODE                                            │  │
│  │                                                            │  │
│  │  UIKit, SwiftUI, AVFoundation                             │  │
│  │  (Apple frameworks - trusted)                             │  │
│  │                                                            │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Configuration

### Cargo.toml (Rust side)

```toml
[package.metadata.trust]
# Generate contract file on build
emit-ffi-contract = true
ffi-contract-path = "target/ffi/core.ffi.json"

# For unified mode with Swift
unified-swift-sources = ["../ios/Sources/**/*.swift"]
```

### Package.swift (Swift side)

```swift
let package = Package(
    name: "dterm-ios",
    dependencies: [
        .package(path: "../core"),  // Unified mode
    ],
    targets: [
        .target(
            name: "DTermApp",
            dependencies: ["DTermCore"],
            swiftSettings: [
                .unsafeFlags([
                    "-ffi-contract", "path/to/core.ffi.json",  // Contract mode
                    "-trust-framework", "UIKit",  // One-sided mode
                ])
            ]
        )
    ]
)
```

---

## Summary

| Mode | Source Access | Bugs Caught | Trust |
|------|--------------|-------------|-------|
| **Unified** | Both sides | **Maximum** | None needed |
| **Contract** | One side | Many | Contract accurate |
| **One-Sided** | Your code only | Some | Library correct |

**Catching bugs is the priority. Unified is the default.**

```
┌─────────────────────────────────────────────────────────────┐
│                                                              │
│   UNIFIED MODE = DEFAULT                                    │
│                                                              │
│   Catches the most bugs. Use this unless you can't.         │
│                                                              │
│   Fall back to Contract mode only when:                     │
│   • Different repositories                                  │
│   • Different teams with separate build systems             │
│                                                              │
│   Fall back to One-Sided only when:                         │
│   • No source access (third-party library)                  │
│   • System frameworks (UIKit, Win32)                        │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```
