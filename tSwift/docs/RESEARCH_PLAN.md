# tSwift Research Plan

**Formal Verification for Swift - Native iOS/macOS Development**

---

## Executive Summary

tSwift is a fork of Apple's Swift compiler that integrates formal verification directly into compilation. Combined with tRust, it enables end-to-end verified native applications.

---

## Architecture

### Shared VC IR

Both tRust and tSwift emit to the same Verification Condition IR:

```
┌─────────────┐     ┌─────────────┐
│   tRust     │     │   tSwift    │
│  (rustc)    │     │  (swiftc)   │
│     ↓       │     │     ↓       │
│    MIR      │     │    SIL      │
└──────┬──────┘     └──────┬──────┘
       └─────────┬─────────┘
                 ↓
          ┌─────────────┐
          │   VC IR     │  ← Shared representation
          └──────┬──────┘
                 ↓
     ┌───────────┼───────────┐
     ↓           ↓           ▼
  ┌─────┐   ┌─────────┐  ┌──────┐
  │ Z4  │   │  Kani   │  │ Lean │
  │ SMT │   │  Fast   │  │  5   │
  └─────┘   └─────────┘  └──────┘
```

---

## Swift Compiler Background

### Key Directories (github.com/apple/swift)

```
SwiftCompilerSources/   - Core compiler (partially Swift)
lib/Parse/             - Recursive-descent parser
lib/Sema/              - Semantic analysis, type inference
lib/SILGen/            - AST → SIL lowering
lib/SILOptimizer/      - SIL transformations
lib/IRGen/             - SIL → LLVM IR
include/swift/SIL/     - SIL definitions
```

### SIL (Swift Intermediate Language)

SIL is ideal for verification:
- Explicit ownership (borrow, consume, copy)
- SSA form
- Explicit control flow
- Rich type information
- ARC operations visible

---

## Technical Approach

### Phase 1: Specification Language

Use Swift 5.9+ macros:

```swift
@attached(peer)
public macro requires(_ condition: String) = #externalMacro(
    module: "tSwiftMacros",
    type: "RequiresMacro"
)

@attached(peer)
public macro ensures(_ condition: String) = #externalMacro(
    module: "tSwiftMacros",
    type: "EnsuresMacro"
)

// Usage
@requires("index >= 0 && index < array.count")
@ensures("result == array[index]")
func safeGet<T>(_ array: [T], at index: Int) -> T {
    return array[index]
}
```

### Phase 2: SIL Analysis Pass

Add verification pass to Swift compiler:

```
lib/SILOptimizer/
└── Verification/
    ├── SpecExtractor.cpp      // Extract specs from macros
    ├── VCGenerator.cpp        // Generate VCs
    ├── SILToVCIR.cpp          // SIL → VC IR
    └── VerificationPass.cpp   // Main pass
```

### Phase 3: VC IR Integration

Connect to tRust's backend via swift-bridge:

```rust
#[swift_bridge::bridge]
mod vc_ir_bridge {
    extern "Rust" {
        fn verify(vc: &VerificationCondition) -> VerifyResult;
    }
}
```

---

## Swift-Specific Challenges

### 1. ARC (Reference Counting)

```swift
@ensures("result.retainCount == 1")
func createObject() -> MyClass {
    return MyClass()
}
```

### 2. Optionals

```swift
@requires("array.count > 0")
@ensures("result != nil")
func first<T>(_ array: [T]) -> T? {
    return array.first
}
```

### 3. Actors

```swift
actor Counter {
    @invariant("value >= 0")
    private var value: Int = 0

    @ensures("value == old(value) + 1")
    func increment() {
        value += 1
    }
}
```

### 4. Objective-C Interop

```swift
@objc class LegacyBridge: NSObject {
    @trusted  // Cannot fully verify Obj-C runtime
    @objc func legacyMethod() -> NSString
}
```

---

## Milestones

### Milestone 1: "Hello, Verified Swift"

```swift
#![trust_level(.verified)]

@requires("n > 0")
@ensures("result >= 1 && result <= n")
func clampPositive(_ n: Int, _ val: Int) -> Int {
    if val < 1 { return 1 }
    else if val > n { return n }
    else { return val }
}
```

### Milestone 2: FFI Verification

Swift-Rust boundary verified.

### Milestone 3: SwiftUI Verification

State machine verification for UI.

### Milestone 4: Actor Verification

Concurrent code verification.

---

## Project Structure

```
tSwift/
├── swift/                  # Fork of apple/swift
├── tswift-macros/          # Swift macro package
├── vc-ir-swift/            # Swift bindings to vc_ir
└── tests/
    └── verification/       # Test cases
```

---

## References

- Swift Compiler: https://github.com/apple/swift
- swift-bridge: https://github.com/chinedufn/swift-bridge
- Swift Macros: SE-0382, SE-0389
