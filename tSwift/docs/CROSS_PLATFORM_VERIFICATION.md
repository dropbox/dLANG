# Cross-Platform Native Verification

**Verified native apps on every platform**

---

## The Stack

```
                        Shared Rust Core (tRust)
                               │
         ┌──────────┬──────────┼──────────┬──────────┐
         ▼          ▼          ▼          ▼          ▼
      tSwift     tSwift    tKotlin     tRust      tRust
       iOS       macOS     Android    Windows     Linux
     (Swift)    (Swift)   (Kotlin)    (Rust)     (Rust)
```

---

## Three Verification Tools (Not Four)

| Tool | Platforms | Language |
|------|-----------|----------|
| **tRust** | Windows, Linux, + Core | Rust |
| **tSwift** | iOS, macOS | Swift |
| **tKotlin** | Android | Kotlin |

No tCpp. Windows uses Rust with verified WinUI 3 bindings.

---

## Platform Details

### iOS / macOS - tSwift
- **Language:** Swift (open source)
- **UI:** SwiftUI, UIKit, AppKit
- **FFI:** swift-bridge

### Android - tKotlin
- **Language:** Kotlin (open source, JetBrains)
- **UI:** Jetpack Compose
- **FFI:** JNI / uniffi-rs

### Windows - tRust + Verified Bindings
- **Language:** Rust
- **UI:** WinUI 3 via custom verified bindings
- **FFI:** None (same language as core)

See: [WINDOWS_BINDINGS.md](WINDOWS_BINDINGS.md)

### Linux - tRust
- **Language:** Rust
- **UI:** GTK4, Iced, egui

---

## Why Not tCpp?

Rust already provides memory safety. C++ doesn't.

```
tRust effort  = functional correctness only
tCpp effort   = memory safety + UB + data races + functional correctness
              = 10x harder
```

Instead: Custom Rust bindings to WinUI 3 with specs. ~50 functions vs. a whole compiler.

---

## Unified VC IR

All platforms share:
- vc_ir crate (this repo)
- Z4 SMT solver
- Kani Fast bounded model checker
- Lean5 theorem prover
