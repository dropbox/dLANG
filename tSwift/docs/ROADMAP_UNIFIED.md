# Unified Verification Roadmap

**tRust + tSwift + tKotlin = Verified Native Apps Everywhere**

---

## The Stack

```
┌─────────────────────────────────────────────────────────────────────┐
│                        Your Applications                             │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐ │
│  │   dterm     │  │ dashterm2   │  │    voice    │  │Dash White-  │ │
│  │             │  │             │  │             │  │   label     │ │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘ │
└─────────┼────────────────┼────────────────┼────────────────┼────────┘
          │                │                │                │
          ▼                ▼                ▼                ▼
┌─────────────────────────────────────────────────────────────────────┐
│                     Platform UI Layers                               │
│                                                                      │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │
│  │   tSwift     │  │   tKotlin    │  │    tRust     │              │
│  │  iOS/macOS   │  │   Android    │  │   Windows    │              │
│  │              │  │              │  │              │              │
│  │  SwiftUI     │  │  Compose     │  │Verified WinUI│              │
│  │  UIKit       │  │  Views       │  │  Bindings    │              │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘              │
│         │                 │                 │                       │
│         └────────────┬────┴────────────┬────┘                       │
│                      │  FFI Verified   │                            │
│                      ▼                 ▼                            │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                     tRust Core                                │  │
│  │                                                               │  │
│  │   Parser │ Grid │ MediaServer │ LLM Client │ Voice │ ...     │  │
│  │                                                               │  │
│  └──────────────────────────────────────────────────────────────┘  │
│                              │                                      │
└──────────────────────────────┼──────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    Shared Verification Infrastructure                │
│                                                                      │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │                        VC IR                                  │  │
│  │              (Verification Condition IR)                      │  │
│  └──────────────────────────┬───────────────────────────────────┘  │
│                             │                                       │
│            ┌────────────────┼────────────────┐                     │
│            ▼                ▼                ▼                     │
│       ┌─────────┐     ┌─────────┐     ┌─────────┐                 │
│       │   Z4    │     │  Kani   │     │  Lean5  │                 │
│       │   SMT   │     │  Fast   │     │         │                 │
│       └─────────┘     └─────────┘     └─────────┘                 │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## Implementation Phases

### Phase 1: Foundation (Current)
**Goal:** tRust core verification working

- [x] VC IR design
- [x] MIR → VC translation
- [x] Z4 SMT backend
- [ ] Path-sensitive verification (in progress)
- [ ] "Hello, Verified World" milestone

**Deliverable:** Verified Rust core for all apps

---

### Phase 2: Apple Platforms (AUTO-VCs COMPLETE, KANI COMPLETE)
**Goal:** tSwift verification for iOS/macOS
**Status:** Auto-VC extraction complete, Kani end-to-end complete, 775+ commits, 4178 passing tests (2 ignored)

| Task | Effort | Status |
|------|--------|--------|
| Fork Swift compiler | 1 commit | ✓ Complete |
| Implement @requires/@ensures macros | 3 commits | ✓ Complete |
| SIL analysis pass | 5 commits | ✓ Complete |
| swift-bridge to VC IR | 3 commits | ✓ Complete |
| Auto-VC extraction | 20 commits | ✓ Complete (18 types) |
| Path condition tracking | 3 commits | ✓ Complete |
| SwiftUI verification | 5 commits | ✓ Complete (StateInvariant, TypeInvariant, MethodCallStateEffect VCs) |
| FFI boundary verification | 3 commits | ✓ Complete (tswift-ffi-verify CLI, 21 integration tests) |
| Kani end-to-end pipeline | 5 commits | ✓ Complete (bitvector mode, counterexamples, overflow detection) |

**Current capabilities:**
- Overflow detection (add/sub/mul/neg)
- Division by zero detection
- Array bounds checking
- Nil unwrap checking
- Forced cast checking
- Integer truncation
- Shift overflow detection
- Callee precondition propagation
- Unowned reference access flagging
- Actor isolation crossing detection
- Basic/mutual/lexicographic termination checking
- StateInvariant/TypeInvariant/MethodCallStateEffect VCs
- Kani backend with bitvector mode and counterexample parsing
- Z3 fallback for non-linear arithmetic

**Deliverable:** Verified Swift UI calling verified Rust core

---

### Phase 3: Android
**Goal:** tKotlin verification for Android

| Task | Effort | Dependencies |
|------|--------|--------------|
| Study Kotlin IR | Research | None |
| kotlinc plugin or fork | 2 commits | KIR understanding |
| Implement @Requires/@Ensures | 3 commits | Plugin working |
| KIR → VC IR translation | 5 commits | VC IR |
| JNI verification | 3 commits | FFI design |
| Compose verification | 5 commits | Basic verification |

**Deliverable:** Verified Kotlin UI calling verified Rust core via JNI

---

### Phase 4: Windows
**Goal:** Native Windows verification via Rust + Verified WinUI Bindings

No tCpp needed. Rust already provides memory safety. Custom bindings add specs to ~50-100 Windows API functions.

| Task | Effort | Dependencies |
|------|--------|--------------|
| Core window management bindings | 2 commits | tRust |
| WinUI 3 control bindings | 3 commits | Core bindings |
| Direct2D/DirectWrite bindings | 2 commits | Core bindings |
| System integration (tray, notifications) | 1 commit | Core bindings |

See: [WINDOWS_BINDINGS.md](WINDOWS_BINDINGS.md) for detailed design.

**Deliverable:** Verified Rust Windows UI with native WinUI 3 look and feel

---

### Phase 5: Linux
**Goal:** Native Linux desktop

Already covered by tRust - Rust GTK4/Iced/egui all verified by same toolchain.

---

## Timeline (AI Commits)

```
Phase 1: tRust Foundation     ████████████░░░░░░░░  ~20 commits remaining
Phase 2: tSwift               ████████████████████  COMPLETE (362+ commits, Kani/FFI/SwiftUI)
Phase 3: tKotlin              ░░░░░░░░░░░░░░░░░░░░  ~20 commits
Phase 4: Windows (Rust)       ░░░░░░░░░░░░░░░░░░░░  ~8 commits
Phase 5: Linux                ░░░░░░░░░░░░░░░░░░░░  ~5 commits (reuse tRust)
```

**Three verification tools total:** tRust, tSwift, tKotlin

---

## Repository Map

```
~/
├── tRust/                    # This repo
│   ├── vc_ir/                # Shared by ALL verification tools
│   ├── backends/
│   │   ├── z4/
│   │   ├── kani_fast/
│   │   └── lean5/
│   ├── compiler/rustc_vc/
│   └── docs/tswift/          # Cross-platform planning docs
│
├── tSwift/                   # To be created
│   ├── swift/                # Fork of apple/swift
│   └── tswift-macros/
│
├── tKotlin/                  # To be created
│   └── kotlin/               # Fork or plugin
│
├── dterm/                    # Your terminal app
│   ├── core/                 # Rust (verified by tRust)
│   ├── ios/                  # Swift (verified by tSwift)
│   ├── macos/                # Swift (verified by tSwift)
│   ├── android/              # Kotlin (verified by tKotlin)
│   └── windows/              # Rust (verified by tRust)
│
├── dashterm2/                # iTerm2 fork
│   ├── core/                 # Extract to Rust
│   └── ui/                   # Migrate Obj-C → Swift
│
├── voice/                    # Voice functionality
│   └── ...                   # Rust core + native wrappers
│
└── dash-whitelabel/          # Native LLM client
    ├── core/                 # Rust
    ├── ios/                  # Swift
    ├── android/              # Kotlin
    └── windows/              # Rust or C++
```

---

## Success Metrics

### Per Platform

| Platform | Metric | Target |
|----------|--------|--------|
| All | Core logic verified | 100% of annotated functions |
| iOS | SwiftUI screens verified | 100% of data-bound views |
| Android | Compose verified | 100% of state-holding composables |
| Windows | UI verified | 100% of critical paths |
| FFI | Boundary verified | 100% of cross-language calls |

### Overall

| Metric | Target |
|--------|--------|
| Verification success rate | >95% first try |
| Runtime bugs post-verification | ~0 |
| Performance vs unverified | Equal or better |

---

## Next Immediate Steps

1. **Complete tRust Phase 1** - Path-sensitive verification
2. ~~**Clone Swift compiler** - Start tSwift~~ COMPLETE
3. **Design unified build** - Single command builds verified app for all platforms
4. **Lean 5 backend** - Interactive proofs for complex properties (Future)

---

## Summary Table

| Platform | Language | Compiler | UI Framework | FFI | Status |
|----------|----------|----------|--------------|-----|--------|
| **Core** | Rust | tRust | - | - | In Progress |
| **iOS** | Swift | tSwift | SwiftUI/UIKit | swift-bridge | **COMPLETE** |
| **macOS** | Swift | tSwift | SwiftUI/AppKit | swift-bridge | **COMPLETE** |
| **Android** | Kotlin | tKotlin | Compose | JNI/uniffi | Future |
| **Windows** | Rust | tRust | Verified WinUI bindings | Native | Future |
| **Linux** | Rust | tRust | GTK4/Iced | Native | Future |

All platforms share:
- **VC IR** - Common verification format
- **Z4/Kani/Lean** - Proof backends
- **FFI Verification** - Boundary checking

**Note:** Windows uses Rust with custom verified WinUI 3 bindings (~50-100 functions), not a separate tCpp compiler.
