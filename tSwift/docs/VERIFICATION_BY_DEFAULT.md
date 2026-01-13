# Verification By Default

**tSwift follows the same design principle as tRust**

---

## Core Principle

> Everything that CAN be verified automatically MUST be verified by default.

No annotations required. If the compiler can prove a property, it proves it.

This is not opt-in verification. This is opt-out.

---

## The Pyramid

```
┌─────────────────────────────────────────────────┐
│           @trusted (opt-out)                    │  Rare, audited
├─────────────────────────────────────────────────┤
│     @requires/@ensures (refinements)            │  Business logic
├─────────────────────────────────────────────────┤
│                                                 │
│                                                 │
│         AUTOMATIC VERIFICATION                  │  Most code
│              (default)                          │
│                                                 │
│   Bounds, overflow, nil, division, unwrap       │
│                                                 │
│                                                 │
└─────────────────────────────────────────────────┘
```

---

## What tRust Proves Automatically

Evidence from `DESIGN_AUTO_VERIFICATION.md` and working examples:

### Arithmetic Safety
- Integer overflow/underflow (all ops: +, -, *, /, %)
- Division by zero
- Shift out of bounds
- Cast truncation (`u32 as u8` where value > 255)
- Negation overflow (`-i32::MIN`)

### Memory Safety
- Array/slice bounds (`arr[i]` proves `i < len`)
- Null/None dereference (`.unwrap()` on None)

### Control Flow Safety
- Unreachable code is actually unreachable
- Match exhaustiveness (with values, not just types)

---

## What tSwift Must Prove Automatically

Same categories, Swift syntax:

### Arithmetic Safety
```swift
// NO SPECS - auto-verified or auto-rejected

func add(_ a: UInt8, _ b: UInt8) -> UInt8 {
    return a + b  // ⚠️ ERROR: possible overflow
}

func guardedAdd(_ a: UInt8, _ b: UInt8) -> UInt8 {
    if a < 100 && b < 100 {
        return a + b  // ✓ VERIFIED: 99 + 99 = 198 <= 255
    }
    return 0
}

func divide(_ a: Int, _ b: Int) -> Int {
    return a / b  // ⚠️ ERROR: possible division by zero
}

func guardedDivide(_ a: Int, _ b: Int) -> Int {
    if b != 0 {
        return a / b  // ✓ VERIFIED: b != 0 from path condition
    }
    return 0
}
```

### Optional Safety
```swift
// NO SPECS - auto-verified or auto-rejected

func unsafeUnwrap(_ x: Int?) -> Int {
    return x!  // ⚠️ ERROR: x might be nil
}

func guardedUnwrap(_ x: Int?) -> Int {
    if let value = x {
        return value  // ✓ VERIFIED: x is non-nil in this branch
    }
    return 0
}

func safeUnwrap(_ x: Int?) -> Int {
    return x ?? 0  // ✓ VERIFIED: nil case handled
}
```

### Array Bounds
```swift
// NO SPECS - auto-verified or auto-rejected

func unsafeIndex(_ arr: [Int], _ i: Int) -> Int {
    return arr[i]  // ⚠️ ERROR: i might be out of bounds
}

func guardedIndex(_ arr: [Int], _ i: Int) -> Int {
    if i >= 0 && i < arr.count {
        return arr[i]  // ✓ VERIFIED: i in bounds from path condition
    }
    return 0
}

func firstElement(_ arr: [Int]) -> Int? {
    if !arr.isEmpty {
        return arr[0]  // ✓ VERIFIED: arr.count > 0
    }
    return nil
}
```

---

## Specs Are For Refinements Only

Automatic verification handles safety. Specs handle business logic:

```swift
// Automatic: overflow, bounds, nil - all handled
// Spec: business rules that compiler can't infer

@requires("account.isActive")
@requires("amount <= account.balance")
@ensures("account.balance == old(account.balance) - amount")
func withdraw(from account: inout Account, amount: UInt) {
    account.balance -= amount  // Overflow already auto-verified
}

@requires("items.count > 0")
@ensures("result == items.max()")
func findMax(_ items: [Int]) -> Int {
    // Bounds auto-verified, but "result is max" is business logic
}
```

---

## Opt-Out When Needed

### Function-Level

```swift
@trusted
func legacyCode() -> Int {
    // Not verified - developer takes responsibility
}

@trusted(.overflow)
func intentionalWrapping(_ x: UInt8) -> UInt8 {
    return x &+ 1  // Wrapping addition, intentional
}
```

### Module-Level

```swift
// At top of file
@trusted(.bounds)  // Skip bounds checks for this file
```

### Why Opt-Out Exists

1. **Legacy code** - Gradual adoption of verification
2. **Performance-critical code** - When wrapping arithmetic is intentional
3. **FFI boundaries** - Obj-C interop that can't be verified
4. **Trusted libraries** - Apple frameworks assumed correct

---

## Error Messages

When automatic verification fails:

```
error: array index may be out of bounds
 --> View.swift:15:12
   |
15 |     return items[index]
   |            ^^^^^^^^^^^^ index may be >= items.count
   |
   = counterexample: items.count = 0, index = 0
   = help: add bounds check: `if index < items.count { ... }`
   = help: or use safe access: `items[safe: index]`
   = help: or add `@trusted(.bounds)` if you know it's safe
```

```
error: integer overflow possible
 --> Math.swift:8:12
   |
 8 |     return a + b
   |            ^^^^^ addition may overflow UInt8
   |
   = counterexample: a = 200, b = 100
   = help: use checked arithmetic: `a.addingReportingOverflow(b)`
   = help: or add guard: `if a < 128 && b < 128 { ... }`
   = help: or add `@trusted(.overflow)` if intentional
```

---

## Comparison: tRust and tSwift

| Feature | tRust | tSwift |
|---------|-------|--------|
| Overflow checking | Auto | Auto |
| Bounds checking | Auto | Auto |
| Division by zero | Auto | Auto |
| Null/nil safety | Auto (Option) | Auto (Optional) |
| Path-sensitive | Yes | Yes |
| Specs for refinement | `// #[requires]` | `@requires` |
| Opt-out | `// #[trust]` | `@trusted` |
| FFI verification | Yes | Yes |

Same design. Same philosophy. Different syntax.

---

## Implementation Priority

### Phase 1: Core Safety (Default ON)
1. Integer overflow/underflow
2. Array bounds
3. Optional unwrap (force unwrap `!`)
4. Division by zero

### Phase 2: Extended Safety
5. Integer cast truncation
6. Shift bounds
7. String index safety

### Phase 3: Refinements
8. `@requires` / `@ensures` parsing
9. Custom invariants
10. FFI boundary verification

---

## Why This Matters

Traditional Swift:
```
Write code → Run tests → Find crash → Debug → Fix → Repeat
```

tSwift:
```
Write code → Compiler proves safe OR shows counterexample → Ship
```

If it compiles, it's proven. No runtime surprises.

---

## UNKNOWN Is A Signal

Sometimes the solver returns `UNKNOWN` (or times out). Treat these as high-value targets:

1. **Flag it**: surface uncertain paths to humans.
2. **Mine it**: export unknown VCs and turn them into regression tests.
3. **Learn it**: once resolved, encode the fix as tighter specs, improved VC generation, or backend improvements.

To export all `UNKNOWN`/`TIMEOUT` VCs from a verification run:

```bash
./bin/tswiftv verify file.swift --emit-unknown-vcs ./unknown_vcs.json
```

Also: don't trust LLM-generated loop bounds; use verification to check (see the "Collatz warning" in issue #15).

---

## Summary

```
┌─────────────────────────────────────────────────────────────┐
│                                                              │
│   Write normal Swift code.                                  │
│                                                              │
│   Compiler automatically proves:                            │
│   • No overflow                                             │
│   • No out-of-bounds                                        │
│   • No nil crashes                                          │
│   • No division by zero                                     │
│                                                              │
│   Add specs only for business logic.                        │
│                                                              │
│   Opt-out only when absolutely necessary.                   │
│                                                              │
│   If it compiles, it's proven.                              │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```
