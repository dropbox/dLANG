# Auto-VC Design Document

**tSwift Automatic Verification Conditions**

**Date:** 2026-01-04
**Status:** Phase 2 Complete
**Test Coverage:** 4178 passing tests (2 ignored) (lib + CLI + integration)

---

## Overview

Auto-VCs (Automatic Verification Conditions) are safety properties that tSwift proves without requiring user annotations. When Swift source is compiled to SIL, the compiler inserts runtime checks for potentially unsafe operations. tSwift extracts these checks and attempts to prove them statically.

### Philosophy

> Everything that CAN be verified automatically MUST be verified by default.

No annotations required. If the compiler can prove a property, it proves it.

---

## Auto-VC Types

tSwift currently supports **18 auto-VC types** in three categories:

### Safety Auto-VCs (10 types)

| Type | SIL Pattern | What It Detects |
|------|-------------|-----------------|
| `Overflow` | `builtin "*_with_overflow"` | Integer overflow in arithmetic |
| `DivByZero` | Division before overflow check | Division/modulo by zero |
| `BoundsCheck` | `cond_fail "Index out of range"` | Array index out of bounds |
| `NilCheck` | `switch_enum` + fail path | Force unwrap on nil |
| `CastCheck` | `unconditional_checked_cast` | Forced type cast failure |
| `CondFail` | `cond_fail` (general) | Generic runtime assertions |
| `CallPrecondition` | `apply` with preconditions | Caller must satisfy callee preconditions |
| `ShiftOverflow` | `builtin "shl/lshr/ashr"` | Shift amount >= bit width (v329) |
| `UnownedAccess` | `load_unowned` | Unowned reference access (v347) |
| `ActorIsolationCrossing` | `apply [isolation]` | Actor boundary crossings (v348) |

### Termination Auto-VCs (5 types)

| Type | Pattern | What It Proves |
|------|---------|----------------|
| `Termination` | Simple bounded loops | Loop terminates (v314) |
| `RecursiveTermination` | `f(n-1)` patterns | Recursive function terminates (v326) |
| `MutualRecursiveTermination` | Cycle of calls | Mutually recursive cycle terminates (v340) |
| `LexicographicTermination` | Multi-param recursion | Lexicographic measure decreases (v341) |
| `LexicographicMutualRecursiveTermination` | Multi-param cycle | Lexicographic mutual recursion terminates (v350) |

### State Invariant Auto-VCs (3 types)

| Type | Context | What It Verifies |
|------|---------|------------------|
| `StateInvariant` | `@_invariant` on methods | Invariant holds after mutation (v327) |
| `TypeInvariant` | `@_invariant` on init | Type-level invariant in all methods (v328) |
| `MethodCallStateEffect` | Method calls | Invariant holds after calling state-modifying method (v342) |

---

## 1. Overflow

**Purpose:** Detect integer overflow/underflow in arithmetic operations.

**SIL Pattern:**
```sil
%result = builtin "sadd_with_overflow_Int32"(%a : $Builtin.Int32, %b : $Builtin.Int32)
%value = tuple_extract %result : $(Builtin.Int32, Builtin.Int1), 0
%overflow = tuple_extract %result : $(Builtin.Int32, Builtin.Int1), 1
cond_fail %overflow : $Builtin.Int1, "arithmetic overflow"
```

**Operations:**
- `sadd` / `uadd` - Signed/unsigned addition
- `ssub` / `usub` - Signed/unsigned subtraction
- `smul` / `umul` - Signed/unsigned multiplication
- Negation (`0 - x` via `ssub_with_overflow`)

**Example:**
```swift
func addUnchecked(_ a: Int32, _ b: Int32) -> Int32 {
    return a + b  // Auto-VC: overflow possible
}
```

**Verification Result:**
- `OK` - Proven no overflow (e.g., constrained inputs)
- `FAIL` - Counterexample found (e.g., `a=2147483647, b=1`)
- `UNKNOWN` - Cannot prove/disprove (unbounded inputs)

**Note:** Negation is implemented as `0 - x`. The verifier correctly finds counterexamples like `x = Int.min` where negation overflows.

---

## 2. DivByZero

**Purpose:** Detect division or modulo by zero.

**SIL Pattern:**
```sil
// Swift inserts a zero-check before the division
%is_zero = builtin "cmp_eq_Int64"(%divisor : $Builtin.Int64, %zero : $Builtin.Int64)
cond_fail %is_zero : $Builtin.Int1, "Division by zero"
%result = builtin "sdiv_Int64"(%dividend, %divisor)
```

**Operations:**
- `sdiv` / `udiv` - Signed/unsigned division
- `srem` / `urem` - Signed/unsigned modulo (remainder)

**Example:**
```swift
func divideUnchecked(_ a: Int, _ b: Int) -> Int {
    return a / b  // Auto-VC: b might be zero
}

func divideGuarded(_ a: Int, _ b: Int) -> Int {
    if b != 0 {
        return a / b  // Auto-VC: PROVEN (path condition: b != 0)
    }
    return 0
}
```

---

## 3. BoundsCheck

**Purpose:** Detect array/buffer index out of bounds.

**SIL Pattern:**
```sil
%len = struct_extract %array : $Array<Int>, #Array._count
%in_bounds = builtin "cmp_slt_Int64"(%index, %len)
%negated = builtin "xor_Int1"(%in_bounds, %true)
cond_fail %negated : $Builtin.Int1, "Index out of range"
```

**Example:**
```swift
func unsafeIndex(_ arr: [Int], _ i: Int) -> Int {
    return arr[i]  // Auto-VC: i might be out of bounds
}

func safeIndex(_ arr: [Int], _ i: Int) -> Int {
    if i >= 0 && i < arr.count {
        return arr[i]  // Auto-VC: PROVEN (path condition: 0 <= i < count)
    }
    return 0
}
```

**Note:** tSwift extracts both the index and length expressions from SIL to generate the verification condition `0 <= index < length`.

---

## 4. NilCheck

**Purpose:** Detect force unwrap (`!`) on nil optionals.

**SIL Pattern:**
```sil
switch_enum %optional : $Optional<T>, case #Optional.some!enumelt: bb_some, case #Optional.none!enumelt: bb_none

bb_none:
  // Trap instruction or unreachable leading to runtime crash
  builtin "int_trap"()
  unreachable
```

**Example:**
```swift
func forceUnwrap(_ x: Int?) -> Int {
    return x!  // Auto-VC: x might be nil
}

func safeUnwrap(_ x: Int?) -> Int {
    if let value = x {
        return value  // No auto-VC needed (value is non-optional)
    }
    return 0
}
```

**Note:** The verifier tracks `switch_enum` branches. In the `.some` branch, the optional is known to be non-nil. In the `.none` branch leading to a trap, an auto-VC is generated.

---

## 5. CastCheck

**Purpose:** Detect forced type cast (`as!`) failures.

**SIL Pattern:**
```sil
%result = unconditional_checked_cast %value : $Base to $Derived
```

or via `checked_cast_br`:
```sil
checked_cast_br %value : $Base to $Derived, bb_success, bb_fail

bb_fail:
  builtin "int_trap"()
  unreachable
```

**Example:**
```swift
func unsafeCast(_ obj: Any) -> String {
    return obj as! String  // Auto-VC: obj might not be String
}

func safeCast(_ obj: Any) -> String? {
    return obj as? String  // No auto-VC (conditional cast returns optional)
}
```

**Precondition Syntax: `is_type()`**

To prove a forced cast is safe, use the `is_type()` precondition syntax:

```swift
@requires("is_type(animal, type_Dog)")
func safeCast(_ animal: Animal) -> Dog {
    return animal as! Dog  // Auto-VC: PROVEN (precondition guarantees type)
}
```

**Format:** `is_type(variable, type_TypeName)`

- The first argument is the variable being cast
- The second argument is `type_` followed by the target type name
- Type names are sanitized (special characters replaced with `_`)

**SIL Example:**
```sil
@_requires("is_type(animal, type_Dog)")
func safeCast(_ animal: Animal) -> Dog

sil hidden @safeCast : $@convention(thin) (@guaranteed Animal) -> @owned Dog {
bb0(%0 : $Animal):
  debug_value %0, let, name "animal", argno 1
  %2 = unconditional_checked_cast %0 : $Animal to $Dog
  return %2
}
```

The verifier generates `is_type(animal, type_Dog)` for the cast and matches it against the precondition.

---

## 6. CondFail

**Purpose:** Catch generic runtime assertions inserted by the compiler.

**SIL Pattern:**
```sil
cond_fail %condition : $Builtin.Int1, "message"
```

**Common Uses:**
- Integer truncation bounds (e.g., `Int8(x)` where x > 127)
- Range bounds validity (`start <= end` for `start..<end` and `start...end`)
- Precondition failures
- Assert statements
- Compiler-inserted safety checks

**Example (Integer Truncation):**
```swift
func truncateToInt8(_ x: Int) -> Int8 {
    return Int8(x)  // Auto-VC: x might not fit in Int8
}
```

The compiler inserts bounds checks:
```sil
%lower_ok = builtin "cmp_sge_Int64"(%x, %min_int8)  // x >= -128
%upper_ok = builtin "cmp_sle_Int64"(%x, %max_int8)  // x <= 127
%both_ok = builtin "and_Int1"(%lower_ok, %upper_ok)
%fail = builtin "xor_Int1"(%both_ok, %true)
cond_fail %fail : $Builtin.Int1, "Not enough bits..."
```

---

## 7. CallPrecondition

**Purpose:** Ensure callers satisfy callee's `@requires` preconditions.

**SIL Pattern:**
```sil
// Function with @requires annotation
sil @verified_function : $@convention(thin) (Int) -> Int {
  // metadata: requires "x > 0"
}

// Call site
%result = apply @verified_function(%arg)  // Auto-VC: x > 0 must hold
```

**Example:**
```swift
@requires("x > 0")
func sqrt(_ x: Double) -> Double { ... }

func callSqrt(_ value: Double) -> Double {
    return sqrt(value)  // Auto-VC: value > 0 must be proven
}
```

---

## 8. ShiftOverflow (v329)

**Purpose:** Detect invalid shift amounts that would cause undefined behavior.

**SIL Pattern:**
```sil
%result = builtin "shl_Int64"(%value : $Builtin.Int64, %amount : $Builtin.Int64)
// OR
%result = builtin "lshr_Int64"(%value : $Builtin.Int64, %amount : $Builtin.Int64)
// OR
%result = builtin "ashr_Int64"(%value : $Builtin.Int64, %amount : $Builtin.Int64)
```

**Operations:**
- `shl` - Shift left (`<<`)
- `lshr` - Logical shift right (`>>` for unsigned)
- `ashr` - Arithmetic shift right (`>>` for signed)

**Example:**
```swift
func shiftBy(_ x: Int, _ n: Int) -> Int {
    return x << n  // Auto-VC: 0 <= n < 64
}

func shiftByFour(_ x: Int) -> Int {
    return x << 4  // No VC needed: constant 4 is always valid
}
```

**Verification:**
- VCs generated only for variable shift amounts
- Constant shifts in valid range are skipped (optimization)
- Proves: `0 <= shift_amount < bit_width`

---

## 9. UnownedAccess (v347)

**Purpose:** Flag potentially unsafe unowned reference accesses.

**SIL Pattern:**
```sil
%ref = load_unowned %addr : $*@sil_unowned T
```

**Example:**
```swift
class Node {
    unowned var parent: Node?

    func getParent() -> Node? {
        return parent  // Auto-VC: unowned reference access flagged
    }
}
```

**Verification Result:**
- Typically returns UNKNOWN without user-provided lifetime guarantees
- Forces explicit documentation of lifetime assumptions
- Use `@_trusted` or `@_requires` to document safety guarantees

**Note:** Weak references (`weak var`) are safe and don't generate VCs - they return `nil` if the object is deallocated.

---

## 10. ActorIsolationCrossing (v348)

**Purpose:** Flag when function calls cross actor isolation boundaries.

**SIL Pattern:**
```sil
%result = apply [caller_isolation=nonisolated] [callee_isolation=actor_instance] %func(%arg)
```

**Example:**
```swift
actor DataManager {
    var data: [String] = []
    func process() { ... }
}

func caller(manager: DataManager) async {
    await manager.process()  // Auto-VC: nonisolated → actor_instance crossing
}
```

**Isolation Types:**
- `nonisolated` - No actor isolation
- `actor_instance` - Isolated to specific actor instance
- `@MainActor` (global actor) - Main thread isolation

**Use Cases:**
- FFI verification: ensure Rust code is safe to call from actor context
- Auditing: visibility into where actor boundaries are crossed
- Custom isolation requirements

---

## Path Conditions

Auto-VCs are **path-sensitive**. The verifier tracks conditions from:

1. **`cond_br` instructions** - if/else branches
2. **`switch_enum` instructions** - optional unwrapping, enum matching
3. **`checked_cast_br` instructions** - conditional type casts

**Example:**
```swift
func guardedDivide(_ a: Int, _ b: Int) -> Int {
    if b != 0 {             // Path condition: b != 0
        return a / b        // Auto-VC includes path condition
    }
    return 0
}
```

The generated VC is: `(b != 0) => (b != 0)`, which is trivially true.

---

## Verification Results

Each auto-VC produces one of these results:

| Result | Meaning |
|--------|---------|
| `OK` | Property proven to always hold |
| `FAIL` | Counterexample found showing violation |
| `UNKNOWN` | Cannot prove or disprove (e.g., unbounded inputs) |
| `TIMEOUT` | Solver exceeded time limit |
| `ERROR` | Internal error during verification |

**Example Output:**
```
$ ./bin/tswiftv verify test.swift --verbose
[VC 1/3] addNumbers spec (ensures_0): OK
[VC 2/3] addNumbers auto (overflow): UNKNOWN (unbounded integers)
[VC 3/3] divideNumbers auto (div_by_zero): FAIL
         Counterexample: b = 0
```

---

## Error Messages and Fix Suggestions

When verification fails, tSwift provides actionable diagnostics:

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

---

## SIL Instruction Coverage

### Currently Supported

| SIL Instruction | Auto-VC Generated |
|-----------------|-------------------|
| `builtin "*_with_overflow"` | Overflow |
| `builtin "*div*"` | DivByZero (+ potential Overflow) |
| `builtin "*rem*"` | DivByZero (modulo) |
| `builtin "shl/lshr/ashr"` | ShiftOverflow (v329) |
| `cond_fail` | CondFail/BoundsCheck/Overflow |
| `switch_enum` | NilCheck (when path leads to trap) |
| `unconditional_checked_cast` | CastCheck |
| `checked_cast_br` | CastCheck (fail path) |
| `apply` | CallPrecondition (if callee has @requires) |
| `apply [isolation]` | ActorIsolationCrossing (v348) |
| `load_unowned` | UnownedAccess (v347) |
| Loop patterns | Termination (v314-v350) |
| `store`/`modify` | StateInvariant/TypeInvariant (v327-v328) |
| Method calls | MethodCallStateEffect (v342) |

### Not Applicable

| SIL Pattern | Reason |
|-------------|--------|
| Wrapping arithmetic (`&+`, `&-`, `&*`) | Intentionally wrapping |

**Note:** Shift operations now generate `ShiftOverflow` VCs (v329) to verify shift amounts are within valid range.

---

## Implementation Details

### Source Files

- `vc-ir-swift/src/json_types.rs` - `SwiftAutoVc` enum definition
- `vc-ir-swift/src/sil_to_vcir.rs` - SIL → auto-VC extraction
- `vc-ir-swift/src/ffi.rs` - Auto-VC verification logic
- `vc-ir-swift/src/convert.rs` - Auto-VC → VC IR conversion
- `vc-ir-swift/src/bin/tswift_verify.rs` - CLI output formatting

### Test Coverage

**Total tests:** 4178 passing (2 ignored) (run via `cargo test` in vc-ir-swift)

- **Unit tests:** `vc-ir-swift/src/tests.rs` and inline module tests
- **CLI e2e tests:** `vc-ir-swift/tests/cli_*.rs`
- **SIL fixture tests:** `vc-ir-swift/tests/sil_examples/*.sil` (126 fixtures)

Each auto-VC type has dedicated test coverage:
- Overflow: signed/unsigned add/sub/mul/neg
- DivByZero: signed/unsigned div/mod
- BoundsCheck: array indexing
- NilCheck: force unwrap
- CastCheck: forced type casts
- CondFail: integer truncation
- CallPrecondition: @requires propagation
- ShiftOverflow: shift amount bounds (shl/lshr/ashr)

---

## Future Work

### Potential Auto-VC Additions

1. **String index safety** - UTF-8 index bounds (currently inside stdlib, not exposed as `cond_fail`)
2. **Capacity checks** - Collection capacity vs count

**Note:** Range bounds (`start <= end`) is now detected via CondFail auto-VC (see section 6).

### SwiftUI Patterns

SwiftUI uses many runtime checks that could benefit from verification:
- View identity stability
- State mutation ordering
- Binding validity

---

## Summary

```
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│   18 Auto-VC Types:                                             │
│                                                                 │
│   Safety (10):                                                  │
│   • Overflow (add/sub/mul/neg)                                 │
│   • DivByZero (div/mod)                                        │
│   • BoundsCheck (array index)                                  │
│   • NilCheck (force unwrap)                                    │
│   • CastCheck (as!)                                            │
│   • CondFail (truncation, assertions)                          │
│   • CallPrecondition (@requires)                               │
│   • ShiftOverflow (<<, >>)                                     │
│   • UnownedAccess (unowned references)                         │
│   • ActorIsolationCrossing (actor boundaries)                  │
│                                                                 │
│   Termination (5):                                              │
│   • Termination, RecursiveTermination                          │
│   • MutualRecursiveTermination, LexicographicTermination       │
│   • LexicographicMutualRecursiveTermination                    │
│                                                                 │
│   State Invariants (3):                                         │
│   • StateInvariant, TypeInvariant, MethodCallStateEffect       │
│                                                                 │
│   Path-sensitive: guards are tracked and used in proofs        │
│   Actionable: counterexamples and fix suggestions provided     │
│                                                                 │
│   4178 passing tests (2 ignored) (lib + CLI + integration)     │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```
