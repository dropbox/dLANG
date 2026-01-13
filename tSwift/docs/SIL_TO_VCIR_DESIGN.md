# SIL → VC IR Translation Design

**Status:** Design Document (Iteration 0)
**Author:** AI Worker
**Date:** 2026-01-01

---

## Overview

This document specifies how Swift Intermediate Language (SIL) is translated to Verification Condition IR (VC IR) for formal verification.

**Goal:** Translate SIL instructions into VC IR that can be verified by Z4/Kani/Lean backends.

---

## Key SIL Instructions for Verification

Based on analysis of `upstream/swift/include/swift/SIL/SILNodes.def` and `SILInstruction.h`.

### Category 1: Arithmetic (Overflow Detection)

| SIL Pattern | Swift Code | VC Generated |
|-------------|------------|--------------|
| `builtin "sadd_with_overflow"` | `a + b` (signed) | `a + b >= INT_MIN && a + b <= INT_MAX` |
| `builtin "uadd_with_overflow"` | `a + b` (unsigned) | `a + b <= UINT_MAX` |
| `builtin "ssub_with_overflow"` | `a - b` (signed) | `a - b >= INT_MIN && a - b <= INT_MAX` |
| `builtin "usub_with_overflow"` | `a - b` (unsigned) | `a >= b` (no underflow) |
| `builtin "smul_with_overflow"` | `a * b` (signed) | `a * b >= INT_MIN && a * b <= INT_MAX` |
| `builtin "umul_with_overflow"` | `a * b` (unsigned) | `a * b <= UINT_MAX` |

**Example SIL:**
```sil
%5 = builtin "sadd_with_overflow_Int64"(%3 : $Builtin.Int64, %4 : $Builtin.Int64) : $(Builtin.Int64, Builtin.Int1)
%6 = tuple_extract %5 : $(Builtin.Int64, Builtin.Int1), 0
%7 = tuple_extract %5 : $(Builtin.Int64, Builtin.Int1), 1
cond_fail %7 : $Builtin.Int1, "arithmetic overflow"
```

**Translation to VC IR:**
```rust
VerificationCondition {
    name: "addition_no_overflow",
    span: <source location>,
    condition: VcKind::Predicate(
        Predicate::and(
            Expr::ge(Expr::add(a, b), Expr::int(i64::MIN)),
            Expr::le(Expr::add(a, b), Expr::int(i64::MAX))
        )
    ),
    preferred_backend: Some(BackendHint::Smt),
}
```

### Category 2: Division by Zero

| SIL Pattern | Swift Code | VC Generated |
|-------------|------------|--------------|
| `builtin "sdiv"` | `a / b` (signed) | `b != 0` |
| `builtin "udiv"` | `a / b` (unsigned) | `b != 0` |
| `builtin "srem"` | `a % b` (signed) | `b != 0` |
| `builtin "urem"` | `a % b` (unsigned) | `b != 0` |

**Translation to VC IR:**
```rust
VcKind::Predicate(Predicate::ne(divisor, Expr::int(0)))
```

### Category 3: Array Bounds

| SIL Pattern | Swift Code | VC Generated |
|-------------|------------|--------------|
| `index_addr %base, %index` | `array[i]` | `i >= 0 && i < array.count` |

**SIL Pattern:**
```sil
// Array subscript access
%addr = index_addr %baseAddr : $*Element, %index : $Builtin.Word
%value = load %addr : $*Element
```

**Translation to VC IR:**
```rust
VcKind::Predicate(Predicate::and(
    Expr::ge(index, Expr::int(0)),
    Expr::lt(index, array_count)
))
```

### Category 4: Optional/Nil Safety

| SIL Pattern | Swift Code | VC Generated |
|-------------|------------|--------------|
| `unchecked_enum_data %val : $Optional<T>, #Optional.some` | `x!` | `x != nil` |
| `unchecked_take_enum_data_addr` | Force unwrap | `optional != nil` |

**SIL Pattern:**
```sil
// Force unwrap Optional<Int>
%value = unchecked_enum_data %optional : $Optional<Int>, #Optional.some!enumelt
```

**Translation to VC IR:**
```rust
VcKind::Predicate(Predicate::not(Predicate::is_none(optional)))
```

---

## Control Flow and Path Sensitivity

### Branch Instructions

| SIL Instruction | Purpose |
|-----------------|---------|
| `br %bb` | Unconditional branch |
| `cond_br %cond, %trueBB, %falseBB` | Conditional branch |
| `switch_enum %val, case #...` | Enum switch |
| `switch_value %val, case ...` | Value switch |

### Path Condition Collection

For path-sensitive verification, collect conditions along execution paths:

```
Entry
 │
 ├─[cond_br %0]─┬── true_bb: path_condition = %0
 │              └── false_bb: path_condition = !%0
 │
 └─[switch_enum %1]─┬── case .some: path_condition = is_some(%1)
                    └── case .none: path_condition = is_none(%1)
```

**Translation:**
```rust
// At each verification point, the VC is:
VcKind::Implies {
    antecedent: path_condition,  // Accumulated from branches
    consequent: property_to_verify,
}
```

---

## Memory and Ownership

### Key Instructions

| SIL Instruction | Purpose | VC Relevance |
|-----------------|---------|--------------|
| `load %addr` | Load from address | May need bounds check for addr |
| `store %val to %addr` | Store to address | May need bounds check |
| `begin_borrow %ref` | Start borrow | Ownership tracking |
| `end_borrow %ref` | End borrow | Ownership tracking |
| `copy_value %ref` | Copy (retain) | ARC safety |
| `destroy_value %ref` | Destroy (release) | Use-after-free prevention |

### ARC Verification

For reference counting, generate VCs ensuring:
1. No use-after-release
2. No double-release
3. Balanced retain/release in non-ARC contexts

---

## Type Mapping: Swift → VC IR

| Swift Type | VC IR Type |
|------------|------------|
| `Bool` | `VcType::Bool` |
| `Int8/16/32/64` | `VcType::Int { signed: true, bits: N }` |
| `UInt8/16/32/64` | `VcType::Int { signed: false, bits: N }` |
| `Float` | `VcType::Float { bits: 32 }` |
| `Double` | `VcType::Float { bits: 64 }` |
| `[T]` / `Array<T>` | `VcType::Array { elem: T, len: Some(n) }` |
| `Optional<T>` | `VcType::Tuple(vec![VcType::Bool, T])` (tag + value) |
| `(T1, T2, ...)` | `VcType::Tuple(vec![T1, T2, ...])` |
| `struct S { ... }` | `VcType::Struct { name, fields }` |
| `class C` | `VcType::Ref { mutable: true, inner: ... }` |
| `inout T` | `VcType::Ref { mutable: true, inner: T }` |

---

## Verification Pass Architecture

### Pass Registration

Following Swift compiler patterns from `SwiftCompilerSources/`:

```swift
// In SwiftCompilerSources/Sources/Optimizer/FunctionPasses/

let verificationConditionGeneration = FunctionPass(name: "verification-condition-generation") {
    (function: Function, context: FunctionPassContext) in

    // 1. Skip if @trusted
    if function.hasAttribute(.trusted) {
        return
    }

    // 2. Collect verification conditions
    var vcCollector = VCCollector(function: function)
    for block in function.blocks {
        vcCollector.collectFromBlock(block)
    }

    // 3. Emit VCs for verification
    for vc in vcCollector.conditions {
        context.emitVerificationCondition(vc)
    }
}
```

### VCCollector Structure

```swift
struct VCCollector {
    let function: Function
    var conditions: [VerificationCondition] = []
    var pathConditions: [Predicate] = []  // Current path conditions

    mutating func collectFromBlock(_ block: BasicBlock) {
        for inst in block.instructions {
            collectFromInstruction(inst)
        }
    }

    mutating func collectFromInstruction(_ inst: Instruction) {
        switch inst {
        case let builtin as BuiltinInst:
            collectFromBuiltin(builtin)
        case let indexAddr as IndexAddrInst:
            collectBoundsCheck(indexAddr)
        case let uncheckedEnumData as UncheckedEnumDataInst:
            collectNilCheck(uncheckedEnumData)
        case let condBr as CondBranchInst:
            updatePathConditions(condBr)
        // ... other cases
        default:
            break
        }
    }
}
```

---

## Integration with tRust VC IR

### Swift Bridge (vc-ir-swift/)

Use swift-bridge to call into the shared VC IR Rust crate:

```rust
// In vc-ir-swift/src/lib.rs (Rust side)
#[swift_bridge::bridge]
mod ffi {
    extern "Rust" {
        type VerificationCondition;
        type Predicate;
        type Expr;

        fn create_overflow_vc(
            name: String,
            file: String,
            line: u32,
            lhs: Expr,
            rhs: Expr,
            op: String,
            bits: u32,
            signed: bool,
        ) -> VerificationCondition;

        fn create_bounds_vc(
            name: String,
            file: String,
            line: u32,
            index: Expr,
            length: Expr,
        ) -> VerificationCondition;

        fn verify_all(vcs: Vec<VerificationCondition>) -> VerifyResult;
    }
}
```

```swift
// In Swift side
import VcIrSwift

func emitOverflowVC(
    at location: SILLocation,
    lhs: SILValue,
    rhs: SILValue,
    operation: String,
    type: SILType
) {
    let vc = VcIrSwift.createOverflowVc(
        name: "overflow_check",
        file: location.file,
        line: location.line,
        lhs: translateExpr(lhs),
        rhs: translateExpr(rhs),
        op: operation,
        bits: type.bitWidth,
        signed: type.isSigned
    )
    emitVc(vc)
}
```

---

## Implementation Phases

### Phase 1: Core Infrastructure (This Iteration)
- [ ] Design document (this file)
- [ ] Key SIL instruction mapping

### Phase 2: VC Collection Pass
- [ ] Create Swift pass skeleton in SwiftCompilerSources/
- [ ] Implement builtin instruction handling (overflow)
- [ ] Implement basic path condition tracking

### Phase 3: Swift-Bridge Integration
- [ ] Set up vc-ir-swift/ with swift-bridge
- [ ] Create FFI layer for VC creation
- [ ] Connect to Z4 backend

### Phase 4: Full Auto-Verification
- [ ] Bounds checking (index_addr)
- [ ] Nil checking (unchecked_enum_data)
- [ ] Division by zero
- [ ] Test suite

---

## Testing Strategy

### Unit Tests

```swift
// tests/verification/overflow_safe.swift
func guardedAdd(_ a: UInt8, _ b: UInt8) -> UInt8 {
    if a < 100 && b < 100 {
        return a + b  // Should verify: 99 + 99 = 198 <= 255
    }
    return 0
}
// Expected: PASS - VC proven by Z4
```

```swift
// tests/verification/overflow_unsafe.swift
func unsafeAdd(_ a: UInt8, _ b: UInt8) -> UInt8 {
    return a + b  // Should fail: 200 + 100 overflows
}
// Expected: FAIL - Counterexample: a=200, b=100
```

### Integration Tests

```bash
# Run all verification tests
cd tSwift && swift test --filter verification
```

---

## References

- `upstream/swift/include/swift/SIL/SILNodes.def` - All SIL instructions
- `upstream/swift/include/swift/SIL/SILInstruction.h` - Instruction classes
- `upstream/swift/include/swift/AST/Builtins.def` - Builtin operations
- `~/tRust/vc_ir/src/lib.rs` - Shared VC IR definition
- `SwiftCompilerSources/Sources/Optimizer/` - Swift pass examples
