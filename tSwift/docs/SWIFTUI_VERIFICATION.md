# SwiftUI Verification Workflow

This document describes how to verify SwiftUI applications with tSwift, including patterns that verify safely and common issues to avoid.

## Overview

SwiftUI verification works by analyzing the SIL (Swift Intermediate Language) generated from SwiftUI code. tSwift extracts verification conditions (VCs) for:

- **Overflow checks**: Addition, subtraction, multiplication, division, negation
- **Bounds checks**: Array index access, string index access
- **Nil checks**: Force unwrap, force try, nil coalescing
- **Cast checks**: Force cast, conditional cast

## Verified SwiftUI Patterns

### 1. @State Counter with Overflow Protection

**Safe Pattern:**
```swift
@State private var counter: Int = 0

Button("Increment") {
    if counter < Int.max {
        counter += 1  // Safe: guarded by comparison
    }
}
```

The path condition `counter < Int.max` proves the increment cannot overflow.

**Unsafe Pattern (will fail verification):**
```swift
@State private var counter: Int = 0

Button("Increment") {
    counter += 1  // Unsafe: no guard against overflow
}
```

### 2. @Binding Value Transform

**Safe Pattern:**
```swift
// @requires("value >= 0 && value <= 10")
func updateSlider(_ binding: inout Int, _ value: Int) {
    binding = value * 10  // Safe: 10 * 10 = 100, no overflow
}
```

With the precondition `value <= 10`, multiplication by 10 is provably safe.

### 3. ForEach Index Access

**Safe Pattern:**
```swift
ForEach(0..<items.count, id: \.self) { index in
    Text(items[index].name)  // Safe: index guaranteed in bounds by ForEach
}
```

ForEach with `0..<items.count` establishes the precondition `0 <= index < items.count`.

### 4. @Observable State Access with isEmpty Guard

**Safe Pattern:**
```swift
@Observable class ViewModel {
    var items: [Item] = []
}

if !viewModel.items.isEmpty {
    let first = viewModel.items[0]  // Safe: isEmpty check establishes count > 0
}
```

The path condition `!isEmpty` (i.e., `count > 0`) proves index 0 is valid.

### 5. List onDelete with Index Validation

**Safe Pattern:**
```swift
List {
    ForEach(items.indices, id: \.self) { index in
        Text(items[index].name)
    }
}
.onDelete { indexSet in
    items.remove(atOffsets: indexSet)  // Safe: indexSet from ForEach
}
```

The `ForEach(items.indices)` establishes that all indices in the IndexSet are valid.

**Unsafe Pattern (will fail verification):**
```swift
func deleteItem(at index: Int) {
    items.remove(at: index)  // Unsafe: index could be out of bounds
}
```

## Verification Commands

### Verify Swift File
```bash
tswift verify MyView.swift
```

### Verify with Verbose Output
```bash
tswift verify --verbose MyView.swift
```

### Verify SIL Directly
```bash
swiftc -emit-sil MyView.swift -o MyView.sil
tswift-verify --sil MyView.sil
```

### JSON Output
```bash
tswift verify --json MyView.swift
```

## Path Condition Tracking

tSwift tracks path conditions through control flow to prove safety. Key patterns:

1. **cond_br tracking**: Conditional branches establish path conditions
2. **switch_enum tracking**: Enum switches (like Optional) establish discriminant values
3. **guard propagation**: Guards before operations constrain variable ranges

Example:
```
bb0:
  %cmp = builtin "cmp_slt_Int64"(%value, %max) : $Builtin.Int1
  cond_br %cmp, bb1, bb2

bb1:  // path condition: value < max
  %result = builtin "sadd_with_overflow_Int64"(%value, %one, ...)
  // Overflow check verified because value < max implies value + 1 <= max
```

## Preconditions (@requires)

For functions called from SwiftUI, add preconditions:

```swift
@requires("items.count > 0")
func getFirst(_ items: [Item]) -> Item {
    return items[0]  // Verified safe due to precondition
}
```

## Test Files

See `vc-ir-swift/tests/sil_examples/` for SwiftUI verification test cases:

- `swiftui_state_counter.sil` - Safe counter increment
- `swiftui_counter_unsafe.sil` - Unsafe counter (for comparison)
- `swiftui_binding_safe.sil` - Safe binding transform
- `swiftui_foreach_bounds.sil` - Safe ForEach access
- `swiftui_observable_state.sil` - Safe observable access
- `swiftui_list_delete.sil` - Safe vs unsafe deletion

## Current Limitations

1. **Complex closures**: Very deeply nested closures may produce UNKNOWN results
2. **Generic constraints**: Generic type constraints aren't fully propagated
3. **Property wrappers**: Some property wrapper patterns need manual annotations
4. **Async/await**: Async verification is limited

## Best Practices

1. **Guard before modifying**: Always check bounds/overflow before operations
2. **Use ForEach ranges**: `ForEach(0..<count)` establishes bounds automatically
3. **Check isEmpty**: Before accessing first/last element
4. **Add preconditions**: For utility functions called from views
5. **Test unsafe patterns**: Verify that unsafe code correctly fails verification

## Related Documentation

- [AUTO_VC_DESIGN.md](AUTO_VC_DESIGN.md) - Auto-VC extraction design
- [SIL_TO_VCIR_DESIGN.md](SIL_TO_VCIR_DESIGN.md) - SIL translation details
- [SPEC_PATTERNS.md](SPEC_PATTERNS.md) - Specification patterns
