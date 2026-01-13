# Macro to Verification Pass Spec Transport

**Status:** Design Document (Iteration 1)
**Author:** AI Worker
**Date:** 2026-01-01

---

## Problem Statement

Swift verification macros (`@requires`, `@ensures`, `@invariant`, `@trusted`) need to transport specification strings from source code to the SIL verification pass. This document explores approaches and their limitations.

---

## Swift Macro Limitations

### Issue: Arbitrary Name Generation

Swift peer macros have strict naming restrictions:
- Peer macros CANNOT introduce declarations with arbitrary names at global scope
- The `names: arbitrary` parameter is not allowed at global scope
- Peer macros can only generate names related to the original declaration

**Error Example:**
```
error: 'peer' macros are not allowed to introduce arbitrary names at global scope
```

### What We Tried

1. **`@_semantics` attribute with marker functions** - Blocked by naming restrictions
   ```swift
   // This approach is blocked:
   @_semantics("tswift.requires:...")
   private func __tswift_requires_funcName() {}
   ```

2. **Nested enums with spec storage** - Same issue
   ```swift
   // Also blocked:
   @frozen enum _$funcName_requires { ... }
   ```

3. **`names: arbitrary` declaration** - Explicitly forbidden at global scope

---

## Current Implementation

The macros currently:
1. **Validate spec syntax** - Ensure condition is a string literal
2. **Validate attachment target** - `@requires`/`@ensures` require function context
3. **Return empty** - No code generation (specs transported separately)
4. **Debug logging** - Print specs during DEBUG builds

```swift
// Current macro behavior:
@requires("x > 0")
func foo(_ x: Int) -> Int { ... }

// Expansion: (empty - specs transported via AST)
```

---

## Proposed Spec Transport Strategies

### Option A: Compiler-Side Custom Attribute Recognition (Recommended)

Add custom attribute support directly in the Swift compiler:

1. **Define attributes in `Attr.def`:**
   ```cpp
   CONTEXTUAL_SIMPLE_DECL_ATTR(Requires, DAK_Requires,
     OnFunc | OnConstructor, 99)
   ```

2. **Parse attributes in `ParseDecl.cpp`:**
   ```cpp
   case DAK_Requires:
     parseTSwiftSpecAttribute(Kind::Requires);
   ```

3. **Transfer to SIL in `SILGenFunction.cpp`:**
   ```cpp
   // Add spec to SILFunction's semantic attributes
   if (auto *requiresAttr = FD->getAttrs().getAttribute<RequiresAttr>()) {
     F->addSemanticsAttr("tswift.requires:" + requiresAttr->getCondition());
   }
   ```

**Pros:** Full integration, survives to SIL, proper tooling support
**Cons:** Requires Swift compiler modification

### Option B: Comment-Based Extraction

Use structured comments that a pre-pass extracts:

```swift
/// @tswift-requires: x > 0
/// @tswift-ensures: result >= 0
func clamp(_ x: Int) -> Int { ... }
```

**Pros:** No compiler changes needed
**Cons:** Fragile, can desync from code

### Option C: Sidecar Metadata File

Generate `.tswift-specs.json` alongside compilation:

```json
{
  "clamp": {
    "requires": ["x > 0"],
    "ensures": ["result >= 0"]
  }
}
```

**Pros:** External tooling friendly
**Cons:** Extra build step, can desync

### Option D: Source-Level Extraction

Parse specs directly from AST custom attributes in the verification pass:

```cpp
// In VerificationPass.cpp
bool extractSpecifications(SILFunction &function) {
  auto *funcDecl = function.getDeclRef().getDecl();
  for (auto *attr : funcDecl->getAttrs()) {
    if (auto *customAttr = dyn_cast<CustomAttr>(attr)) {
      // Check if it's @requires, @ensures, etc.
      // Extract the string literal argument
    }
  }
}
```

**Pros:** No compiler changes to attribute system
**Cons:** Requires AST access from SIL pass

---

## Recommendation

**Start with Option D (Source-Level Extraction)** for immediate progress:
1. Macros validate syntax at compile time
2. Verification pass reads specs from AST via DeclRef
3. No Swift compiler core changes required initially

**Migrate to Option A (Compiler-Side)** for production:
1. Proper attribute integration
2. Better tooling support
3. Cleaner architecture

---

## Next Steps

1. Implement AST-based spec extraction in verification pass
2. Test with `~/swift-project/swift` compiler build
3. Add `-verify-specs` flag to trigger extraction
4. Connect extracted specs to VC IR generation

---

## References

- Swift Macros: SE-0389, SE-0394
- `upstream/swift/include/swift/AST/Attr.def` - Attribute definitions
- `upstream/swift/lib/SILGen/SILGenFunction.cpp` - AST to SIL transfer
