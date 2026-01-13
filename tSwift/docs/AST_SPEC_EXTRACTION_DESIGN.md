# AST-Based Specification Extraction Design

**Status:** Design Document (Iteration 2)
**Author:** AI Worker
**Date:** 2026-01-01
**Supersedes:** Option D from MACRO_SPEC_TRANSPORT.md

---

## Problem Statement

Worker #1 discovered that Swift peer macros cannot generate arbitrary declarations at global scope:

```
error: 'peer' macros are not allowed to introduce arbitrary names at global scope
```

This blocks the `@_semantics` approach proposed in WORKER_DIRECTIVE_002.md Option A.

**Solution:** Extract specifications directly from custom attributes via AST access in the SIL verification pass (Option D).

---

## Architecture Overview

```
┌───────────────────────────────────────────────────────────────────┐
│                     Swift Source Code                             │
│  @requires("x > 0")                                               │
│  func positiveOnly(_ x: Int) -> Int { ... }                       │
└──────────────────────────────┬────────────────────────────────────┘
                               │ Parse + Type Check
                               ▼
┌───────────────────────────────────────────────────────────────────┐
│                        AST (AbstractFunctionDecl)                 │
│  FuncDecl {                                                       │
│    name: "positiveOnly",                                          │
│    attrs: [CustomAttr {                                           │
│      typeExpr: @requires,                                         │
│      resolvedMacro: MacroDecl("requires"),                        │
│      argList: [StringLiteralExpr("x > 0")]                        │
│    }]                                                             │
│  }                                                                │
└──────────────────────────────┬────────────────────────────────────┘
                               │ SILGen
                               ▼
┌───────────────────────────────────────────────────────────────────┐
│                        SIL (SILFunction)                          │
│  sil @$positiveOnly : $@convention(thin) (Int) -> Int {           │
│    // SILFunction has getDeclRef() → SILDeclRef                   │
│    // SILDeclRef has getAbstractFunctionDecl() → FuncDecl*        │
│  }                                                                │
└──────────────────────────────┬────────────────────────────────────┘
                               │ Verification Pass
                               ▼
┌───────────────────────────────────────────────────────────────────┐
│              extractSpecifications(SILFunction &F)                │
│                                                                   │
│  1. auto *decl = F.getDeclRef().getAbstractFunctionDecl()         │
│  2. for (auto *attr : decl->getAttrs().getAttributes<CustomAttr>())│
│  3. if (attr->getResolvedMacro()) {                               │
│       auto name = macro->getName().str();                         │
│       if (name == "requires" || name == "ensures" || ...)         │
│       → Extract string argument from attr->getArgs()              │
│     }                                                             │
└───────────────────────────────────────────────────────────────────┘
```

---

## Key Swift Compiler Classes

### Accessing AST from SIL

```cpp
// SILFunction.h
class SILFunction {
  DeclContext *getDeclContext() const;
  SILDeclRef getDeclRef() const;  // Key accessor
};

// SILDeclRef.h
struct SILDeclRef {
  ValueDecl *getDecl() const;
  AbstractFunctionDecl *getAbstractFunctionDecl() const;  // For functions
};
```

### Custom Attribute Access

```cpp
// Attr.h
class CustomAttr : public DeclAttribute {
  TypeExpr *getTypeExpr() const;           // The @attributeName
  MacroDecl *getResolvedMacro() const;     // The macro it refers to
  ArgumentList *getArgs() const;           // Arguments like ("x > 0")
};

// DeclAttributes iteration
// Attr.h / Decl.h
class DeclAttributes {
  template<typename ATTR>
  iterator_range<AttributeIterator<ATTR>> getAttributes() const;
};

// Usage:
for (auto *attr : decl->getAttrs().getAttributes<CustomAttr>()) {
  // Process each custom attribute
}
```

### String Extraction from Arguments

```cpp
// ArgumentList.h
class ArgumentList {
  Argument operator[](unsigned idx) const;
  unsigned size() const;
};

class Argument {
  Expr *getExpr() const;
};

// Expr.h
class StringLiteralExpr : public BuiltinLiteralExpr {
  StringRef getValue() const;  // The string content
};
```

---

## Implementation

### Core Extraction Function

```cpp
// VerificationPass.cpp

#include "swift/AST/Attr.h"
#include "swift/AST/Decl.h"
#include "swift/AST/Expr.h"
#include "swift/AST/MacroDecl.h"
#include "swift/SIL/SILFunction.h"

namespace swift {

struct VerificationSpec {
  enum Kind { Requires, Ensures, Invariant };
  Kind kind;
  std::string condition;
  SourceLoc location;
};

/// Extract @requires/@ensures/@invariant specifications from a SIL function
/// by accessing the underlying AST declaration's custom attributes.
std::vector<VerificationSpec> extractSpecifications(SILFunction &F) {
  std::vector<VerificationSpec> specs;

  // Step 1: Get the underlying AST declaration
  auto *decl = F.getDeclRef().getAbstractFunctionDecl();
  if (!decl) {
    // Closures and anonymous functions don't have specs
    return specs;
  }

  // Step 2: Iterate over custom attributes
  for (auto *attr : decl->getAttrs().getAttributes<CustomAttr>()) {
    // Step 3: Check if this is a macro attribute
    auto *macro = attr->getResolvedMacro();
    if (!macro) continue;

    // Step 4: Check if it's one of our verification macros
    StringRef macroName = macro->getName().str();
    VerificationSpec::Kind kind;

    if (macroName == "requires") {
      kind = VerificationSpec::Requires;
    } else if (macroName == "ensures") {
      kind = VerificationSpec::Ensures;
    } else if (macroName == "invariant") {
      kind = VerificationSpec::Invariant;
    } else {
      continue;  // Not a verification macro
    }

    // Step 5: Extract the string argument
    auto *argList = attr->getArgs();
    if (!argList || argList->size() == 0) {
      // No arguments provided - error case
      continue;
    }

    // Get the first argument's expression
    Expr *argExpr = (*argList)[0].getExpr();

    // Check if it's a string literal
    auto *stringLit = dyn_cast<StringLiteralExpr>(argExpr);
    if (!stringLit) {
      // Argument is not a string literal - error case
      continue;
    }

    // Step 6: Create the specification
    specs.push_back({
      kind,
      stringLit->getValue().str(),
      attr->getLocation()
    });
  }

  return specs;
}

} // namespace swift
```

### Integration with Verification Pass

```cpp
// SILVerificationPass.cpp

class SILVerificationPass : public SILFunctionTransform {
  void run() override {
    SILFunction *F = getFunction();

    // Check for @trusted attribute - skip verification
    if (hasTrustedAttribute(*F)) {
      return;
    }

    // Extract user-provided specifications
    auto specs = extractSpecifications(*F);

    // Log extracted specs (debug)
    LLVM_DEBUG({
      llvm::dbgs() << "Verification specs for " << F->getName() << ":\n";
      for (const auto &spec : specs) {
        llvm::dbgs() << "  @" << specKindName(spec.kind)
                     << ": \"" << spec.condition << "\"\n";
      }
    });

    // TODO: Parse condition strings into VC IR predicates
    // TODO: Generate verification conditions
    // TODO: Connect to Z4/Kani backends
  }

private:
  bool hasTrustedAttribute(SILFunction &F) {
    auto *decl = F.getDeclRef().getAbstractFunctionDecl();
    if (!decl) return false;

    for (auto *attr : decl->getAttrs().getAttributes<CustomAttr>()) {
      auto *macro = attr->getResolvedMacro();
      if (macro && macro->getName().str() == "trusted") {
        return true;
      }
    }
    return false;
  }

  StringRef specKindName(VerificationSpec::Kind kind) {
    switch (kind) {
      case VerificationSpec::Requires: return "requires";
      case VerificationSpec::Ensures: return "ensures";
      case VerificationSpec::Invariant: return "invariant";
    }
  }
};
```

---

## Testing Strategy

### Test 1: Verify Spec Extraction Works

```swift
// tests/verification/spec_extraction_test.swift
import tSwiftMacros

@requires("x > 0")
@ensures("result >= 0")
func positiveDouble(_ x: Int) -> Int {
    return x * 2
}
```

Compile with debug logging:
```bash
swiftc -Xllvm -debug-only=sil-verification tests/verification/spec_extraction_test.swift
```

Expected debug output:
```
Verification specs for $s4main14positiveDoubleSiSiF:
  @requires: "x > 0"
  @ensures: "result >= 0"
```

### Test 2: @trusted Skips Verification

```swift
@trusted
func unsafeOperation(_ ptr: UnsafePointer<Int>) -> Int {
    return ptr.pointee  // No verification generated
}
```

---

## Build Integration

### File Locations

```
~/swift-project/swift/
├── include/swift/SIL/
│   └── SILVerificationSpec.h      # Spec types (new)
├── lib/SILOptimizer/
│   └── Verification/
│       ├── CMakeLists.txt         # Build config (new)
│       ├── SILVerificationPass.cpp # Main pass (new)
│       └── SpecExtraction.cpp     # This design (new)
```

### CMake Integration

```cmake
# lib/SILOptimizer/Verification/CMakeLists.txt
add_swift_host_library(swiftSILVerification STATIC
  SILVerificationPass.cpp
  SpecExtraction.cpp)

target_link_libraries(swiftSILVerification PRIVATE
  swiftSIL
  swiftAST)
```

---

## Next Steps

1. **Create compiler/lib/SILOptimizer/Verification/ directory structure**
2. **Implement SpecExtraction.cpp** with the code above
3. **Add pass registration** to SILOptimizer pass pipeline
4. **Build modified Swift compiler**
5. **Run test case** to verify spec extraction works

---

## References

- `~/swift-project/swift/include/swift/AST/Attr.h` - CustomAttr class
- `~/swift-project/swift/include/swift/SIL/SILFunction.h` - getDeclRef()
- `~/swift-project/swift/include/swift/SIL/SILDeclRef.h` - getAbstractFunctionDecl()
- `~/swift-project/swift/lib/Sema/TypeCheckAttr.cpp:8864` - CustomAttr iteration pattern
