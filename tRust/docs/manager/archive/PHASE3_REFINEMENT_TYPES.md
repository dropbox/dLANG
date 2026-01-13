# PHASE 3: Refinement Types

**Date**: 2024-12-30
**Priority**: HIGH - Next major language feature after modular verification
**Estimated Complexity**: 6-10 AI commits

## Overview

Refinement types extend the type system with predicates that constrain values. Instead of just `i32`, you can have `i32 where self > 0` (positive integers). The compiler proves these predicates at type boundaries.

## Current State

The verification infrastructure from Phase 2.5 provides:
- MIR type representation (`MirType` in `mir.rs`)
- Expression parsing (`Expr` in `expr.rs` and `specs.rs`)
- Predicate verification with Z3 (`verify.rs`)
- Modular verification (function contracts)

## Goals

1. Parse refinement type syntax
2. Check refinements at function boundaries
3. Support subtyping (refined type is subtype of base type)
4. Integrate with existing function specs

## Design

### 3.1 Refinement Type Syntax

Two forms to support:

**Form A: Type alias with refinement**
```rust
// #[type_alias]
// type Positive = i32 where self > 0;

// #[type_alias]
// type NonEmpty<T> = Vec<T> where self.len() > 0;
```

**Form B: Inline refinement (shorthand)**
```rust
// #[requires(n: i32 where n > 0)]  // Alternative to #[requires(n > 0)]
fn foo(n: i32) -> i32 { ... }
```

For Phase 3.1, we focus on **Form A** as type aliases are more reusable.

### 3.2 Implementation Approach

#### Step 1: Parse Type Alias Specifications

Add parsing for type alias refinements in `specs.rs`:

```rust
/// A refinement type definition
pub struct RefinementType {
    pub name: String,                    // "Positive"
    pub base_type: String,               // "i32"
    pub type_params: Vec<String>,        // ["T"] for NonEmpty<T>
    pub predicate: Predicate,            // self > 0
    pub location: Option<SourceLocation>,
}

/// Parse refinement type definitions from source
pub fn parse_refinement_types(source: &str) -> Vec<RefinementType> {
    // Look for patterns like:
    // // type Positive = i32 where self > 0;
    // or as attribute:
    // #[refined(where = "self > 0")]
    // type Positive = i32;
}
```

#### Step 2: Track Refinement Types During Verification

In `verify.rs`, maintain a registry of refinement types:

```rust
pub struct RefinementRegistry {
    types: HashMap<String, RefinementType>,
}

impl RefinementRegistry {
    pub fn get_refinement(&self, type_name: &str) -> Option<&RefinementType> {
        self.types.get(type_name)
    }

    /// Check if a type has a refinement (directly or via alias)
    pub fn get_predicate_for_type(&self, ty: &MirType) -> Option<&Predicate> {
        match ty {
            MirType::Adt { name } => self.types.get(name).map(|r| &r.predicate),
            _ => None,
        }
    }
}
```

#### Step 3: Generate Verification Conditions for Refinements

At type boundaries (function parameters, return values), check that the refinement holds:

```rust
// When parameter has refined type:
fn foo(x: Positive) { ... }

// Generated VC:
// 1. At call site: prove x > 0 before calling foo
// 2. Inside foo: assume x > 0

// When return type is refined:
fn bar() -> Positive { ... }

// Generated VC:
// At return: prove result > 0 before returning
```

#### Step 4: Subtyping

`Positive` is a subtype of `i32`. This means:
- Anywhere an `i32` is expected, a `Positive` can be used (coercion)
- Anywhere a `Positive` is expected from an `i32`, proof is needed

```rust
fn takes_i32(x: i32) { ... }
fn returns_positive() -> Positive { ... }

let p: Positive = returns_positive();
takes_i32(p);  // OK: Positive coerces to i32 (subtype)

let i: i32 = 42;
// let p2: Positive = i;  // Requires proof that i > 0
```

### 3.3 File Changes

| File | Changes |
|------|---------|
| `mir.rs` | Add `RefinedType` variant or refinement field to `MirType` |
| `expr.rs` | No changes needed (already supports `self` as identifier) |
| `specs.rs` | Add `parse_refinement_types()`, `RefinementType` struct |
| `verify.rs` | Add `RefinementRegistry`, check refinements at boundaries |
| `convert.rs` | Extract refinement info from rustc if using attributes |
| `main.rs` | Pass refinement types to verifier |

### 3.4 Test Cases

```rust
// test_refinement_basic.rs

// type Positive = i32 where self > 0;

// #[requires(n > 0)]  // Implies Positive
// #[ensures(result > 0)]  // Returns Positive
fn double_positive(n: i32) -> i32 {
    n * 2  // Needs proof that n * 2 > 0 when n > 0
}

// #[ensures(result > 0)]
fn always_one() -> i32 {
    1  // Trivially satisfies result > 0
}

// type Index = usize where self < array.len();  // Dependent type (Phase 3.3)
```

### 3.5 Limitations (Deferred to Later)

1. **Dependent types**: Refinements that reference other values (`Index` depends on `array`)
2. **Inference**: Automatically inferring refinements
3. **Generic refinements**: `fn first<T>(v: Vec<T> where v.len() > 0) -> &T`

## Implementation Checklist

### Phase 3.1: Basic Refinement Types (COMPLETE - commit #30)
- [x] Add `RefinementTypeDef` struct to `specs.rs`
- [x] Parse `// type Name = Base where predicate;` syntax
- [x] Add `RefinementRegistry` to `verify.rs`
- [x] Unit tests for parsing refinement types (27 unit tests)
- [x] Integration test: `examples/refinement_test.rs` (4/4)

### Phase 3.2: Subtyping (COMPLETE - commit #31)
- [x] Add `param_refinements` and `return_refinement` to `FunctionSpec`
- [x] Parse `// #[param_type(n: Positive)]` annotations
- [x] Parse `// #[return_type(NonNegative)]` annotations
- [x] Implement `expand_spec_refinements()` in `RefinementRegistry`
- [x] Integration test: `examples/refinement_subtype_test.rs` (4/4)
- [x] Unit tests for Phase 3.2 parsing (31 total unit tests)

### Phase 3.3: Generic Refinements (COMPLETE - commits #32, #33)
- [x] Add method call support in predicate parsing (e.g., `self.len()`) - commit #32
- [x] Handle generic instantiation - commit #33
  - Added `is_generic()` and `instantiate()` methods to `RefinementTypeDef`
  - Added `get_or_instantiate()` method to `RefinementRegistry`
  - Updated `expand_spec_refinements()` to use `get_or_instantiate()`
  - Added 12 unit tests for generic instantiation
- [x] Test generic refinement types - commit #33
  - Added `examples/generic_refinement_test.rs` (4/4 verified)

### Phase 3.4: Signature-Based Inference (COMPLETE - commit #34)
- [x] Infer refinement types from function signatures
  - Added `parse_signature_types()` to extract parameter/return type names from syn AST
  - Automatically generates `param_refinements`/`return_refinement` when signature types match known refinement types
  - Works for generic instantiations (e.g., `fn foo(x: NonEmpty<i32>)`)
- [x] Test signature-based inference
  - Added `examples/signature_refinement_test.rs` (3/3 verified)
- Note: Using `// #[param_type(...)]` and `// #[return_type(...)]` is no longer required when the function signature uses refinement type names

## Success Criteria

```bash
$ cargo trust verify test_refinement.rs
=== tRust Verification ===
File: test_refinement.rs

Refinement types loaded:
  Positive = i32 where self > 0

--- Verifying: double_positive ---
  Checking: result satisfies Positive (self > 0): PROVEN
  Status: ALL PROVEN

--- Verifying: use_positive ---
  Checking: argument satisfies Positive: PROVEN
  Status: ALL PROVEN

=== Verification Summary ===
Functions verified: 2/2
```

## Dependencies

- Phase 2.5 complete (modular verification with contracts) - DONE
- Z3 integration working - DONE
- Expression parsing for predicates - DONE

## Notes

Refinement types are a stepping stone to:
- **Liquid Types** (Phase 3.4): Automatic refinement inference
- **Dependent Types**: Refinements that reference program values
- **Session Types**: Refinements on protocol states

## References

- Liquid Types: https://goto.ucsd.edu/~rjhala/papers/liquid_types.pdf
- Refinement Types for ML: https://www.cs.cmu.edu/~rwh/papers/refinements/popl91.pdf
- F*: https://www.fstar-lang.org/
