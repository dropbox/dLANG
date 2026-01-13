# PHASE 2.5: Struct Field Access in Specs

**Date**: 2024-12-31
**Priority**: HIGH - Last critical gap for practical use

## STATUS

Modular verification is COMPLETE (excellent work!). One gap remains:

```rust
struct Pair { first: i32, second: i32 }

// #[ensures(result.first == a)]  // FAILS - field not resolved
fn make_pair(a: i32, b: i32) -> Pair {
    Pair { first: a, second: b }
}
```

## THE PROBLEM

Specs like `result.first` parse but don't resolve to actual MIR field projections.

The MIR creates an Aggregate:
```
Assign { place: _0, rvalue: Aggregate { kind: Adt, operands: [Copy(_1), Copy(_2)] } }
```

But the spec `result.first == a` becomes `Var("result.first")` - a single variable name, not a field access.

## THE SOLUTION

### Step 1: Parse Field Access in specs.rs

Update the expression parser to handle `expr.field`:

```rust
fn parse_primary(&mut self) -> Option<Expr> {
    let mut expr = self.parse_atom()?;

    // Handle field access chain: expr.field1.field2
    while self.consume(".") {
        let field = self.parse_identifier_string()?;
        expr = Expr::FieldAccess {
            base: Box::new(expr),
            field,
        };
    }

    Some(expr)
}
```

Add to `expr.rs`:
```rust
pub enum Expr {
    // ... existing variants ...
    FieldAccess {
        base: Box<Expr>,
        field: String,
    },
}
```

### Step 2: Resolve Fields During Verification

In `verify.rs`, when evaluating `FieldAccess`:

```rust
fn eval_expr(&self, expr: &Expr, state: &State) -> Z3Expr {
    match expr {
        Expr::FieldAccess { base, field } => {
            // Get the base expression (e.g., _0 for "result")
            let base_val = self.eval_expr(base, state);

            // Look up field index from struct definition
            let field_idx = self.get_field_index(&base_val, field);

            // Extract field from aggregate/tuple
            self.extract_field(base_val, field_idx)
        }
        // ...
    }
}
```

### Step 3: Track Struct Definitions

Need to track which fields belong to which structs:

```rust
struct StructInfo {
    name: String,
    fields: Vec<(String, usize)>,  // (field_name, index)
}

// Build from MIR type information
fn get_struct_info(ty: &MirType) -> Option<StructInfo> {
    // Extract from Adt type
}
```

### Step 4: Handle Aggregates in WP

When processing `Assign { rvalue: Aggregate { operands } }`:
- Track that `_0.0` = `operands[0]`, `_0.1` = `operands[1]`, etc.
- Map field names to indices using struct info

## TEST CASES

```rust
// Test 1: Basic field access
struct Point { x: i32, y: i32 }
// #[ensures(result.x == a)]
// #[ensures(result.y == b)]
fn make_point(a: i32, b: i32) -> Point {
    Point { x: a, y: b }
}

// Test 2: Nested field access
struct Line { start: Point, end: Point }
// #[ensures(result.start.x == x1)]
fn make_line(x1: i32, y1: i32, x2: i32, y2: i32) -> Line {
    Line { start: Point { x: x1, y: y1 }, end: Point { x: x2, y: y2 } }
}

// Test 3: Field in precondition
// #[requires(p.x > 0)]
// #[ensures(result > 0)]
fn get_x(p: Point) -> i32 {
    p.x
}
```

## FILES TO MODIFY

1. `tools/cargo-trust/src/expr.rs` - Add `FieldAccess` variant
2. `tools/cargo-trust/src/specs.rs` - Parse `expr.field` syntax
3. `tools/cargo-trust/src/verify.rs` - Resolve field access during verification
4. `tools/cargo-trust/src/convert.rs` - May need to extract struct field info from rustc

## SUCCESS CRITERIA

```bash
$ cargo trust verify test_struct.rs
--- Verifying: make_point ---
    result.x == a: PROVEN
    result.y == b: PROVEN
  Status: ALL PROVEN
```

## AFTER THIS

Once struct fields work, focus on:
1. Array/slice indexing in specs (`arr[i]`)
2. Reference handling (`*ptr`, `&x`)
3. Method call specs (`vec.len()`)
4. Performance optimization

## DO NOT

- Do not regress existing features (modular verification, loop invariants, termination)
- Do not skip tests - verify all existing tests still pass
- Do not over-engineer - simple field access first, nested later
