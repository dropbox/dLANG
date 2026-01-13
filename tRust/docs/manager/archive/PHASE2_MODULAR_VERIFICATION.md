# PHASE 2: MODULAR VERIFICATION

**Date**: 2024-12-30
**Priority**: CRITICAL - Required for real-world use

## THE PROBLEM

cargo-trust verifies functions in isolation. It does NOT use contracts from called functions.

```rust
// abs PROVES: result >= 0
fn abs(x: i32) -> i32 { if x < 0 { -x } else { x } }

// sum_abs FAILS - verifier doesn't know abs returns >= 0
fn sum_abs(a: i32, b: i32) -> i32 {
    abs(a) + abs(b)
}
```

The verifier treats `abs(a)` as an UNINTERPRETED function - it could return anything.

## THE SOLUTION

When verifying `sum_abs`, at each `Call` terminator:
1. **Check precondition** of called function is satisfied
2. **Assume postcondition** of called function holds for return value

### Implementation Plan

#### Step 1: Build Function Contract Registry

```rust
// In verify.rs or new module contracts.rs
struct ContractRegistry {
    contracts: HashMap<String, FunctionSpec>,
}

impl ContractRegistry {
    fn get_contract(&self, func_name: &str) -> Option<&FunctionSpec> {
        self.contracts.get(func_name)
    }
}
```

#### Step 2: Modify Call Handling in WP

When processing `Call { func, args, destination, target }`:

```rust
// Pseudocode for verify.rs
fn handle_call(
    &mut self,
    func_name: &str,
    args: &[Operand],
    dest: &Place,
    registry: &ContractRegistry,
) -> Expr {
    if let Some(contract) = registry.get_contract(func_name) {
        // 1. Generate VC that precondition holds
        let pre_vc = substitute_args(&contract.preconditions, args);
        self.add_verification_condition(pre_vc, "precondition of call");

        // 2. Assume postcondition for result
        let post_assumption = substitute_result(&contract.postconditions, dest);
        return post_assumption;
    } else {
        // No contract - treat as havoc (return unknown value)
        return Expr::Var(fresh_var());
    }
}
```

#### Step 3: Substitute Arguments

Map spec variables to actual arguments:
- `x` in `abs` spec → `_1` (first arg to abs)
- `result` → destination place

```rust
fn substitute_args(spec: &Predicate, args: &[Operand]) -> Predicate {
    // Replace spec parameter names with actual argument expressions
    // e.g., if spec says "x > 0" and args[0] is Copy(_1),
    // produce "_1 > 0"
}
```

## SUCCESS CRITERIA

```bash
$ cargo trust verify /tmp/with_call.rs
--- Verifying: abs ---
  result >= 0: PROVEN

--- Verifying: sum_abs ---
  Checking precondition of abs(_1): satisfied (a >= 0)
  Checking precondition of abs(_2): satisfied (b >= 0)
  Using postcondition: abs(_1) >= 0
  Using postcondition: abs(_2) >= 0
  result >= 0: PROVEN

Functions verified: 2/2
```

## FILES TO MODIFY

1. `tools/cargo-trust/src/verify.rs` - Add contract registry, modify call handling
2. `tools/cargo-trust/src/main.rs` - Build registry from parsed specs
3. `tools/cargo-trust/src/specs.rs` - May need to track which specs belong to which functions

## ALSO FIX: Struct Field Access

Specs like `result.x == a` fail because we don't resolve field projections.

In `specs.rs`, parsing `result.x` should produce:
```rust
Expr::FieldAccess {
    base: Expr::Var("_0"),
    field: "x",
}
```

Then in verification, when the result is an Aggregate, we can extract the field.

## DO NOT

- Do not add more unit tests until modular verification works
- Do not polish existing code
- Do not fix warnings

## PRIORITY ORDER

1. Modular verification (function call contracts) - HIGHEST
2. Struct field access in specs - HIGH
3. Everything else - LATER

---

**This is the difference between a toy and a tool.**
