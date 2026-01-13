# Modular Verification

Modular verification allows you to verify functions independently by using contracts. Instead of inlining callee code, the verifier uses callee contracts.

## Why Modular Verification?

Without modular verification:
```rust,ignore
fn helper(x: i32) -> i32 { x + 1 }
fn caller(x: i32) -> i32 { helper(x) + helper(x) }
// Verifier must analyze helper's body twice
```

With modular verification:
```rust,ignore
#[ensures("result == x + 1")]
fn helper(x: i32) -> i32 { x + 1 }

fn caller(x: i32) -> i32 {
    helper(x) + helper(x)
    // Verifier uses helper's contract, not its body
}
```

Benefits:
- **Scalability**: Verify each function once, regardless of call count
- **Information hiding**: Implementation details stay hidden
- **Faster verification**: Smaller formulas for the SMT solver
- **Parallel verification**: Functions can be verified independently

## How It Works

When verifying a caller:
1. At each call site, check the callee's precondition is satisfied
2. Assume the callee's postcondition holds for the return value
3. The callee's body is never examined

```rust,ignore
#[requires("x >= 0")]
#[ensures("result >= 0")]
fn sqrt(x: i32) -> i32 { /* ... */ }

#[ensures("result >= 0")]
fn distance(a: i32, b: i32) -> i32 {
    // 1. Check: a*a + b*b >= 0? Yes, squares are non-negative
    // 2. Assume: sqrt returns >= 0 (from postcondition)
    sqrt(a * a + b * b)
}
```

## Contract Verification

Each function's contract is verified separately:

```rust,ignore
#[requires("x >= 0")]
#[ensures("result * result <= x")]
fn isqrt(x: i32) -> i32 {
    // Verifier proves: given x >= 0, the result satisfies result * result <= x
    let mut r = 0;
    while r * r <= x { r += 1; }
    r - 1
}
```

## Builtin Contracts

tRust provides contracts for standard library functions:

```rust,ignore
fn example(a: i32, b: i32) -> i32 {
    // std::cmp::min has contract: result <= a && result <= b
    std::cmp::min(a, b)
}
```

Available builtin contracts:
- `min`, `max`, `clamp`
- `abs`, `signum`
- `saturating_add`, `saturating_sub`, `saturating_mul`
- `count_ones`, `count_zeros`, `leading_zeros`, `trailing_zeros`
- And many more (see [Builtin Contracts](../reference/builtins.md))

## Contract Strengthening and Weakening

### Stronger Preconditions at Call Sites

The caller can satisfy a stronger condition than required:

```rust,ignore
#[requires("x > 0")]  // Requires positive
fn log(x: i32) -> i32 { /* ... */ }

fn example() {
    let x = 42;  // x > 0 && x < 100 (stronger than just x > 0)
    log(x);      // OK: 42 > 0 satisfies precondition
}
```

### Weaker Postconditions in Callers

The caller can use less than what the callee guarantees:

```rust,ignore
#[ensures("result == x * 2")]  // Exact specification
fn double(x: i32) -> i32 { x * 2 }

#[ensures("result >= 0")]  // Weaker: just needs non-negative
fn example(x: i32) -> i32 {
    if x >= 0 {
        double(x)  // result == x * 2 >= 0
    } else {
        0
    }
}
```

## Verification Order

tRust verifies functions in dependency order:
1. Functions with no calls are verified first
2. Functions calling verified functions are verified next
3. Recursive/mutually recursive functions use their own contracts

## Mutual Recursion

For mutually recursive functions, each function's contract is assumed when verifying the other:

```rust,ignore
#[requires("n >= 0")]
#[ensures("result >= 0")]
fn is_even(n: i32) -> bool {
    if n == 0 { true }
    else { is_odd(n - 1) }  // Uses is_odd's contract
}

#[requires("n >= 0")]
#[ensures("result >= 0")]
fn is_odd(n: i32) -> bool {
    if n == 0 { false }
    else { is_even(n - 1) }  // Uses is_even's contract
}
```

## Trust Levels

Control how strictly functions are verified:

```rust,ignore
#![trust_level = "verified"]  // Full verification (default)
// or
#![trust_level = "assumed"]   // Skip verification, trust contracts
// or
#![trust_level = "audited"]   // Specs from external audit
```

Useful for:
- Legacy code: Mark as `assumed` until you add specs
- External libraries: Mark as `audited` for reviewed specs
- Performance: Skip verification of stable code

## Best Practices

1. **Write contracts for all public functions**: They form the API contract
2. **Keep preconditions minimal**: Don't require more than necessary
3. **Make postconditions precise**: Help callers prove their properties
4. **Use helper functions**: Break complex logic into verifiable pieces
5. **Trust standard library**: Use builtin contracts instead of re-proving

## Example: Modular Stack

```rust,ignore
struct Stack {
    data: Vec<i32>,
}

impl Stack {
    #[ensures("result.data.len() == 0")]
    fn new() -> Self {
        Stack { data: Vec::new() }
    }

    #[ensures("self.data.len() == old(self.data.len()) + 1")]
    fn push(&mut self, value: i32) {
        self.data.push(value);
    }

    #[requires("self.data.len() > 0")]
    #[ensures("self.data.len() == old(self.data.len()) - 1")]
    fn pop(&mut self) -> i32 {
        self.data.pop().unwrap()
    }

    #[ensures("result == self.data.len()")]
    fn len(&self) -> usize {
        self.data.len()
    }
}
```

Each method is verified independently using the contracts of other methods.

## Next Steps

- [Loop Invariants](./loops.md) - Verify loops with invariants
- [Cross-Crate Verification](./cross-crate.md) - Use contracts across crate boundaries
