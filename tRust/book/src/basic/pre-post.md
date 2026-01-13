# Preconditions and Postconditions

Preconditions and postconditions are the foundation of specification in tRust. They define the contract between a function and its callers.

## Preconditions with `#[requires]`

A precondition states what must be true **before** a function is called. The caller is responsible for ensuring preconditions hold.

```rust,ignore
#[requires("divisor != 0")]
fn divide(dividend: i32, divisor: i32) -> i32 {
    dividend / divisor
}
```

### What Preconditions Mean

- The function **assumes** the precondition holds
- Callers **must** satisfy the precondition
- If a caller might violate the precondition, tRust reports an error

### Multiple Preconditions

You can have multiple `#[requires]` attributes:

```rust,ignore
#[requires("n > 0")]
#[requires("n <= 100")]
fn process_bounded(n: i32) -> i32 {
    // ...
}
```

This is equivalent to `#[requires("n > 0 && n <= 100")]`.

### Precondition Expressions

Preconditions can use:
- Arithmetic operators: `+`, `-`, `*`, `/`, `%`
- Comparisons: `==`, `!=`, `<`, `<=`, `>`, `>=`
- Logical operators: `&&`, `||`, `!`
- Parameter names
- Constants and literals

```rust,ignore
#[requires("a >= 0 && b >= 0")]
#[requires("a + b < i32::MAX")]  // Prevent overflow
fn safe_add(a: i32, b: i32) -> i32 {
    a + b
}
```

## Postconditions with `#[ensures]`

A postcondition states what must be true **after** a function returns. The function is responsible for ensuring postconditions hold.

```rust,ignore
#[ensures("result >= 0")]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

### The `result` Variable

In postconditions, the special variable `result` refers to the function's return value:

```rust,ignore
#[ensures("result == a + b")]
fn add(a: i32, b: i32) -> i32 {
    a + b
}
```

### Relating Input to Output

Postconditions often relate the output to the input:

```rust,ignore
#[requires("x >= 0")]
#[ensures("result * result <= x")]
#[ensures("(result + 1) * (result + 1) > x")]
fn integer_sqrt(x: i32) -> i32 {
    // Returns floor(sqrt(x))
    let mut r = 0;
    while (r + 1) * (r + 1) <= x {
        r += 1;
    }
    r
}
```

This specifies that `result` is the largest integer whose square doesn't exceed `x`.

### Old Values

Sometimes you need to refer to the original value of a parameter that might be modified. Use `old(expr)`:

```rust,ignore
#[ensures("result == old(x) + 1")]
fn increment(x: i32) -> i32 {
    x + 1
}
```

Note: `old()` is most useful in methods that modify `&mut self`.

## Combining Preconditions and Postconditions

A complete contract often has both:

```rust,ignore
/// Computes a / b, rounding toward zero.
#[requires("b != 0")]
#[requires("a != i32::MIN || b != -1")]  // Prevent overflow
#[ensures("result * b <= a")]
#[ensures("result * b + b > a || result * b - b < a")]
fn checked_div(a: i32, b: i32) -> i32 {
    a / b
}
```

## Contract Composition

When function A calls function B:
1. A must satisfy B's preconditions (checked by tRust)
2. A can assume B's postconditions hold (used by tRust)

```rust,ignore
#[requires("x >= 0")]
#[ensures("result >= 0")]
fn sqrt(x: i32) -> i32 { /* ... */ }

#[ensures("result >= 0")]
fn distance(a: i32, b: i32) -> i32 {
    // a*a >= 0 and b*b >= 0, so sum >= 0
    // sqrt's postcondition gives result >= 0
    sqrt(a * a + b * b)
}
```

tRust verifies that `a * a + b * b >= 0` (satisfying `sqrt`'s precondition) and then uses `sqrt`'s postcondition to prove `distance`'s postcondition.

## Common Patterns

### Non-Negative Result

```rust,ignore
#[ensures("result >= 0")]
fn positive_fn(...) -> i32 { ... }
```

### Bounded Result

```rust,ignore
#[requires("min <= max")]
#[ensures("result >= min")]
#[ensures("result <= max")]
fn clamp(val: i32, min: i32, max: i32) -> i32 { ... }
```

### Option Guarantees

```rust,ignore
#[requires("slice.len() > 0")]
#[ensures("result.is_some()")]
fn first_element(slice: &[i32]) -> Option<i32> {
    slice.first().copied()
}
```

### Result Guarantees

```rust,ignore
#[requires("divisor != 0")]
#[ensures("result.is_ok()")]
fn safe_divide(a: i32, b: i32) -> Result<i32, &'static str> {
    Ok(a / b)
}
```

## Best Practices

1. **Be precise but not over-specified**: Specify what matters, not implementation details
2. **Use preconditions liberally**: They document assumptions and catch bugs at call sites
3. **Start with simple postconditions**: Add complexity only when needed
4. **Test your specs**: Write functions that should fail verification to ensure specs catch bugs

## Next Steps

- [Integer Overflow Verification](./overflow.md) - Handle arithmetic safely
- [Array Bounds Checking](./bounds.md) - Verify array access is safe
