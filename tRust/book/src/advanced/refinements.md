# Refinement Types

Refinement types extend ordinary types with logical predicates. Instead of just `i32`, you can have "positive i32" or "i32 between 0 and 100".

## Basic Refinement Syntax

Define a refinement type using a type alias with a predicate:

```rust,ignore
// type Positive = i32 where self > 0
#[param_type(n: "self > 0")]
fn requires_positive(n: i32) -> i32 {
    n  // We know n > 0 inside this function
}
```

The `#[param_type]` attribute specifies refinement constraints on parameters.

## Parameter Type Annotations

Use `#[param_type]` to refine function parameters:

```rust,ignore
#[param_type(divisor: "self != 0")]
fn divide(dividend: i32, divisor: i32) -> i32 {
    dividend / divisor  // Safe: divisor != 0
}
```

Multiple parameter refinements:

```rust,ignore
#[param_type(a: "self >= 0")]
#[param_type(b: "self >= 0")]
#[param_type(a: "self + b <= i32::MAX")]
fn safe_add(a: i32, b: i32) -> i32 {
    a + b
}
```

## Return Type Annotations

Use `#[return_type]` to refine the return type:

```rust,ignore
#[return_type("self >= 0")]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

This is equivalent to `#[ensures("result >= 0")]` but expressed as a type property.

## Automatic Spec Expansion

Refinement types automatically expand to preconditions and postconditions:

```rust,ignore
#[param_type(x: "self > 0")]
#[return_type("self > 0")]
fn double_positive(x: i32) -> i32 {
    x * 2
}

// Equivalent to:
#[requires("x > 0")]
#[ensures("result > 0")]
fn double_positive(x: i32) -> i32 {
    x * 2
}
```

## Generic Refinements

Refinement types work with generics:

```rust,ignore
// NonEmpty<T> = Vec<T> where self.len() > 0
#[param_type(vec: "self.len() > 0")]
fn first<T: Copy>(vec: &Vec<T>) -> T {
    vec[0]  // Safe: len > 0
}
```

## Common Refinement Patterns

### Non-Zero

```rust,ignore
#[param_type(n: "self != 0")]
fn reciprocal(n: f64) -> f64 {
    1.0 / n
}
```

### Bounded Values

```rust,ignore
#[param_type(percent: "self >= 0 && self <= 100")]
fn apply_percentage(value: i32, percent: i32) -> i32 {
    value * percent / 100
}
```

### Valid Index

```rust,ignore
#[param_type(index: "self < arr.len()")]
fn get_element(arr: &[i32], index: usize) -> i32 {
    arr[index]
}
```

### Sorted Array

```rust,ignore
// Conceptually: SortedArray<T> = Vec<T> where is_sorted(self)
#[param_type(arr: "is_sorted(self)")]  // Requires is_sorted predicate
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    // Can assume arr is sorted
}
```

## Subtyping

Refinement types create subtyping relationships:

- `Positive <: i32` (Positive is a subtype of i32)
- `NonZero <: i32`
- `BoundedPercent <: i32`

A value of refined type can be used where the base type is expected:

```rust,ignore
#[return_type("self > 0")]
fn get_positive() -> i32 { 42 }

fn takes_int(x: i32) { /* ... */ }

fn example() {
    let p = get_positive();  // p has refinement "self > 0"
    takes_int(p);            // OK: Positive <: i32
}
```

## Refinements and Option/Result

```rust,ignore
#[return_type("self.is_some()")]
fn find_guaranteed(arr: &[i32], target: i32) -> Option<usize> {
    // Implementation must guarantee Some is returned
}

#[return_type("self.is_ok()")]
fn infallible_parse(s: &str) -> Result<i32, ()> {
    // Implementation must guarantee Ok is returned
}
```

## Combining with Specifications

Refinement types complement explicit specifications:

```rust,ignore
#[param_type(n: "self > 0")]
#[ensures("result > 0")]
#[ensures("result <= n")]
fn clamp_to_n(value: i32, n: i32) -> i32 {
    if value < 1 { 1 }
    else if value > n { n }
    else { value }
}
```

## Current Limitations

tRust's refinement types have some limitations:

1. **No inference**: Must explicitly annotate refinements
2. **Limited method calls**: `self.len()` works, complex methods may not
3. **No dependent types**: Can't express `fn(n: i32) -> [i32; n]`
4. **No union refinements**: Can't say "positive OR zero"

## Future Directions

Future versions may support:
- Liquid type inference (automatic refinement discovery)
- Dependent function types
- Refinement propagation through assignments
- User-defined refinement predicates

## Best Practices

1. **Use refinements for domain types**: `PositiveAmount`, `ValidIndex`
2. **Document with types**: Refinements serve as documentation
3. **Prefer refinements over runtime checks**: Compile-time guarantees
4. **Combine with testing**: Verify edge cases at refinement boundaries

## Next Steps

- [Effects System](./effects.md) - Track computational effects
- [Cross-Crate Verification](./cross-crate.md) - Share refinements across crates
