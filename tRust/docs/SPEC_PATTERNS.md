# tRust Specification Patterns Cookbook

Common patterns for writing specifications in tRust.

## Basic Function Contracts

### Preconditions and Postconditions

```rust
// Simple bounds
#[requires(n > 0)]
#[ensures(result >= 1)]
fn positive_double(n: i32) -> i32 {
    n * 2
}

// Multiple conditions
#[requires(x > 0)]
#[requires(y > 0)]
#[ensures(result > x)]
#[ensures(result > y)]
fn sum_positive(x: i32, y: i32) -> i32 {
    x + y
}
```

### Result Relations

```rust
// Relate result to input
#[requires(x >= 0)]
#[ensures(result >= x)]
fn grow(x: i32) -> i32 {
    x + 1
}

// Monotonicity
#[requires(a <= b)]
#[ensures(result <= other_result)] // when called with larger arg
fn monotonic_transform(x: i32) -> i32 {
    x / 2
}
```

## Overflow Prevention

### Basic Arithmetic

```rust
// Addition - constrain to prevent overflow
#[requires(a < i32::MAX - b)]
#[ensures(result == a + b)]
fn safe_add(a: i32, b: i32) -> i32 {
    a + b
}

// Multiplication - wider bounds
#[requires(a <= 46340)]  // sqrt(i32::MAX)
#[requires(b <= 46340)]
fn safe_mul(a: i32, b: i32) -> i32 {
    a * b
}

// Use checked arithmetic when you can't constrain
fn flexible_add(a: i32, b: i32) -> Option<i32> {
    a.checked_add(b)
}
```

### Unsigned Subtraction

```rust
// Prevent underflow
#[requires(a >= b)]
#[ensures(result == a - b)]
fn safe_sub(a: u32, b: u32) -> u32 {
    a - b
}

// Or use saturating
fn saturating_diff(a: u32, b: u32) -> u32 {
    a.saturating_sub(b)
}
```

## Array/Slice Access

### Index Bounds

```rust
// Explicit bounds check in spec
#[requires(idx < arr.len())]
fn get_element(arr: &[i32], idx: usize) -> i32 {
    arr[idx]
}

// Non-empty slice
#[requires(!arr.is_empty())]
#[ensures(result == arr[0])]
fn first(arr: &[i32]) -> i32 {
    arr[0]
}

// Last element
#[requires(!arr.is_empty())]
fn last(arr: &[i32]) -> i32 {
    arr[arr.len() - 1]
}
```

### Range Iteration

```rust
// Process all elements
#[ensures(result == arr.iter().sum())]
fn sum_slice(arr: &[i32]) -> i32 {
    let mut total = 0;
    for &x in arr {
        total += x;
    }
    total
}
```

## Division Safety

### Non-Zero Divisor

```rust
#[requires(divisor != 0)]
fn safe_divide(dividend: i32, divisor: i32) -> i32 {
    dividend / divisor
}

// Average with count check
#[requires(count > 0)]
#[ensures(result == sum / count)]
fn average(sum: i32, count: i32) -> i32 {
    sum / count
}
```

## Option and Result Handling

### Option Unwrapping

```rust
// Know it's Some
#[requires(opt.is_some())]
fn unwrap_known(opt: Option<i32>) -> i32 {
    opt.unwrap()
}

// Provide default
#[ensures(result == opt.unwrap_or(default))]
fn get_or_default(opt: Option<i32>, default: i32) -> i32 {
    opt.unwrap_or(default)
}
```

### Result Handling

```rust
// Propagate errors properly
#[ensures(result.is_ok() == input.is_ok())]
fn transform_result(input: Result<i32, E>) -> Result<i32, E> {
    input.map(|x| x * 2)
}
```

## Comparison and Ordering

### Min/Max

```rust
#[ensures(result <= a)]
#[ensures(result <= b)]
#[ensures(result == a || result == b)]
fn min(a: i32, b: i32) -> i32 {
    if a < b { a } else { b }
}

#[ensures(result >= a)]
#[ensures(result >= b)]
fn max(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}
```

### Clamping

```rust
#[requires(min <= max)]
#[ensures(result >= min)]
#[ensures(result <= max)]
fn clamp(val: i32, min: i32, max: i32) -> i32 {
    if val < min { min }
    else if val > max { max }
    else { val }
}
```

## Loop Invariants

### Summation

```rust
fn sum_to_n(n: u32) -> u32 {
    let mut sum = 0u32;
    let mut i = 0u32;
    // Invariant: sum == i*(i-1)/2, i <= n
    while i < n {
        sum = sum.saturating_add(i);
        i += 1;
    }
    sum
}
```

### Search

```rust
fn find_first(arr: &[i32], target: i32) -> Option<usize> {
    let mut i = 0;
    // Invariant: forall j < i: arr[j] != target
    while i < arr.len() {
        if arr[i] == target {
            return Some(i);
        }
        i += 1;
    }
    None
}
```

## Struct Invariants

### Field Relationships

```rust
struct Range {
    start: i32,
    end: i32,
}

impl Range {
    // Constructor maintains invariant
    #[requires(start <= end)]
    fn new(start: i32, end: i32) -> Self {
        Range { start, end }
    }

    // Methods can assume invariant
    #[ensures(result >= 0)]
    fn len(&self) -> i32 {
        self.end - self.start
    }
}
```

### Non-Empty Collections

```rust
struct NonEmptyVec<T> {
    items: Vec<T>,
}

impl<T> NonEmptyVec<T> {
    #[requires(!items.is_empty())]
    fn new(items: Vec<T>) -> Self {
        NonEmptyVec { items }
    }

    // Always safe to get first
    fn first(&self) -> &T {
        &self.items[0]
    }
}
```

## Modular Verification (Function Composition)

### Using Callee Contracts

```rust
// Callee with postcondition
#[ensures(result >= 0)]
fn abs(x: i32) -> i32 {
    if x < 0 { x.wrapping_neg() } else { x }
}

// Caller can use postcondition
#[ensures(result >= 0)]  // Provable from abs's postcondition
fn abs_sum(a: i32, b: i32) -> i32 {
    abs(a).saturating_add(abs(b))
}
```

### Building on Libraries

```rust
// std::cmp::min guarantees result <= both args
fn bounded_increment(x: u32, max: u32) -> u32 {
    std::cmp::min(x.saturating_add(1), max)
}
```

## Pure Functions and Method Inlining

### The #[pure] Attribute

Mark functions with no side effects as `#[pure]`. Pure functions can be safely used in specifications.

```rust
// Mark simple accessors as pure
#[pure]
fn len<T>(v: &Vec<T>) -> usize {
    v.len()
}

// Pure functions can be called in specs
#[requires(len(&v) > 0)]
fn process(v: &Vec<i32>) -> i32 {
    v[0]
}
```

### The #[pure_returns] Attribute

When you need to call methods on `result` in postconditions, use `#[pure_returns("expr")]` to tell the verifier what the method returns. This enables **method inlining** in specifications.

**Problem**: The verifier can't evaluate method calls on return values.

```rust
// WITHOUT #[pure_returns] - DISPROVEN (solver can't resolve result.get())
pub struct Wrap(pub usize);
impl Wrap {
    pub fn get(&self) -> usize { self.0 }
}

#[ensures("result.get() == 42")]  // Fails: can't evaluate result.get()
pub fn make_wrap() -> Wrap { Wrap(42) }
```

**Solution**: Annotate accessor methods with `#[pure_returns]`:

```rust
// WITH #[pure_returns] - VERIFIED
pub struct Wrap(pub usize);
impl Wrap {
    #[pure]
    #[pure_returns("self.0")]  // Declares: get() returns self.0
    pub fn get(&self) -> usize { self.0 }
}

#[ensures("result.get() == 42")]  // Works: result.get() becomes result.0
pub fn make_wrap() -> Wrap { Wrap(42) }
```

When the verifier sees `result.get()` in a spec, it substitutes the `#[pure_returns]` expression with `self` replaced by `result`, yielding `result.0`.

### More Examples

```rust
// Index wrapper type
pub struct Idx(pub usize);

impl Idx {
    #[pure]
    #[pure_returns("self.0")]
    pub fn index(&self) -> usize { self.0 }

    #[pure]
    #[pure_returns("self.0")]
    pub fn as_usize(&self) -> usize { self.0 }
}

// All of these now verify
#[ensures("result.index() == 10")]
fn make_idx() -> Idx { Idx(10) }

#[ensures("result.index() == n")]
fn new_idx(n: usize) -> Idx { Idx(n) }

#[ensures("result.index() == result.as_usize()")]
fn consistent_idx() -> Idx { Idx(5) }
```

### When to Use

Use `#[pure_returns]` on:
- Simple accessor methods that return a field (`self.field`)
- Methods on newtype wrappers (`self.0`)
- Any `#[pure]` method you need to call in postconditions

### Current Limitations

1. **Manual annotation required**: You must add `#[pure_returns]` yourself; automatic inference is not implemented.

2. **Simple expressions only**: The return expression should be a simple field access (e.g., `self.0`, `self.field`).

3. **Closures not supported**: Specs with closures like `result.is_some_and(|x| x > 0)` cannot be verified.

## Common Anti-Patterns

### Avoid: Trivial Specs

```rust
// BAD - spec doesn't constrain anything useful
#[ensures(true)]
fn bad_spec(x: i32) -> i32 { x }

// GOOD - meaningful constraint
#[ensures(result == x)]
fn identity(x: i32) -> i32 { x }
```

### Avoid: Missing Edge Cases

```rust
// BAD - doesn't handle i32::MIN
#[ensures(result >= 0)]
fn bad_abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }  // -i32::MIN overflows!
}

// GOOD - explicit precondition for edge case
#[requires(x > i32::MIN)]
#[ensures(result >= 0)]
fn safe_abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

### Avoid: Overspecification

```rust
// BAD - over-constrained, brittle
#[requires(x == 5)]
#[requires(y == 10)]
fn overly_specific(x: i32, y: i32) -> i32 { x + y }

// GOOD - general constraint
#[requires(x < i32::MAX - y)]
fn general_add(x: i32, y: i32) -> i32 { x + y }
```

## Tips

1. **Start simple**: Add specs incrementally. Start with obvious preconditions.

2. **Let errors guide you**: Counterexamples show what you missed.

3. **Use `trustc --explain`**: Get detailed help on error codes.

4. **Checked arithmetic**: When specs would be too complex, use `checked_*` methods.

5. **Modular verification**: Well-specified helper functions make caller verification easier.

6. **Test your specs**: Verify they actually constrain what you intend.

Run `trustc --explain E0906` for overflow errors, `trustc --explain E0907` for division, etc.
