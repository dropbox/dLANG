# Integer Overflow Verification

Integer overflow is a common source of bugs. tRust can verify that arithmetic operations don't overflow.

## The Problem

In Rust (release mode), integer overflow wraps around silently:

```rust,ignore
let x: u8 = 255;
let y = x + 1;  // y = 0, not 256!
```

This can cause security vulnerabilities, data corruption, and subtle bugs.

## Automatic Overflow Detection

tRust automatically checks for overflow in arithmetic expressions:

```rust,ignore
#[ensures("result >= 0")]
fn bad_abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

```console
Verifying bad_abs...
  ensures(result >= 0): DISPROVEN
    Counterexample: x = -2147483648
```

The issue: `-(-2147483648)` overflows because `2147483648` doesn't fit in `i32`.

## Preventing Overflow with Preconditions

Add preconditions to exclude overflow-causing inputs:

```rust,ignore
#[requires("x > i32::MIN")]  // Exclude the problematic value
#[ensures("result >= 0")]
fn safe_abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

For addition:

```rust,ignore
#[requires("a >= 0 && b >= 0")]
#[requires("a <= i32::MAX - b")]  // Ensure no overflow
#[ensures("result == a + b")]
fn safe_add(a: i32, b: i32) -> i32 {
    a + b
}
```

## Using Checked Operations

Rust provides checked operations that return `Option`:

```rust,ignore
#[ensures("result.is_none() || result.unwrap() == a + b")]
fn checked_add(a: i32, b: i32) -> Option<i32> {
    a.checked_add(b)
}
```

## Using Saturating Operations

Saturating operations clamp at the bounds instead of overflowing:

```rust,ignore
#[ensures("result >= a")]  // Never less than input (for positive b)
#[ensures("result >= b")]
fn saturating_sum(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}
```

tRust has built-in contracts for saturating operations:
- `saturating_add`: `result >= a && result >= b` (unsigned)
- `saturating_sub`: `result <= a && result >= 0` (unsigned)
- `saturating_mul`: `result >= 0` (unsigned)

## Using Wrapping Operations

If you intentionally want wrapping behavior, use wrapping operations:

```rust,ignore
#[ensures("result == a.wrapping_add(b)")]
fn intentional_wrap(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}
```

tRust recognizes that wrapping operations are intentional and won't flag them as potential bugs.

## Overflow in Complex Expressions

Be careful with intermediate values:

```rust,ignore
// Bug: a * b might overflow even if result fits
#[requires("a >= 0 && b >= 0 && c > 0")]
fn average_bad(a: i32, b: i32, c: i32) -> i32 {
    (a + b) / c  // a + b might overflow!
}

// Fixed: use wider type for intermediate
fn average_good(a: i32, b: i32, c: i32) -> i32 {
    ((a as i64 + b as i64) / c as i64) as i32
}
```

## Common Overflow Patterns

### Subtraction with Unsigned Types

```rust,ignore
#[requires("a >= b")]  // Prevent underflow
#[ensures("result == a - b")]
fn safe_sub(a: u32, b: u32) -> u32 {
    a - b
}
```

### Multiplication

```rust,ignore
#[requires("b == 0 || a <= i32::MAX / b")]
#[requires("b == 0 || a >= i32::MIN / b")]
#[ensures("result == a * b")]
fn safe_mul(a: i32, b: i32) -> i32 {
    a * b
}
```

### Negation

```rust,ignore
#[requires("x != i32::MIN")]  // -MIN overflows
#[ensures("result == -x")]
fn safe_neg(x: i32) -> i32 {
    -x
}
```

### Division (MIN / -1 case)

```rust,ignore
#[requires("b != 0")]
#[requires("a != i32::MIN || b != -1")]  // MIN / -1 overflows
fn safe_div(a: i32, b: i32) -> i32 {
    a / b
}
```

## Bit Width Considerations

Different integer sizes have different overflow points:

| Type | MIN | MAX |
|------|-----|-----|
| `i8` | -128 | 127 |
| `i16` | -32768 | 32767 |
| `i32` | -2147483648 | 2147483647 |
| `i64` | -9223372036854775808 | 9223372036854775807 |
| `u8` | 0 | 255 |
| `u16` | 0 | 65535 |
| `u32` | 0 | 4294967295 |
| `u64` | 0 | 18446744073709551615 |

## Best Practices

1. **Prefer unsigned for counts**: `usize` and `u32` can't go negative
2. **Use checked/saturating when unsure**: Explicit handling is safer
3. **Document overflow assumptions**: Preconditions make assumptions clear
4. **Consider wider intermediate types**: `i64` for `i32` arithmetic

## Next Steps

- [Array Bounds Checking](./bounds.md) - Verify array access is safe
- [Working with Structs](./structs.md) - Specify properties of aggregate types
