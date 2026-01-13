# Your First Verified Program

Let's write and verify a simple function that clamps a value to a range.

## The Problem

We want a function that takes a value and ensures it's between 1 and some maximum `n`. If the value is too small, return 1. If too large, return `n`. Otherwise, return the value unchanged.

## Writing the Code

Create a file called `clamp.rs`:

```rust,ignore
#[requires("n > 0")]
#[ensures("result >= 1")]
#[ensures("result <= n")]
fn clamp_positive(n: i32, val: i32) -> i32 {
    if val < 1 {
        1
    } else if val > n {
        n
    } else {
        val
    }
}

fn main() {
    let x = clamp_positive(10, 15);
    println!("Clamped: {}", x);  // Prints: 10
}
```

## Understanding the Specifications

The function has three specification attributes:

### `#[requires("n > 0")]`

This is a **precondition**. It states what callers must guarantee before calling this function. Here, we require `n > 0` because our return value must be between 1 and `n`, which only makes sense if `n >= 1`.

### `#[ensures("result >= 1")]`

This is a **postcondition**. It states what the function guarantees to callers. The special variable `result` refers to the return value. This says the result will always be at least 1.

### `#[ensures("result <= n")]`

Another postcondition saying the result will never exceed `n`.

## Running Verification

Verify the function with tRust:

```bash
./bin/trustc clamp.rs
```

Output:

```console
Verifying clamp_positive...
  requires(n > 0): assumed
  ensures(result >= 1): PROVEN
  ensures(result <= n): PROVEN

Verification: 1/1 functions verified
```

What this means:
- **assumed**: Preconditions are assumed to hold (callers must satisfy them)
- **PROVEN**: The compiler mathematically proved this property holds for all valid inputs

## What Was Actually Proven?

The compiler proved that **for all** values of `n` and `val` where `n > 0`:
- The returned value is `>= 1`
- The returned value is `<= n`

This isn't testing with a few examples - it's a mathematical proof covering every possible input.

## A Common Bug

Let's see what happens with a buggy implementation. Create `clamp_bug.rs`:

```rust,ignore
#[requires("n > 0")]
#[ensures("result >= 1")]
#[ensures("result <= n")]
fn clamp_positive(n: i32, val: i32) -> i32 {
    // Bug: forgot to handle val < 1 case
    if val > n {
        n
    } else {
        val  // Could be negative!
    }
}
```

Run verification:

```bash
./bin/trustc clamp_bug.rs
```

Output:

```console
Verifying clamp_positive...
  requires(n > 0): assumed
  ensures(result >= 1): DISPROVEN
    Counterexample: n = 1, val = 0
  ensures(result <= n): PROVEN

Verification: 0/1 functions verified
```

The compiler found a **counterexample**: when `n = 1` and `val = 0`, the function returns `0`, which violates `result >= 1`.

## Overflow Verification

tRust also verifies integer overflow by default. Create `overflow.rs`:

```rust,ignore
#[ensures("result >= 0")]
fn bad_abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

This looks correct, but:

```bash
./bin/trustc overflow.rs
```

```console
Verifying bad_abs...
  ensures(result >= 0): DISPROVEN
    Counterexample: x = -2147483648

Verification: 0/1 functions verified
```

The problem: `-(-2147483648)` overflows in signed 32-bit arithmetic, wrapping to `-2147483648` (negative).

Fix it with a precondition:

```rust,ignore
#[requires("x > i32::MIN")]
#[ensures("result >= 0")]
fn safe_abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

Or use `wrapping_abs` if you want to handle all inputs:

```rust,ignore
#[ensures("result == x || result == -x")]
fn wrapping_abs(x: i32) -> i32 {
    x.wrapping_abs()
}
```

## Compiling to an Executable

tRust is a full Rust compiler. After verification succeeds, it produces a working executable:

```bash
./bin/trustc clamp.rs -o clamp
./clamp
# Output: Clamped: 10
```

## Next Steps

Now that you've verified your first function, learn about:
- [Understanding Verification Output](./output.md) for detailed output interpretation
- [Preconditions and Postconditions](../basic/pre-post.md) for more specification patterns
