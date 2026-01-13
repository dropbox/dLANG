# Builtin Contracts

tRust provides builtin contracts for standard library functions. These contracts are automatically used during verification.

## Comparison Functions

### `std::cmp::min(a, b)`

```rust,ignore
#[ensures("result <= a")]
#[ensures("result <= b")]
#[ensures("result == a || result == b")]
```

### `std::cmp::max(a, b)`

```rust,ignore
#[ensures("result >= a")]
#[ensures("result >= b")]
#[ensures("result == a || result == b")]
```

### `Ord::clamp(val, min, max)`

```rust,ignore
#[requires("min <= max")]
#[ensures("result >= min")]
#[ensures("result <= max")]
```

## Absolute Value

### `i32::abs(x)` (all signed integers)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result == x || result == -x")]
```

Note: Overflows for `i32::MIN`. Use with `#[requires("x > i32::MIN")]` or use `wrapping_abs`.

### `i32::wrapping_abs(x)`

```rust,ignore
#[ensures("result == x || result == -x")]
```

Safe for all inputs including `MIN`.

### `i32::unsigned_abs(x)`

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result == x || result == -x")]
```

Returns unsigned type, safe for all inputs.

## Sign Functions

### `i32::signum(x)` (all signed integers)

```rust,ignore
#[ensures("x > 0 => result == 1")]
#[ensures("x < 0 => result == -1")]
#[ensures("x == 0 => result == 0")]
```

### `i32::is_positive(x)`

```rust,ignore
#[ensures("result == (x > 0)")]
```

### `i32::is_negative(x)`

```rust,ignore
#[ensures("result == (x < 0)")]
```

## Saturating Arithmetic

### `u32::saturating_add(a, b)` (all unsigned)

```rust,ignore
#[ensures("result >= a")]
#[ensures("result >= b")]
```

### `u32::saturating_sub(a, b)` (all unsigned)

```rust,ignore
#[ensures("result <= a")]
#[ensures("result >= 0")]
```

### `u32::saturating_mul(a, b)` (all unsigned)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("a > 0 && b > 0 => result >= a && result >= b")]
```

## Division Functions

### `i32::div_euclid(x, rhs)` (all signed)

```rust,ignore
#[requires("rhs != 0")]
#[ensures("x >= 0 && rhs > 0 => result >= 0 && result <= x")]
```

Euclidean division (rounds toward negative infinity).

### `u32::div_euclid(x, rhs)` (all unsigned)

```rust,ignore
#[requires("rhs != 0")]
#[ensures("result >= 0")]
#[ensures("result <= x")]
```

### `i32::rem_euclid(x, rhs)` (all signed)

```rust,ignore
#[requires("rhs != 0")]
#[ensures("result >= 0")]
```

Always non-negative remainder.

### `u32::rem_euclid(x, rhs)` (all unsigned)

```rust,ignore
#[requires("rhs != 0")]
#[ensures("result >= 0")]
#[ensures("result < rhs")]
```

### `u32::div_ceil(x, rhs)` (all integers)

```rust,ignore
#[requires("rhs != 0")]
#[ensures("result >= 0")]  // for unsigned
#[ensures("x == 0 => result == 0")]
```

Ceiling division (rounds toward positive infinity).

### `u32::next_multiple_of(x, rhs)` (all integers)

```rust,ignore
#[requires("rhs != 0")]
#[ensures("result >= 0")]  // for unsigned
#[ensures("result >= x")]
#[ensures("result < x + rhs")]
#[ensures("x == 0 => result == 0")]
```

Returns smallest multiple of `rhs` that is >= `x`.

### `u32::isqrt(x)` (all unsigned)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result <= x")]
#[ensures("x == 0 => result == 0")]
#[ensures("x == 1 => result == 1")]
```

Integer square root (floor of sqrt).

### `i32::isqrt(x)` (all signed except isize)

```rust,ignore
#[requires("x >= 0")]
#[ensures("result >= 0")]
#[ensures("result <= x")]
#[ensures("x == 0 => result == 0")]
#[ensures("x == 1 => result == 1")]
```

Integer square root for signed types. Panics if `x < 0`.

## Bit Operations

### `u32::count_ones(x)` (all integers)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result <= 32")]  // bit_width
#[ensures("x == 0 => result == 0")]
```

### `u32::count_zeros(x)` (all integers)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result <= 32")]  // bit_width
```

### `u32::leading_zeros(x)` (all integers)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result <= 32")]  // bit_width
#[ensures("x == 0 => result == 32")]  // bit_width
```

### `u32::trailing_zeros(x)` (all integers)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result <= 32")]  // bit_width
#[ensures("x == 0 => result == 32")]  // bit_width
```

### `u32::leading_ones(x)` (all integers)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result <= 32")]  // bit_width
```

### `u32::trailing_ones(x)` (all integers)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result <= 32")]  // bit_width
```

### `u32::is_power_of_two(x)` (all unsigned)

```rust,ignore
#[ensures("result => x > 0")]
#[ensures("x == 0 => !result")]
#[ensures("x == 1 => result")]
```

### `u32::next_power_of_two(x)` (all unsigned)

```rust,ignore
#[ensures("result > 0")]
#[ensures("result >= x || x == 0")]
```

## Bit Manipulation

### `u32::rotate_left(x, n)` (all integers)

```rust,ignore
#[ensures("(x == 0) == (result == 0)")]
```

Zero-ness is preserved.

### `u32::rotate_right(x, n)` (all integers)

```rust,ignore
#[ensures("(x == 0) == (result == 0)")]
```

### `u32::swap_bytes(x)` (all integers)

```rust,ignore
#[ensures("(x == 0) == (result == 0)")]
```

### `u32::reverse_bits(x)` (all integers)

```rust,ignore
#[ensures("(x == 0) == (result == 0)")]
```

### Endianness Functions

`from_be`, `from_le`, `to_be`, `to_le`:

```rust,ignore
#[ensures("(x == 0) == (result == 0)")]
```

## Logarithms

### `u32::ilog2(x)` (all integers)

```rust,ignore
#[requires("x > 0")]
#[ensures("result >= 0")]
#[ensures("result < 32")]  // bit_width
#[ensures("x == 1 => result == 0")]
```

### `u32::ilog10(x)` (all integers)

```rust,ignore
#[requires("x > 0")]
#[ensures("result >= 0")]
#[ensures("result <= 9")]  // max_log10 for u32
#[ensures("x == 1 => result == 0")]
```

### `u32::ilog(x, base)` (all integers)

```rust,ignore
#[requires("x > 0")]
#[requires("base > 1")]
#[ensures("result >= 0")]
#[ensures("x == 1 => result == 0")]
```

## Absolute Difference

### `u32::abs_diff(a, b)` (all integers)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("a == b => result == 0")]
#[ensures("result <= a || result <= b")]  // for unsigned
```

Returns `|a - b|`. For signed types, returns unsigned result.

## Exponentiation

### `u32::pow(base, exp)` (all integers)

```rust,ignore
#[ensures("exp == 0 => result == 1")]
#[ensures("base == 0 && exp > 0 => result == 0")]
#[ensures("base == 1 => result == 1")]
#[ensures("exp == 1 => result == base")]
```

Note: May overflow for large values. Use `checked_pow` for safety.

## Wrapping Operations

Wrapping operations perform the operation with wrap-around on overflow. These contracts express properties that hold regardless of wrapping.

### `u32::wrapping_neg(x)` (all integers)

```rust,ignore
#[ensures("(x == 0) == (result == 0)")]
```

### `u32::wrapping_add(a, b)` (all integers)

```rust,ignore
#[ensures("a == 0 && b == 0 => result == 0")]
```

### `u32::wrapping_sub(a, b)` (all integers)

```rust,ignore
#[ensures("a == b => result == 0")]
```

### `u32::wrapping_mul(a, b)` (all integers)

```rust,ignore
#[ensures("a == 0 || b == 0 => result == 0")]
```

### `u32::wrapping_pow(base, exp)` (all integers)

```rust,ignore
#[ensures("exp == 0 => result == 1")]
#[ensures("base == 0 && exp > 0 => result == 0")]
#[ensures("base == 1 => result == 1")]
```

### `u32::wrapping_div(x, y)` (all unsigned)

```rust,ignore
#[requires("y != 0")]
#[ensures("result >= 0")]
#[ensures("result <= x")]
#[ensures("x == 0 => result == 0")]
```

### `u32::wrapping_rem(x, y)` (all unsigned)

```rust,ignore
#[requires("y != 0")]
#[ensures("result >= 0")]
#[ensures("result < y")]
#[ensures("x == 0 => result == 0")]
```

## Midpoint Operation

The `midpoint` method returns the average of two numbers without overflow.

### `u32::midpoint(a, b)` (all unsigned)

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result <= a || result <= b")]
#[ensures("a == b => result == a")]
```

Returns `(a + b) / 2` rounded down. Never overflows.

### `i32::midpoint(a, b)` (all signed)

```rust,ignore
#[ensures("a == b => result == a")]
#[ensures("(a <= result <= b) || (b <= result <= a)")]
```

Returns `(a + b) / 2` rounded towards negative infinity. Never overflows.

## Checked Arithmetic (`Option<T>` Return)

These methods return `Option<T>` instead of panicking on overflow. The Option is modeled as:
- `result.is_some()` → boolean indicating Some
- `result.is_none()` → boolean indicating None
- `result.unwrap()` → the underlying value (only valid when is_some)
- `result.unwrap_or(default)` → conditional: `if is_some then value else default`

**Constructor Tracking**: When `Some(x)` or `None` is constructed, the model variables are automatically set:
- `Some(x)` sets `is_some=true` and `value=x`
- `None` sets `is_some=false`

This enables verification of postconditions like `result.is_some()` and `result.unwrap() == expected`.

### `u32::checked_add(a, b)` (all integers)

```rust,ignore
#[ensures("result.is_some() => result.unwrap() == a + b")]
```

### `u32::checked_sub(a, b)` (all integers)

```rust,ignore
#[ensures("result.is_some() => result.unwrap() == a - b")]
```

### `u32::checked_mul(a, b)` (all integers)

```rust,ignore
#[ensures("result.is_some() => result.unwrap() == a * b")]
```

### `u32::checked_div(a, b)` (all integers)

```rust,ignore
#[ensures("result.is_some() => result.unwrap() == a / b")]
```

### `u32::checked_rem(a, b)` (all integers)

```rust,ignore
#[ensures("result.is_some() => result.unwrap() == a % b")]
```

### `i32::checked_neg(a)` (all signed)

```rust,ignore
#[ensures("result.is_some() => result.unwrap() == -a")]
```

### `i32::checked_abs(a)` (all signed)

```rust,ignore
#[ensures("result.is_some() => result.unwrap() >= 0")]
#[ensures("result.is_some() => result.unwrap() == a || result.unwrap() == -a")]
```

### `u32::checked_pow(base, exp)` (all integers)

```rust,ignore
#[ensures("result.is_some() && exp == 0 => result.unwrap() == 1")]
#[ensures("result.is_some() && base == 1 => result.unwrap() == 1")]
```

**Note**: The current implementation models Option variables and their values. Full tracking of when `is_some` should be true (based on overflow conditions) requires additional work.

## `Result<T,E>` Method Parsing

Result types are modeled similarly to Option:
- `result.is_ok()` → boolean indicating Ok
- `result.is_err()` → boolean indicating Err (equivalent to `!is_ok`)
- `result.unwrap()` → the Ok value (only valid when is_ok)
- `result.unwrap_err()` → the Err value (only valid when is_err)

These methods can be used in specifications to reason about Result-returning functions:

```rust,ignore
#[ensures("result.is_ok()")]
fn always_succeeds() -> Result<i32, String> { Ok(42) }

#[requires("x >= 0")]
#[ensures("result.is_ok()")]
fn validate(x: i32) -> Result<i32, &'static str> {
    if x >= 0 { Ok(x) } else { Err("negative") }
}
```

**Constructor Tracking**: When `Ok(x)` or `Err(e)` is constructed, the model variables are automatically set:
- `Ok(x)` sets `is_ok=true` and `value=x`
- `Err(e)` sets `is_ok=false` and `err_value=e`

This enables verification of postconditions like `result.is_ok()` and `result.unwrap() == expected`.

## Conversion Methods

tRust supports conversion methods between `Option` and `Result` types:

### `Result::ok()` - Convert Result to Option

Converts `Result<T, E>` to `Option<T>`:
- `Ok(v)` → `Some(v)`
- `Err(e)` → `None`

```rust,ignore
#[ensures("result.is_some()")]
fn ok_to_option(x: i32) -> Option<i32> {
    let r: Result<i32, ()> = Ok(x);
    r.ok()
}
```

### `Result::err()` - Convert Result to Option (error variant)

Converts `Result<T, E>` to `Option<E>`:
- `Err(e)` → `Some(e)`
- `Ok(v)` → `None`

```rust,ignore
#[ensures("result.is_some()")]
fn err_to_option(e: i32) -> Option<i32> {
    let r: Result<(), i32> = Err(e);
    r.err()
}
```

### `Option::ok_or()` - Convert Option to Result

Converts `Option<T>` to `Result<T, E>`:
- `Some(v)` → `Ok(v)`
- `None` → `Err(err)` (using provided error value)

```rust,ignore
#[ensures("result.is_ok()")]
fn some_to_result(x: i32) -> Result<i32, i32> {
    let opt: Option<i32> = Some(x);
    opt.ok_or(0)
}

#[ensures("result.is_err()")]
#[ensures("result.unwrap_err() == 404")]
fn none_to_result() -> Result<i32, i32> {
    let opt: Option<i32> = None;
    opt.ok_or(404)
}
```

These conversion methods preserve value tracking across type conversions, enabling verification of chained operations like `Ok(x).ok().ok_or(e)`.

## Combinator Methods

tRust supports verification of combinator methods for `Option` and `Result`. Since closures cannot be statically analyzed, tRust verifies **structural properties** that hold regardless of closure behavior.

### Option Combinators

| Method | Postcondition |
|--------|---------------|
| `map(f)` | `result.is_some() == self.is_some()` |
| `and_then(f)` | `self.is_none() ==> result.is_none()` |
| `or_else(f)` | `self.is_some() ==> result == self` |
| `or(other)` | `result.is_some() == (self.is_some() \|\| other.is_some())` |
| `filter(p)` | `self.is_none() ==> result.is_none()` |
| `flatten()` | `self.is_none() ==> result.is_none()` |

### Result Combinators

| Method | Postcondition |
|--------|---------------|
| `map(f)` | `result.is_ok() == self.is_ok()`, error preserved if Err |
| `map_err(f)` | `result.is_ok() == self.is_ok()`, value preserved if Ok |
| `and_then(f)` | `self.is_err() ==> result == self` (error propagates) |
| `or_else(f)` | `self.is_ok() ==> result == self` (ok preserved) |
| `or(other)` | `result.is_ok() == (self.is_ok() \|\| other.is_ok())` |
| `flatten()` | `self.is_err() ==> result == self` (error propagates) |

### Example

```rust,ignore
// Option::map preserves is_some status
#[ensures("result.is_some()")]
fn option_map_preserves() -> Option<i32> {
    let opt: Option<i32> = Some(42);
    opt.map(|x| x * 2)  // Value transformed, but still Some
}

// Option::and_then propagates None
#[ensures("result.is_none()")]
fn none_propagates() -> Option<i32> {
    let opt: Option<i32> = None;
    opt.and_then(|x| Some(x + 1))  // None stays None
}

// Result::and_then preserves error with value
#[ensures("result.is_err()")]
#[ensures("result.unwrap_err() == 500")]
fn error_propagates() -> Result<i32, i32> {
    let res: Result<i32, i32> = Err(500);
    res.and_then(|x| Ok(x * 2))  // Error value preserved
}

// Option::or_else preserves Some with value
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == 42")]
fn some_preserved() -> Option<i32> {
    let opt: Option<i32> = Some(42);
    opt.or_else(|| Some(100))  // Original Some value preserved
}
```

These structural postconditions enable verification of code that chains Option/Result combinators, even when closure behavior cannot be analyzed.

## Additional Option/Result Methods

tRust also supports these commonly-used methods:

### Option Methods

| Method | Postcondition |
|--------|---------------|
| `unwrap_or_else(f)` | `self.is_some() ==> result == self.value` |
| `unwrap_or_default()` | `self.is_some() ==> result == self.value` |
| `xor(other)` | `result.is_some() == (self.is_some() XOR other.is_some())` |
| `expect(msg)` | `result == self.value` (same as unwrap) |
| `zip(other)` | `result.is_some() == (self.is_some() && other.is_some())` |
| `and(other)` | `result.is_some() == (self.is_some() && other.is_some())`, returns other |
| `copied()` | Preserves `is_some`, copies value (`Option<&T>` -> `Option<T>`) |
| `cloned()` | Preserves `is_some`, clones value (`Option<&T>` -> `Option<T>`) |
| `as_ref()` | Preserves `is_some` (`Option<T>` -> `Option<&T>`) |
| `as_mut()` | Preserves `is_some` (`Option<T>` -> `Option<&mut T>`) |
| `transpose()` | `Option<Result<T,E>>` -> `Result<Option<T>,E>` |
| `inspect(f)` | Returns self unchanged (identity, f called for side effects) |
| `map_or(default, f)` | `self.is_none() ==> result == default` |
| `map_or_else(default_fn, f)` | No postcondition (both branches use closures) |

### Result Methods

| Method | Postcondition |
|--------|---------------|
| `unwrap_or_else(f)` | `self.is_ok() ==> result == self.value` |
| `unwrap_or_default()` | `self.is_ok() ==> result == self.value` |
| `expect(msg)` | `result == self.value` (same as unwrap) |
| `expect_err(msg)` | `result == self.err_value` (same as unwrap_err) |
| `and(other)` | `result.is_ok() == (self.is_ok() && other.is_ok())`, returns other |
| `as_ref()` | Preserves `is_ok` (`Result<T,E>` -> `Result<&T,&E>`) |
| `as_mut()` | Preserves `is_ok` (`Result<T,E>` -> `Result<&mut T,&mut E>`) |
| `copied()` | Preserves `is_ok`, copies values (`Result<&T,E>` -> `Result<T,E>`) |
| `cloned()` | Preserves `is_ok`, clones values (`Result<&T,E>` -> `Result<T,E>`) |
| `transpose()` | `Result<Option<T>,E>` -> `Option<Result<T,E>>` |
| `inspect(f)` | Returns self unchanged (identity) |
| `inspect_err(f)` | Returns self unchanged (identity) |
| `map_or(default, f)` | `self.is_err() ==> result == default` |
| `map_or_else(default_fn, f)` | No postcondition (both branches use closures) |

### Example: xor and zip

```rust,ignore
// xor returns Some only if exactly one is Some
#[ensures("result.is_some()")]
#[ensures("result.unwrap() == 42")]
fn xor_example() -> Option<i32> {
    let a: Option<i32> = Some(42);
    let b: Option<i32> = None;
    a.xor(b)  // Returns Some(42)
}

// zip combines two Options into Option<(T, U)>
#[ensures("result.is_some()")]
fn zip_example() -> Option<(i32, i32)> {
    let a: Option<i32> = Some(1);
    let b: Option<i32> = Some(2);
    a.zip(b)  // Returns Some((1, 2))
}
```

## `Vec<T>` Methods

tRust supports a length-based model for `Vec<T>`. The `len` function is treated as an uninterpreted function, allowing verification of length-related properties.

### Construction

#### `Vec::new()`, `Vec::with_capacity(n)`

```rust,ignore
#[ensures("result.len() == 0")]
```

### Length Queries

#### `Vec::len()`, `Vec::is_empty()`

```rust,ignore
#[ensures("result == v.len()")]
#[ensures("result == v.is_empty()")]
```

#### `Vec::capacity()`

```rust,ignore
#[ensures("result >= v.len()")]
```

### `Vec::pop()`

```rust,ignore
#[ensures("result.is_some() == (v.len() > 0)")]  // before pop
```

### Example

```rust,ignore
// Vec::new().pop() returns None (empty vector)
#[ensures("result.is_none()")]
fn pop_empty() -> Option<i32> {
    let mut v: Vec<i32> = Vec::new();
    v.pop()
}

// Vec::pop returns Some when len > 0
#[requires("v.len() > 0")]
#[ensures("result.is_some()")]
fn pop_nonempty(v: &mut Vec<i32>) -> Option<i32> {
    v.pop()
}
```

**Note**:
- Slice methods (`get`, `first`, `last`, `contains`) are NOT YET MODELED because they deref through slices, which can also apply to fixed-size arrays.
- Mutating operations (`push`, `clear`) do not yet model length changes.
- Element contents are not tracked.

## String Methods

tRust supports a length-based model for `String`, similar to `Vec<T>`. The `len` function is treated as an uninterpreted function.

### Construction

#### `String::new()`, `String::with_capacity(n)`

```rust,ignore
#[ensures("result.len() == 0")]
```

### Length Queries

#### `String::len()`, `String::is_empty()`

```rust,ignore
#[ensures("result == s.len()")]
#[ensures("result == s.is_empty()")]
```

#### `String::capacity()`

```rust,ignore
#[ensures("result >= s.len()")]
```

### Mutation Tracking

tRust tracks String length changes through mutation methods:

#### `String::push(ch)`
```rust,ignore
// After push, length increases by 1 (UTF-8 char modeled as +1)
// len(s) = len(s) + 1
```

#### `String::push_str(str)`
```rust,ignore
// After push_str, length increases by str.len()
// len(s) = len(s) + len(str)
```

#### `String::clear()`
```rust,ignore
// After clear, length becomes 0
// len(s) = 0
```

#### `String::truncate(n)`
```rust,ignore
// After truncate, length is min(old_len, n)
// len(s) = min(len(s), n)
```

#### `String::pop()`
```rust,ignore
// After pop (if non-empty), length decreases by at least 1
// if len(s) > 0 then len(s) = len(s) - 1
```

#### `String::insert(idx, ch)`, `String::insert_str(idx, str)`
```rust,ignore
// After insert, length increases
// insert: len(s) = len(s) + 1
// insert_str: len(s) = len(s) + len(str)
```

#### `String::remove(idx)`
```rust,ignore
// After remove, length decreases
// len(s) = len(s) - 1
```

### Example

```rust,ignore
// String::new() creates an empty string
#[ensures("result == 0")]
fn string_new_len() -> usize {
    let s: String = String::new();
    s.len()
}

// String::is_empty() is true for new strings
#[ensures("result")]
fn string_new_is_empty() -> bool {
    let s: String = String::new();
    s.is_empty()
}

// Push increases length
#[ensures("result == 1")]
fn string_push_one() -> usize {
    let mut s = String::new();
    s.push('a');
    s.len()
}

// Clear then push gives length 1
#[ensures("result == 1")]
fn string_clear_push() -> usize {
    let mut s = String::new();
    s.push('x');
    s.push('y');
    s.clear();
    s.push('z');
    s.len()
}

// Parameter with length precondition
#[requires("s.len() > 0")]
#[ensures("result > 0")]
fn non_empty_string(s: &String) -> usize {
    s.len()
}
```

**Note**:
- String literals (`"..."`) do not have their length modeled in the current architecture.
- Mutation tracking requires known initial state (e.g., via `String::new()` or `String::clear()`).
- Character contents are not tracked, only length.

## &str Methods

tRust supports `&str` slice length queries. The `len` function is treated as an uninterpreted function.

### Length Queries

#### `str::len()`, `str::is_empty()`

```rust,ignore
#[ensures("result == s.len()")]
#[ensures("result == s.is_empty()")]
```

### Example

```rust,ignore
// str parameter with length precondition
#[requires("s.len() > 0")]
#[ensures("result > 0")]
fn non_empty_str(s: &str) -> usize {
    s.len()
}
```

**Note**:
- String literals (`""`) do not establish their length in the verification model.
- Use preconditions on parameters to establish length constraints.

## Iterator Methods

tRust models basic iterator methods.

### `Iterator::count()`

```rust,ignore
#[ensures("result >= 0")]
```

Consumes the iterator and returns the element count.

### `ExactSizeIterator::len()`

```rust,ignore
#[ensures("result >= 0")]
```

Returns the exact remaining length without consuming the iterator.

### Example

```rust,ignore
#[ensures("result >= 0")]
fn count_elements(v: Vec<i32>) -> usize {
    v.into_iter().count()
}

#[ensures("result >= 0")]
fn iter_length(v: &Vec<i32>) -> usize {
    v.iter().len()
}
```

**Note**:
- Iterator methods that return `Option` (like `last`, `nth`, `max`, `min`) don't have strong postconditions because we don't track iterator contents.
- Accumulating methods (`sum`, `product`) also don't have strong postconditions.

## Usage Example

```rust,ignore
fn example(a: i32, b: i32) -> i32 {
    // tRust uses builtin contracts automatically
    let minimum = std::cmp::min(a, b);
    // Known: minimum <= a && minimum <= b

    let clamped = a.clamp(0, 100);
    // Known: 0 <= clamped <= 100

    let positive = a.saturating_add(b);
    // Known: positive >= a && positive >= b (if both >= 0)

    minimum + clamped
}
```

## Adding Custom Builtins

Currently, builtin contracts are defined in `kani_bridge.rs`. Future versions may support user-defined builtin contracts through configuration.

## Type-Specific Bit Widths

The bit width constraints adjust per type:

| Type | bit_width | max_log10 |
|------|-----------|-----------|
| `u8` / `i8` | 8 | 2 |
| `u16` / `i16` | 16 | 4 |
| `u32` / `i32` | 32 | 9 |
| `u64` / `i64` | 64 | 18 |
| `u128` / `i128` | 128 | 38 |

## Next Steps

- [Specification Attributes](./attributes.md) - Writing your own specifications
- [Modular Verification](../advanced/modular.md) - Using contracts in composition
