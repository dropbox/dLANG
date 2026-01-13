# Migration Guide: Adding Specs to Existing Code

How to gradually add formal verification to an existing Rust codebase.

## Step 1: Install and Test

```bash
# Build tRust (if not already done)
cd ~/tRust/upstream/rustc
./x.py build --stage 1

# Add to PATH
export PATH="$HOME/tRust/bin:$PATH"

# Test on your project (verification off)
cd your-project
trustc --no-verify src/lib.rs
```

Ensure your code compiles with tRust before enabling verification.

## Step 2: Start with Leaf Functions

Begin verification with **leaf functions** - functions that don't call other unverified code.

```rust
// Good starting point: pure computation, no external calls
fn calculate_discount(price: u32, percent: u32) -> u32 {
    price * percent / 100
}
```

Run verification:
```bash
trustc src/lib.rs
```

You'll likely see overflow warnings. Fix them:

```rust
#[requires(percent <= 100)]
#[requires(price <= u32::MAX / 100)]  // Prevent overflow in multiplication
fn calculate_discount(price: u32, percent: u32) -> u32 {
    price * percent / 100
}
```

## Step 3: Add Postconditions

Once preconditions are satisfied, add postconditions to document guarantees:

```rust
#[requires(percent <= 100)]
#[requires(price <= u32::MAX / 100)]
#[ensures(result <= price)]  // Discount never exceeds original price
fn calculate_discount(price: u32, percent: u32) -> u32 {
    price * percent / 100
}
```

## Step 4: Work Up the Call Stack

Once leaf functions have specs, verify their callers:

```rust
// Caller can now assume calculate_discount's postcondition
fn apply_discount(item: &mut Item) {
    let discount = calculate_discount(item.price, item.discount_percent);
    item.price -= discount;  // Safe: discount <= price
}
```

## Step 5: Handle Error Cases

For functions that return `Result` or `Option`:

```rust
// Document what makes this succeed vs fail
#[ensures(result.is_ok() == (value != 0))]
fn safe_divide(numerator: i32, value: i32) -> Result<i32, DivisionError> {
    if value == 0 {
        Err(DivisionError::DivideByZero)
    } else {
        Ok(numerator / value)
    }
}
```

## Step 6: Common Migration Patterns

### Pattern: Replacing Panics with Preconditions

Before:
```rust
fn get_item(arr: &[i32], idx: usize) -> i32 {
    arr[idx]  // May panic
}
```

After:
```rust
#[requires(idx < arr.len())]
fn get_item(arr: &[i32], idx: usize) -> i32 {
    arr[idx]  // Verified safe
}
```

### Pattern: Making Implicit Assumptions Explicit

Before:
```rust
fn process_positive(x: i32) -> i32 {
    // Assumes x > 0 but doesn't check
    x * 2
}
```

After:
```rust
#[requires(x > 0)]
#[requires(x <= i32::MAX / 2)]  // Overflow protection
#[ensures(result > 0)]
fn process_positive(x: i32) -> i32 {
    x * 2
}
```

### Pattern: Using Checked Arithmetic

When you can't constrain inputs:

```rust
// Instead of adding preconditions everywhere
fn flexible_add(a: i32, b: i32) -> i32 {
    a.checked_add(b).unwrap_or(i32::MAX)
}

// Or saturating for bounded results
fn bounded_add(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}
```

### Pattern: Struct Invariants

Document type invariants:

```rust
struct PositiveRange {
    start: u32,
    end: u32,
}

impl PositiveRange {
    #[requires(start <= end)]
    fn new(start: u32, end: u32) -> Self {
        PositiveRange { start, end }
    }

    // Methods can assume the invariant holds
    fn len(&self) -> u32 {
        self.end - self.start  // Safe: start <= end
    }
}
```

## Step 7: Dealing with External Code

For code that calls unverified external functions:

```rust
// Mark external functions as trusted
#[trusted]
extern "C" fn external_computation(x: i32) -> i32;

// Wrap with verified interface
#[requires(x >= 0)]
#[ensures(result >= 0)]  // We trust this holds
fn call_external(x: i32) -> i32 {
    // Safety: external_computation documented to return non-negative for non-negative input
    unsafe { external_computation(x) }
}
```

## Step 8: Incremental Verification

You don't need to verify everything at once:

```rust
// Verified module
mod verified {
    #[requires(x > 0)]
    #[ensures(result > 0)]
    pub fn safe_double(x: i32) -> i32 {
        x.saturating_mul(2).max(1)
    }
}

// Unverified module (uses verified functions)
mod unverified {
    use super::verified::safe_double;

    pub fn process(x: i32) {
        if x > 0 {
            let doubled = safe_double(x);  // Precondition satisfied
            println!("{}", doubled);
        }
    }
}
```

## Common Issues and Solutions

### Issue: "overflow possible"

```
error[E0906]: arithmetic overflow possible
 --> src/lib.rs:5:5
```

**Solutions:**
1. Add bounds with `#[requires(...)]`
2. Use checked arithmetic: `checked_add`, `checked_mul`
3. Use saturating arithmetic: `saturating_add`, `saturating_sub`

### Issue: "division by zero possible"

```
error[E0907]: division by zero possible
 --> src/lib.rs:10:5
```

**Solutions:**
1. Add `#[requires(divisor != 0)]`
2. Check before dividing: `if divisor != 0 { ... }`
3. Use `checked_div`

### Issue: "precondition not established"

```
error[E0903]: precondition not established
 --> src/lib.rs:15:5
```

**Solutions:**
1. Add guards before the call
2. Propagate the precondition to the caller
3. Verify the context implies the precondition

### Issue: "index out of bounds"

```
error[E0908]: array index out of bounds
 --> src/lib.rs:20:5
```

**Solutions:**
1. Add `#[requires(idx < arr.len())]`
2. Use `arr.get(idx)` instead of `arr[idx]`
3. Check bounds before indexing

## Tips for Success

1. **Start small**: Verify one module at a time
2. **Use counterexamples**: They show exactly what input causes issues
3. **Run `trustc --explain`**: Get detailed help on error codes
4. **Document why**: Specs serve as executable documentation
5. **Test with verification off**: Ensure behavior doesn't change
6. **Review specs in code review**: Specs are contracts worth reviewing

## Checking Progress

Count verified vs unverified functions:

```bash
# Functions with specs
grep -r "#\[requires\|#\[ensures" src/ | wc -l

# All functions
grep -r "^pub fn\|^fn" src/ | wc -l
```

## Next Steps

- Read `docs/SPEC_PATTERNS.md` for common patterns
- Run `trustc --explain E0900` for error details
- Use JSON output for CI integration: `trustc --output-format=json`
