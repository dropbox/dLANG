# Error Codes

tRust verification errors use codes starting with E09xx. Use `trustc --explain E09xx` for detailed explanations.

## E0900: Verification Condition Not Provable

The SMT solver could not prove a verification condition.

```console
error[E0900]: verification failed: postcondition
  --> src/lib.rs:10:5
   |
10 |     x + 1
   |     ^^^^^ verification condition declared here
   |
   = note: counterexample: x = 2147483647
```

**Common causes:**
- Postcondition not satisfied by implementation
- Precondition violation at call site
- Overflow possible without bounds checks

**Resolution:** Add preconditions, use checked arithmetic, or fix implementation:

```rust,ignore
// Error: postcondition cannot be proven
#[ensures("result > 0")]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }  // -x overflows for i32::MIN!
}

// Fixed: add precondition to exclude edge case
#[requires("x > i32::MIN")]
#[ensures("result >= 0")]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

## E0901: Termination Not Proven

The verifier cannot prove that a recursive function or loop terminates.

```console
error[E0901]: termination not proven
  --> src/lib.rs:5:1
   |
5  | fn factorial(n: i32) -> i32 { ... }
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ missing decreases clause
```

**Resolution:** Add termination measure:

```rust,ignore
// For recursive functions
#[requires("n >= 0")]
#[decreases(n)]
fn factorial(n: i32) -> i32 {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}

// For intentionally non-terminating functions
#[may_diverge]
fn event_loop() { loop { handle_request(); } }
```

## E0902: Temporal Property Violated

A temporal logic specification cannot be proven. This applies to async code and distributed systems.

```console
error[E0902]: temporal property violated
  --> src/lib.rs:10:1
   |
10 | #[temporal(eventually(responded))]
   | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ property not satisfied
```

**Common violations:**
- `eventually(condition)` - condition may never become true
- `always(invariant)` - invariant may be violated at some point
- `until(p, q)` - p may not hold until q becomes true

**Resolution:** Ensure all code paths establish the required property:

```rust,ignore
#[temporal(eventually(responded))]
async fn handle_request(req: Request) -> Response {
    // Ensure responded is set on all paths
    if !req.is_valid() {
        set_responded();  // Don't forget this!
        return Response::bad_request();
    }
    process(req).await
}
```

## E0903: Precondition Not Established

A function call does not satisfy the callee's precondition.

```console
error[E0903]: precondition of `sqrt` might not be satisfied
  --> src/lib.rs:10:5
   |
10 |     sqrt(x - y)
   |     ^^^^^^^^^^^ requires: x - y >= 0
   |
   = note: counterexample: x = 0, y = 1
```

**Resolution:** Add precondition to caller or handle the edge case:

```rust,ignore
// Option 1: Add precondition
#[requires("x >= y")]
fn caller(x: i32, y: i32) -> i32 {
    sqrt(x - y)
}

// Option 2: Handle edge case
fn caller(x: i32, y: i32) -> i32 {
    if x >= y { sqrt(x - y) } else { 0 }
}
```

## E0904: Invariant Not Preserved

A loop invariant is not maintained across iterations.

```console
error[E0904]: invariant might not hold
  --> src/lib.rs:15:1
   |
15 | #[invariant("sum >= 0")]
   | ^^^^^^^^^^^^^^^^^^^^^^ invariant not preserved
```

**For an invariant to be valid:**
1. **Establishment**: Invariant must hold before the loop
2. **Preservation**: If invariant holds at start of iteration, it must hold at end
3. **Usage**: Invariant + negated condition implies postcondition

**Resolution:** Strengthen or fix the invariant:

```rust,ignore
// Complete invariant captures loop state
#[invariant("i <= n")]
#[invariant("sum == i * (i + 1) / 2")]
while i <= n {
    sum += i;
    i += 1;
}
```

## E0905: Refinement Type Mismatch

A value does not satisfy a refinement type's predicate.

```console
error[E0905]: refinement type mismatch
  --> src/lib.rs:8:5
   |
8  |     first(v)
   |     ^^^^^^^^ expected NonEmpty<i32>, found Vec<i32>
```

**Resolution:** Add runtime check or precondition:

```rust,ignore
type NonEmpty<T> = Vec<T> where self.len() > 0;

// Option 1: Add precondition
#[requires("!v.is_empty()")]
fn use_first(v: Vec<i32>) -> i32 {
    first(v)
}

// Option 2: Runtime check
fn use_first(v: Vec<i32>) -> Option<i32> {
    if !v.is_empty() { Some(first(v)) } else { None }
}
```

## E0906: Arithmetic Overflow Possible

An arithmetic operation may overflow at runtime.

```console
error[E0906]: potential overflow in addition
  --> src/lib.rs:8:12
   |
8  |     let z = x + y;
   |             ^^^^^ might overflow
   |
   = note: counterexample: x = 2147483647, y = 1
```

**Resolution:** Add bounds or use checked/saturating operations:

```rust,ignore
// Option 1: Precondition
#[requires("x <= i32::MAX - y")]
fn add(x: i32, y: i32) -> i32 { x + y }

// Option 2: Checked operation
fn add(x: i32, y: i32) -> Option<i32> { x.checked_add(y) }

// Option 3: Saturating
fn add(x: i32, y: i32) -> i32 { x.saturating_add(y) }
```

## E0907: Division by Zero Possible

A division or modulo operation may have a zero divisor.

```console
error[E0907]: potential division by zero
  --> src/lib.rs:5:5
   |
5  |     sum / count
   |     ^^^^^^^^^^^ count could be 0
```

**Resolution:** Add precondition or runtime check:

```rust,ignore
// Option 1: Precondition
#[requires("count != 0")]
fn average(sum: i32, count: i32) -> i32 { sum / count }

// Option 2: Checked division
fn average(sum: i32, count: i32) -> Option<i32> {
    sum.checked_div(count)
}
```

## E0908: Array Index Out of Bounds

An array or slice access may be out of bounds.

```console
error[E0908]: array access might be out of bounds
  --> src/lib.rs:6:12
   |
6  |     arr[idx]
   |     ^^^^^^^^ index might be >= arr.len()
   |
   = note: counterexample: arr.len() = 5, idx = 10
```

**Resolution:** Add bounds check or precondition:

```rust,ignore
// Option 1: Precondition
#[requires("idx < arr.len()")]
fn get(arr: &[i32], idx: usize) -> i32 { arr[idx] }

// Option 2: Safe access
fn get(arr: &[i32], idx: usize) -> Option<i32> {
    arr.get(idx).copied()
}
```

## E0909: Unsafe Block Requires Proof

An unsafe block has verification conditions that must be proven.

```console
error[E0909]: unsafe block requires proof
  --> src/lib.rs:10:5
   |
10 |     *ptr = 42;
   |     ^^^^^^^^^ pointer validity not proven
```

**Requirements for unsafe verification:**
- Pointer validity
- Aliasing rules: no mutable aliasing
- Lifetime correctness

**Resolution:** Use `#[trusted]` sparingly for extern code:

```rust,ignore
#[trusted]  // Bypass verification - use with caution
unsafe fn call_extern() {
    extern_function();
}
```

## Diagnostic Levels

| Prefix | Meaning |
|--------|---------|
| `error` | Verification failed, must fix |
| `warning` | Potential issue, review recommended |
| `note` | Additional information |
| `help` | Suggested fix |

## Getting Help

For any error code:

```bash
trustc --explain E0902
```

This shows:
- Detailed explanation
- Common causes
- Example fixes
- Related errors

## Next Steps

- [Builtin Contracts](./builtins.md) - Contracts for standard library functions
- [Preconditions and Postconditions](../basic/pre-post.md) - Specification basics
