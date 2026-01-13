# Specification Attributes

This reference documents all specification attributes available in tRust.

## Core Specification Attributes

### `#[requires("condition")]`

Specifies a precondition - what must be true before the function is called.

```rust,ignore
#[requires("x > 0")]
#[requires("y != 0")]
fn divide(x: i32, y: i32) -> i32 { x / y }
```

- Multiple `#[requires]` attributes are ANDed together
- Can reference any parameter
- Condition is a string containing standard Rust expression syntax
- Supports array/slice indexing syntax like `arr[i]`

### `#[ensures("condition")]`

Specifies a postcondition - what the function guarantees to be true after returning.

```rust,ignore
#[ensures("result >= 0")]
#[ensures("result <= x")]
fn clamp_zero(x: i32) -> i32 { if x < 0 { 0 } else { x } }
```

- `result` refers to the return value
- Multiple `#[ensures]` attributes are ANDed together
- Condition is a string referencing parameters and `result`
- Supports array/slice indexing syntax like `arr[i]`

### `#[invariant("condition")]`

For loops, specifies a loop invariant.

```rust,ignore
let mut i = 0;
#[invariant("i <= n")]
#[invariant("sum == i * (i + 1) / 2")]
while i < n {
    i += 1;
    sum += i;
}
```

- Must hold before the loop starts
- Must be preserved by each iteration
- Placed immediately before the loop

## Termination Attributes

### `#[decreases(expression)]`

Specifies a termination measure for recursive functions.

```rust,ignore
#[requires("n >= 0")]
#[decreases(n)]
fn factorial(n: i32) -> i32 {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}
```

- Expression must be non-negative integer
- Must decrease with each recursive call

### `#[variant(expression)]`

Loop variant - proves loop termination.

```rust,ignore
#[invariant("i <= n")]
#[variant(n - i)]
while i < n { i += 1; }
```

- Must be non-negative integer
- Must decrease each iteration
- Combined with invariant to prove termination

### `#[may_diverge]`

Indicates function may not terminate (escape hatch).

```rust,ignore
#[may_diverge]
fn infinite_loop() {
    loop { }
}
```

### `#[mutual_recursion(fn1, fn2, ...)]`

Declares mutually recursive functions for termination checking.

```rust,ignore
#[mutual_recursion(is_even, is_odd)]
#[decreases(n)]
fn is_even(n: i32) -> bool { ... }

#[mutual_recursion(is_even, is_odd)]
#[decreases(n)]
fn is_odd(n: i32) -> bool { ... }
```

## Effects Attributes

### `#[effects(effect1, effect2, ...)]`

Declares the effects a function may have.

```rust,ignore
#[effects(IO, Alloc)]
fn read_file(path: &str) -> Vec<u8> { ... }
```

Available effects:
- `IO` - File, network, console I/O
- `Alloc` - Heap allocation
- `Panic` - May panic
- `Diverge` - May not terminate
- `Unsafe` - Uses unsafe code
- `GlobalState` - Accesses global/static state

### `#[pure]`

Declares function has no effects.

```rust,ignore
#[pure]
fn add(a: i32, b: i32) -> i32 { a + b }
```

Equivalent to `#[effects()]`.

### `#[effects_of(param)]`

Effect polymorphism - function has effects of calling parameter.

```rust,ignore
#[effects_of(f)]
fn apply<T, U>(f: impl Fn(T) -> U, x: T) -> U { f(x) }
```

## Trust Level Attributes

### `#![trust_level = "level"]`

Crate-level attribute controlling verification behavior.

```rust,ignore
#![trust_level = "verified"]   // Full verification (default)
#![trust_level = "assumed"]    // Skip verification
#![trust_level = "audited"]    // Has specs from audit
```

## Refinement Type Attributes

### `#[param_type(param: "predicate")]`

Refines a parameter type with a predicate.

```rust,ignore
#[param_type(x: "self > 0")]
fn sqrt(x: i32) -> i32 { ... }
```

### `#[return_type("predicate")]`

Refines the return type with a predicate.

```rust,ignore
#[return_type("self >= 0")]
fn abs(x: i32) -> i32 { ... }
```

## Neural Network Attributes

### `#[nn_model("path")]`

Specifies the model file for neural network verification.

```rust,ignore
#[nn_model("models/classifier.json")]
fn classify(input: &[f32]) -> usize { ... }
```

### `#[nn_bounds(lower, upper)]`

Specifies expected output bounds.

```rust,ignore
#[nn_bounds(0.0, 1.0)]
fn predict(x: &[f32]) -> f32 { ... }
```

### `#[certified_robust(epsilon, norm)]`

Specifies robustness certification requirements.

```rust,ignore
#[certified_robust(0.01, "linf")]
fn robust_classify(x: &[f32]) -> usize { ... }
```

### `#[monotonic(input => output)]`

Specifies monotonicity constraints.

```rust,ignore
#[monotonic(0 => 0)]  // Output 0 increases with input 0
fn price_model(features: &[f32]) -> &[f32] { ... }
```

### `#[fair(exclude = [indices])]`

Specifies fairness constraints.

```rust,ignore
#[fair(exclude = [0, 1])]  // Exclude indices 0,1 from affecting output
fn loan_decision(features: &[f32]) -> f32 { ... }
```

## Temporal Logic Attributes

### `#[temporal("formula")]`

Specifies temporal logic properties.

```rust,ignore
#[temporal("eventually(done)")]
async fn process() { ... }
```

## Wiring Attributes

### `#[wire_start]`

Marks function as application entry point.

```rust,ignore
#[wire_start]
fn main() { ... }
```

### `#[wire_state("name")]`

Marks function as reachable state.

```rust,ignore
#[wire_state("checkout")]
fn checkout_handler() { ... }
```

### `#[wire_must_reach("state1, state2")]`

Requires function to reach specified states.

```rust,ignore
#[wire_must_reach("payment_success, payment_error")]
fn process_payment() { ... }
```

### `#[wire_terminal]`

Marks function as valid end state.

```rust,ignore
#[wire_terminal]
fn confirmed() { ... }
```

### `#[wire_recoverable]`

Marks error state that must have recovery path.

```rust,ignore
#[wire_recoverable]
fn payment_failed() { ... }
```

### `#[wire_data_flow("input=>output")]`

Specifies data flow requirements.

```rust,ignore
#[wire_data_flow("user_id=>audit_log")]
fn handle_request(user_id: u64) { ... }
```

## Expression Syntax

Specification expressions support:

### Operators
- Arithmetic: `+`, `-`, `*`, `/`, `%`
- Comparison: `==`, `!=`, `<`, `<=`, `>`, `>=`
- Logical: `&&`, `||`, `!`
- Bitwise: `&`, `|`, `^`, `<<`, `>>`

### Special Variables
- `result` - Return value (in postconditions)
- `self` - Method receiver
- `old(expr)` - Value of expression before function call

### Field Access
- `param.field` - Struct field access
- `result.field` - Return struct field
- `param.field.nested` - Nested field access

### Method Calls
- `arr.len()` - Array/slice length
- `opt.is_some()` - Option check
- `res.is_ok()` - Result check

### Constants
- `i32::MIN`, `i32::MAX`
- `u32::MAX`
- Literal integers and booleans

## Next Steps

- [Error Codes](./errors.md) - Understanding verification errors
- [Builtin Contracts](./builtins.md) - Standard library contracts
