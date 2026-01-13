# Effects System

tRust tracks computational effects - actions like I/O, allocation, and panicking. This allows verification of effect-related properties.

## What Are Effects?

Effects are observable behaviors beyond returning a value:

| Effect | Description |
|--------|-------------|
| `IO` | File/network/console operations |
| `Alloc` | Heap allocation |
| `Panic` | May panic |
| `Diverge` | May not terminate |
| `Unsafe` | Uses unsafe code |
| `GlobalState` | Accesses global/static variables |

## The `#[effects]` Attribute

Declare a function's effects:

```rust,ignore
#[effects(IO)]
fn print_hello() {
    println!("Hello!");
}

#[effects(Alloc)]
fn create_vec() -> Vec<i32> {
    Vec::new()
}

#[effects(IO, Alloc)]
fn read_file() -> Vec<u8> {
    std::fs::read("file.txt").unwrap()
}
```

## Pure Functions with `#[pure]`

A pure function has no effects - it only computes a value from its inputs:

```rust,ignore
#[pure]
fn add(a: i32, b: i32) -> i32 {
    a + b  // No effects
}

#[pure]
fn factorial(n: u32) -> u32 {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}
```

`#[pure]` is equivalent to `#[effects()]` (empty effect set).

## Effect Checking

tRust checks that a function only performs declared effects:

```rust,ignore
#[pure]  // Declares no effects
fn bad_pure(x: i32) -> i32 {
    println!("x = {}", x);  // ERROR: IO effect not declared
    x
}
```

A function can call another only if callee effects are subset of caller effects:

```rust,ignore
#[effects(IO)]
fn print_num(n: i32) { println!("{}", n); }

#[pure]
fn compute() -> i32 {
    print_num(42);  // ERROR: pure can't call IO
    42
}

#[effects(IO)]
fn main_fn() {
    print_num(42);  // OK: IO ⊆ IO
}
```

## Effect Inference

tRust can infer effects from function bodies:

```rust,ignore
fn auto_inferred() {
    println!("Hello");  // IO effect inferred
    let v = Vec::new(); // Alloc effect inferred
}
// Inferred: #[effects(IO, Alloc)]
```

Explicit declarations override inference:

```rust,ignore
#[pure]  // Explicit: must have no effects
fn must_be_pure() -> i32 {
    42  // OK if body is actually pure
}
```

## Panic Effect

Division and array indexing may panic:

```rust,ignore
#[effects(Panic)]
fn might_panic(x: i32, y: i32) -> i32 {
    x / y  // Panics if y == 0
}
```

With a precondition, the panic is prevented:

```rust,ignore
#[requires("y != 0")]
#[pure]  // No panic because y != 0
fn safe_divide(x: i32, y: i32) -> i32 {
    x / y
}
```

## Common Effect Patterns

### Pure Computation

```rust,ignore
#[pure]
fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}
```

### I/O Functions

```rust,ignore
#[effects(IO)]
fn log_message(msg: &str) {
    eprintln!("[LOG] {}", msg);
}
```

### Allocating Functions

```rust,ignore
#[effects(Alloc)]
fn create_buffer(size: usize) -> Vec<u8> {
    vec![0; size]
}
```

### Mixed Effects

```rust,ignore
#[effects(IO, Alloc, Panic)]
fn read_config(path: &str) -> Config {
    let content = std::fs::read_to_string(path).unwrap();
    parse_config(&content)
}
```

## Effect Polymorphism

Higher-order functions can be polymorphic in their effects:

```rust,ignore
#[effects_of(f)]  // Has whatever effects f has
fn apply<T, U>(f: impl Fn(T) -> U, x: T) -> U {
    f(x)
}
```

The `#[effects_of(param)]` attribute means "this function has the effects of calling `param`".

```rust,ignore
// When called with pure function:
let result = apply(|x| x + 1, 42);  // Pure call

// When called with IO function:
let result = apply(|x| { println!("{}", x); x }, 42);  // IO call
```

## Benefits of Effect Tracking

1. **Memoization**: Pure functions can be cached
2. **Parallelization**: Pure functions are safe to parallelize
3. **Testing**: Pure functions are easier to test
4. **Optimization**: No-panic functions skip unwind handling

## Effect-Based Optimization (Future)

tRust aims to optimize based on effects:

- Pure functions: Safe to memoize or eliminate redundant calls
- No-panic functions: Skip unwind table generation
- No-alloc functions: Can run in no_std/embedded contexts

## Best Practices

1. **Prefer pure functions**: Easier to verify and test
2. **Isolate effects**: Push effects to the boundaries
3. **Declare effects explicitly**: Documentation and checking
4. **Use preconditions to eliminate Panic**: `#[requires("y != 0")]` makes division safe

## Current Status

tRust's effect system includes:
- Effect enum with all core effects
- `#[effects(...)]` and `#[pure]` attribute parsing
- Effect inference from function bodies
- Effect checking at call sites
- Effect polymorphism infrastructure

Future work:
- Effect-based optimizations in codegen
- More sophisticated effect inference
- Effect type syntax in function signatures

## Next Steps

- [Cross-Crate Verification](./cross-crate.md) - Effects across crate boundaries
- [Builtin Contracts](../reference/builtins.md) - Effects of standard library functions
