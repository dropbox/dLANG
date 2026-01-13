# Working with Structs

tRust can verify properties of structs, including field values and relationships between fields.

## Field Access in Specifications

You can reference struct fields in preconditions and postconditions:

```rust,ignore
struct Point {
    x: i32,
    y: i32,
}

#[requires("p.x >= 0 && p.y >= 0")]
#[ensures("result >= 0")]
fn manhattan_distance(p: Point) -> i32 {
    p.x + p.y
}
```

## Postconditions on Returned Structs

Use `result.field` to specify properties of returned structs:

```rust,ignore
#[ensures("result.x == x")]
#[ensures("result.y == y")]
fn new_point(x: i32, y: i32) -> Point {
    Point { x, y }
}
```

## Nested Field Access

For nested structs, use dot notation:

```rust,ignore
struct Rectangle {
    origin: Point,
    size: Point,
}

#[requires("r.origin.x >= 0 && r.origin.y >= 0")]
#[requires("r.size.x > 0 && r.size.y > 0")]
#[ensures("result > 0")]
fn area(r: &Rectangle) -> i32 {
    r.size.x * r.size.y
}
```

## Constructors with Invariants

Define constructor functions that establish invariants:

```rust,ignore
struct PositivePoint {
    x: i32,
    y: i32,
}

#[requires("x > 0 && y > 0")]
#[ensures("result.x == x && result.y == y")]
fn positive_point(x: i32, y: i32) -> PositivePoint {
    PositivePoint { x, y }
}
```

Functions receiving `PositivePoint` can use `positive_point`'s postcondition to assume `x > 0 && y > 0`.

## Tuple Structs

Tuple structs work with positional field access:

```rust,ignore
struct Pair(i32, i32);

#[ensures("result.0 <= result.1")]
fn ordered_pair(a: i32, b: i32) -> Pair {
    if a <= b {
        Pair(a, b)
    } else {
        Pair(b, a)
    }
}
```

## Methods and Self

For methods, `self` refers to the receiver:

```rust,ignore
impl Point {
    #[requires("self.x >= 0 && self.y >= 0")]
    #[ensures("result >= 0")]
    fn magnitude_squared(&self) -> i32 {
        self.x * self.x + self.y * self.y
    }

    #[ensures("result.x == self.x + dx")]
    #[ensures("result.y == self.y + dy")]
    fn translate(&self, dx: i32, dy: i32) -> Point {
        Point {
            x: self.x + dx,
            y: self.y + dy,
        }
    }
}
```

## Mutable References

For `&mut self` methods, specifications can relate old and new values:

```rust,ignore
impl Point {
    #[ensures("self.x == old(self.x) + dx")]
    #[ensures("self.y == old(self.y) + dy")]
    fn translate_mut(&mut self, dx: i32, dy: i32) {
        self.x += dx;
        self.y += dy;
    }
}
```

The `old()` function captures the value before the function executes.

## Struct Invariants

While tRust doesn't yet support `#[invariant]` on structs directly, you can enforce invariants through constructor patterns:

```rust,ignore
/// A range where start <= end
struct ValidRange {
    start: i32,
    end: i32,
}

impl ValidRange {
    #[requires("start <= end")]
    #[ensures("result.start == start")]
    #[ensures("result.end == end")]
    pub fn new(start: i32, end: i32) -> Self {
        ValidRange { start, end }
    }

    // All methods can assume start <= end because
    // the only way to create a ValidRange is through new()
    #[ensures("result >= 0")]
    pub fn length(&self) -> i32 {
        self.end - self.start  // Safe: end >= start
    }
}
```

## Enum Variants

For enums, you can specify properties based on variants:

```rust,ignore
enum Shape {
    Circle { radius: i32 },
    Rectangle { width: i32, height: i32 },
}

#[ensures("result >= 0")]
fn area(shape: &Shape) -> i32 {
    match shape {
        Shape::Circle { radius } => radius * radius * 3,  // Approximate
        Shape::Rectangle { width, height } => width * height,
    }
}
```

## Generic Structs

Specifications work with generic structs:

```rust,ignore
struct Container<T> {
    value: T,
    count: i32,
}

#[requires("c.count > 0")]
fn has_items<T>(c: &Container<T>) -> bool {
    true
}
```

## Best Practices

1. **Use constructor functions**: Establish invariants at creation time
2. **Keep fields private**: Prevent direct mutation that might violate invariants
3. **Document field relationships**: Use postconditions to express constraints
4. **Prefer immutable structs**: Easier to reason about than mutable state

## Limitations

Currently, tRust has some limitations with structs:

- No direct `#[invariant]` on struct definitions (use constructor patterns)
- Limited support for recursive struct types
- Method resolution may require explicit trait bounds

## Next Steps

- [Modular Verification](../advanced/modular.md) - Compose specifications across functions
- [Refinement Types](../advanced/refinements.md) - Type-level invariants
