# Array Bounds Checking

Out-of-bounds array access is undefined behavior in many languages. While Rust prevents it at runtime with panics, tRust can prove at compile time that bounds violations never occur.

## The Problem

```rust,ignore
fn get_element(arr: &[i32], index: usize) -> i32 {
    arr[index]  // Panics if index >= arr.len()
}
```

This compiles, but will panic at runtime if `index` is out of bounds.

## Preconditions for Bounds Safety

Add a precondition to require valid indices:

```rust,ignore
#[requires("index < arr.len()")]
fn get_element(arr: &[i32], index: usize) -> i32 {
    arr[index]  // Proven safe!
}
```

Now tRust:
1. Assumes `index < arr.len()` inside the function
2. Checks that callers satisfy this condition

## Verifying Loop Bounds

For loops accessing arrays:

```rust,ignore
#[requires("arr.len() > 0")]
#[ensures("result >= arr[0]")]
fn find_max(arr: &[i32]) -> i32 {
    let mut max = arr[0];  // Safe: arr.len() > 0
    let mut i = 1;
    while i < arr.len() {
        // Inside loop: i < arr.len(), so arr[i] is safe
        if arr[i] > max {
            max = arr[i];
        }
        i += 1;
    }
    max
}
```

## Using get() for Safe Access

The `get()` method returns `Option<&T>`:

```rust,ignore
fn safe_get(arr: &[i32], index: usize) -> Option<i32> {
    arr.get(index).copied()
}
```

This never panics, returning `None` for out-of-bounds indices.

## Slice Specifications

### Non-Empty Slices

```rust,ignore
#[requires("slice.len() > 0")]
fn process_nonempty(slice: &[i32]) { ... }
```

### Fixed-Size Slices

```rust,ignore
#[requires("slice.len() >= 4")]
fn process_quad(slice: &[i32]) -> (i32, i32, i32, i32) {
    (slice[0], slice[1], slice[2], slice[3])  // All safe
}
```

### Slice Relationships

```rust,ignore
#[requires("a.len() == b.len()")]
fn pointwise_add(a: &[i32], b: &[i32], out: &mut [i32]) {
    // ...
}
```

## Common Patterns

### First/Last Element

```rust,ignore
#[requires("arr.len() > 0")]
#[ensures("result == arr[0]")]
fn first(arr: &[i32]) -> i32 {
    arr[0]
}

#[requires("arr.len() > 0")]
#[ensures("result == arr[arr.len() - 1]")]
fn last(arr: &[i32]) -> i32 {
    arr[arr.len() - 1]
}
```

### Binary Search Index

```rust,ignore
#[requires("sorted.len() > 0")]
#[ensures("result < sorted.len()")]
fn binary_search_index(sorted: &[i32], target: i32) -> usize {
    let mut lo = 0;
    let mut hi = sorted.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;  // No overflow
        if sorted[mid] < target {      // mid < hi <= len, so safe
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo.min(sorted.len() - 1)  // Ensure valid index
}
```

### Range Slicing

```rust,ignore
#[requires("start <= end")]
#[requires("end <= arr.len()")]
fn subslice(arr: &[i32], start: usize, end: usize) -> &[i32] {
    &arr[start..end]
}
```

## Vector Operations

For `Vec<T>`, the same principles apply:

```rust,ignore
#[requires("vec.len() > 0")]
fn pop_front(vec: &mut Vec<i32>) -> i32 {
    vec.remove(0)  // Safe: len > 0
}

#[requires("index <= vec.len()")]
fn insert_at(vec: &mut Vec<i32>, index: usize, value: i32) {
    vec.insert(index, value);  // Safe: index <= len
}
```

## Multi-Dimensional Arrays

For 2D arrays represented as 1D:

```rust,ignore
#[requires("rows > 0 && cols > 0")]
#[requires("row < rows && col < cols")]
fn get_2d(data: &[i32], rows: usize, cols: usize, row: usize, col: usize) -> i32 {
    // Need: row * cols + col < data.len()
    // Given: row < rows, col < cols, data.len() >= rows * cols (implicit)
    data[row * cols + col]
}
```

## Proving Bounds in Complex Cases

Sometimes the bounds check isn't obvious to the solver:

```rust,ignore
#[requires("arr.len() >= 10")]
fn complex_access(arr: &[i32], x: usize) -> i32 {
    // x % 10 is always < 10, and 10 <= arr.len()
    arr[x % 10]  // Safe!
}
```

tRust uses SMT solving to determine that `x % 10 < 10 <= arr.len()`.

## Best Practices

1. **Prefer iterators when possible**: `for x in arr` avoids index bounds issues
2. **Use preconditions for index parameters**: Document and verify requirements
3. **Consider `get()` for potentially-invalid indices**: Returns `Option` instead of panicking
4. **Group related bounds requirements**: Multiple indices into same array should share preconditions

## Next Steps

- [Working with Structs](./structs.md) - Verify properties of structured data
- [Modular Verification](../advanced/modular.md) - Compose verified functions
