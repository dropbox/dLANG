# Loop Invariants

Loops require special handling in verification because they can execute an unbounded number of times. Loop invariants are the key to verifying loops.

## What Is a Loop Invariant?

A loop invariant is a property that:
1. Holds before the loop starts
2. Is preserved by each iteration
3. Holds after the loop terminates

```rust,ignore
#[ensures("result == n * (n + 1) / 2")]
fn sum_to_n(n: i32) -> i32 {
    let mut sum = 0;
    let mut i = 0;

    #[invariant("sum == i * (i + 1) / 2")]
    #[invariant("i <= n")]
    while i < n {
        i += 1;
        sum += i;
    }

    sum
}
```

## The `#[invariant]` Attribute

Place invariant attributes immediately before the loop:

```rust,ignore
#[invariant("i >= 0")]
#[invariant("i <= arr.len()")]
#[invariant("sum >= 0")]
while i < arr.len() {
    // loop body
}
```

Multiple invariants can be combined:

```rust,ignore
#[invariant("i >= 0 && i <= n && sum == i * i")]
while i < n { /* ... */ }
```

## Verification Process

tRust verifies loops by checking:

1. **Initialization**: Invariant holds before the first iteration
2. **Preservation**: If invariant holds at start of iteration, it holds at end
3. **Utilization**: Invariant + loop exit condition proves postcondition

```rust,ignore
// 1. Before loop: i = 0, sum = 0
//    Invariant check: 0 == 0*(0+1)/2 ✓, 0 <= n ✓

// 2. Each iteration: assume sum == i*(i+1)/2 && i <= n
//    After i += 1; sum += i;
//    Check: sum == i*(i+1)/2 still holds ✓

// 3. After loop: i >= n && sum == i*(i+1)/2
//    Combined with i <= n: i == n
//    Therefore: sum == n*(n+1)/2 ✓
```

## Loop Variants (Termination)

To prove a loop terminates, use a variant - an expression that decreases each iteration:

```rust,ignore
#[invariant("i <= n")]
#[variant(n - i)]  // Decreases each iteration, bounded below by 0
while i < n {
    i += 1;
}
```

The variant must:
- Be an integer expression
- Decrease with each iteration
- Be bounded below (typically >= 0)

## Common Patterns

### Array Sum

```rust,ignore
#[requires("arr.len() < 1000")]  // Prevent overflow
#[ensures("result >= 0")]
fn sum_positive(arr: &[u32]) -> u32 {
    let mut sum: u32 = 0;
    let mut i = 0;

    #[invariant("i <= arr.len()")]
    #[invariant("sum <= i as u32 * 1000")]  // Bounded
    while i < arr.len() {
        sum += arr[i].min(1000);  // Cap individual values
        i += 1;
    }

    sum
}
```

### Finding Maximum

```rust,ignore
#[requires("arr.len() > 0")]
#[ensures("result >= arr[0]")]
fn find_max(arr: &[i32]) -> i32 {
    let mut max = arr[0];
    let mut i = 1;

    #[invariant("i <= arr.len()")]
    #[invariant("max >= arr[0]")]  // At least as big as first element
    while i < arr.len() {
        if arr[i] > max {
            max = arr[i];
        }
        i += 1;
    }

    max
}
```

### Binary Search

```rust,ignore
#[requires("arr.len() > 0")]
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut lo = 0;
    let mut hi = arr.len();

    #[invariant("lo <= hi")]
    #[invariant("hi <= arr.len()")]
    #[variant(hi - lo)]
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    None
}
```

## For Loops

For loops over iterators are often handled automatically:

```rust,ignore
fn sum_array(arr: &[i32]) -> i32 {
    let mut sum = 0;
    for x in arr {
        sum += x;
    }
    sum
}
```

For range-based for loops, invariants can be specified:

```rust,ignore
#[invariant("sum == i * (i - 1) / 2")]
for i in 0..n {
    sum += i;
}
```

## Nested Loops

Each loop needs its own invariant:

```rust,ignore
fn matrix_sum(rows: usize, cols: usize, data: &[i32]) -> i32 {
    let mut sum = 0;
    let mut i = 0;

    #[invariant("i <= rows")]
    while i < rows {
        let mut j = 0;

        #[invariant("j <= cols")]
        while j < cols {
            sum += data[i * cols + j];
            j += 1;
        }

        i += 1;
    }

    sum
}
```

## CHC-Based Invariant Inference

tRust can sometimes infer loop invariants automatically using Constrained Horn Clause (CHC) solving:

```rust,ignore
// Simple loops may not need explicit invariants
fn count_to(n: i32) -> i32 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i  // tRust can infer i == n
}
```

However, complex loops usually need manual invariants.

## Tips for Writing Invariants

1. **Start with bounds**: Ensure loop indices stay in bounds
2. **Track progress**: Relate loop variable to the goal
3. **Preserve relevant properties**: What does the postcondition need?
4. **Be precise enough**: Weak invariants may not prove the postcondition
5. **Don't be too strong**: Overly strong invariants may not be preserved

## Debugging Invariant Failures

When invariant verification fails:

1. **Initialization failure**: Invariant doesn't hold before loop
   - Check initial values match invariant

2. **Preservation failure**: Invariant not maintained by iteration
   - Check all paths through loop body preserve invariant
   - May need to strengthen invariant

3. **Postcondition failure**: Invariant + exit condition insufficient
   - May need to strengthen invariant
   - Check postcondition is achievable

## Next Steps

- [Refinement Types](./refinements.md) - Type-level invariants
- [Effects System](./effects.md) - Track side effects
