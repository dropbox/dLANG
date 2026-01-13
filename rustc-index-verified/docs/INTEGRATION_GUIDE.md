# Integration Guide

Using rustc-index-verified specifications in tRust projects.

## Overview

rustc-index-verified provides formal specifications for type-safe indexing data structures. This guide explains how to:
1. Use the verified crate as a dependency
2. Understand specification attributes
3. Verify your own code using these specs
4. Extend specifications to new modules

## Adding the Dependency

```toml
[dependencies]
rustc-index-verified = { path = "../deps/rustc-index-verified" }
```

Or, when the crate is published:
```toml
[dependencies]
rustc-index-verified = "0.1"
```

## Understanding Specification Attributes

Specifications use `trust_macros` attributes that are processed by trustc:

### `#[requires(expr)]` - Preconditions

Preconditions must hold when calling the function:

```rust
use trust_macros::requires;

impl Idx for u32 {
    #[requires(idx <= u32::MAX as usize)]  // Caller must ensure this
    fn new(idx: usize) -> Self {
        assert!(idx <= u32::MAX as usize);
        idx as u32
    }
}
```

### `#[ensures(expr)]` - Postconditions

Postconditions hold when the function returns:

```rust
use trust_macros::ensures;

impl IndexVec<I, T> {
    #[ensures(result.index() == old(self.raw.len()))]  // Proven by trustc
    #[ensures(self.raw.len() == old(self.raw.len()) + 1)]
    pub fn push(&mut self, d: T) -> I {
        let idx = I::new(self.raw.len());
        self.raw.push(d);
        idx
    }
}
```

### Special Expressions

| Expression | Meaning |
|------------|---------|
| `result` | Return value of the function |
| `old(expr)` | Value of `expr` at function entry |
| `forall \|x: T\| pred` | Universal quantification |
| `exists \|x: T\| pred` | Existential quantification |
| `a => b` | Logical implication (`!a \|\| b`) |

## Data Structures

### Idx Trait

Type-safe index wrapper. Implementations provided for `u32` and `usize`.

```rust
use rustc_index_verified::Idx;

// Custom index type
struct MyIdx(u32);

impl Idx for MyIdx {
    #[requires(idx <= u32::MAX as usize)]
    #[ensures(result.0 as usize == idx)]
    fn new(idx: usize) -> Self { MyIdx(idx as u32) }

    #[ensures(result == self.0 as usize)]
    fn index(self) -> usize { self.0 as usize }
}
```

### IndexVec<I, T>

Type-indexed vector. Key specifications:

| Method | Precondition | Postcondition |
|--------|--------------|---------------|
| `new()` | - | `len == 0` |
| `push(d)` | - | `result.index() == old(len)`, `len == old(len) + 1` |
| `pop()` | - | `old(len) > 0 => result.is_some()` |
| `truncate(a)` | - | `len <= old(len)`, `len <= a` |
| `get(i)` | - | `i < len => result.is_some()` |

### IndexSlice<I, T>

Reference wrapper for slices. Key specifications:

| Method | Precondition | Postcondition |
|--------|--------------|---------------|
| `get(i)` | - | `i < len => result.is_some()` |
| `swap(a, b)` | `a < len && b < len` | - |
| `pick2_mut(a, b)` | `a != b && a < len && b < len` | - |

### IntervalSet<I>

Set represented as sorted, non-overlapping intervals. Key specifications:

| Method | Precondition | Postcondition |
|--------|--------------|---------------|
| `insert(p)` | `p < domain` | - |
| `contains(p)` | - | Accurate membership |
| `union(other)` | `domain == other.domain` | - |

### BitSet<T>

Dense bitset. Key specifications:

| Method | Precondition | Postcondition |
|--------|--------------|---------------|
| `contains(e)` | `e < domain_size` | - |
| `insert(e)` | `e < domain_size` | `self.contains(e)` |
| `remove(e)` | `e < domain_size` | `!self.contains(e)` |
| `union(other)` | `domain_size == other.domain_size` | - |

### BitMatrix<R, C>

2D bit matrix for reachability and relation analysis. Key specifications:

| Method | Precondition | Postcondition |
|--------|--------------|---------------|
| `new(rows, cols)` | - | `num_rows == rows`, `num_columns == cols` |
| `insert(r, c)` | `r < num_rows && c < num_columns` | `self.contains(r, c)` |
| `contains(r, c)` | `r < num_rows && c < num_columns` | - |
| `union_rows(read, write)` | `read < num_rows && write < num_rows` | - |
| `iter(r)` | `r < num_rows` | Yields set columns |

Example usage for transitive closure:

```rust
use rustc_index_verified::BitMatrix;

// Graph: 0 -> 1 -> 2
let mut reach: BitMatrix<usize, usize> = BitMatrix::new(3, 3);
reach.insert(0, 1);  // 0 can reach 1
reach.insert(1, 2);  // 1 can reach 2

// Propagate: 0 can reach what 1 can reach
reach.union_rows(1, 0);
assert!(reach.contains(0, 2));  // Now 0 can reach 2
```

## Verifying Your Code

### Step 1: Add Specifications

```rust
use trust_macros::{requires, ensures};
use rustc_index_verified::{IndexVec, Idx};

struct NodeId(u32);
impl Idx for NodeId { /* ... */ }

struct Graph {
    nodes: IndexVec<NodeId, Node>,
}

impl Graph {
    #[ensures(result.index() == old(self.nodes.len()))]
    fn add_node(&mut self, node: Node) -> NodeId {
        self.nodes.push(node)
    }

    #[requires(id.index() < self.nodes.len())]
    fn get_node(&self, id: NodeId) -> &Node {
        &self.nodes[id]
    }
}
```

### Step 2: Run Verification

```bash
# From your project directory
~/tRust/tools/trustc src/lib.rs -Zverify --edition 2021

# With detailed output
~/tRust/tools/trustc src/lib.rs -Zverify --edition 2021 --output-format=json
```

### Step 3: Interpret Results

- **PROVEN**: Specification verified for all inputs
- **DISPROVEN**: Counterexample found (fix spec or implementation)
- **UNKNOWN**: Solver timeout (simplify spec or increase resources)

## Best Practices

### 1. Start with Simple Properties

Begin with obvious properties:
```rust
#[ensures(result.len() == 0)]
fn new() -> Self { /* ... */ }
```

### 2. Add Preconditions for Bounds

Always specify bounds:
```rust
#[requires(idx < self.len())]
fn get(&self, idx: I) -> &T { /* ... */ }
```

### 3. Use `old()` for Mutation

Track changes:
```rust
#[ensures(self.len() == old(self.len()) + 1)]
fn push(&mut self, val: T) { /* ... */ }
```

### 4. Document Invariants

Annotate complex invariants:
```rust
/// Invariant: intervals are sorted, non-overlapping, non-adjacent
struct IntervalSet<I: Idx> {
    // intervals: SmallVec<[(u32, u32); 2]>
    // forall i: intervals[i].1 < intervals[i+1].0
}
```

### 5. Const Functions

Note: `const fn` cannot have attributes. Document specs in doc comments:
```rust
/// # Specification
/// ensures(result.len() == 0)
pub const fn new() -> Self { /* ... */ }
```

## Limitations

1. **Const functions**: Cannot have `#[requires]`/`#[ensures]` attributes
2. **Trait methods**: Attribute placement on trait methods vs impls varies
3. **Iterator methods**: Complex lifetimes prevent some specs
4. **Solver limitations**: See tests/solver_limitations.rs for edge cases

## Module Status

| Module | Functions | With Specs | Verified |
|--------|-----------|------------|----------|
| idx.rs | 8 | 8 | 4 |
| vec.rs | 28 | 28 | 8 |
| slice.rs | 21 | 21 | 4 |
| interval.rs | 25 | 25 | 2 |
| bit_set.rs | 120 | 120 | 42 |
| **Total** | **202** | **202** | **60** |

See docs/VERIFICATION_STATUS.md for detailed function-level tracking.

## Verification

The project is **COMPLETE** with 60/60 attributed functions verified by trustc (82 total spec attributes: 78 verified specs + 4 `#[requires]` on `#[pure]` fns).

```bash
# Run verification
RUSTC=~/tRust/bin/trustc RUSTC_WRAPPER=./scripts/trust-workspace-wrapper.sh cargo check
```

## Next Steps

1. Extend to other rustc components (rustc-arena, rustc-data-structures)
2. Use docs/VERIFICATION_TEMPLATE.md as a starting point for new projects
