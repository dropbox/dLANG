# Getting Started with tRust

tRust is a fork of rustc that integrates formal verification directly into the compiler. Write specifications, compile your code, and get mathematical proofs of correctness.

## Prerequisites

- **Rust 1.75+**: `rustup update stable`
- **CMake and Ninja**: `brew install cmake ninja` (macOS) or equivalent
- **Z3/Z4 SMT solver**: Built automatically during setup

## Installation

```bash
# Clone the repository
git clone https://github.com/dropbox/dLANG/tRust.git
cd tRust

# Initialize submodules
git submodule update --init --recursive

# Build the compiler (requires upstream/rustc - see note)
./rebuild.sh
```

The build produces `./bin/trustc`, the tRust compiler.

**Upstream rustc**: `./bin/trustc` and `./run_tests.sh` require a **tRust-patched** rustc source tree in `upstream/rustc/`.

- The patched fork lives on the `trust-verify` branch (currently `rustc 1.92.0`).
- If `upstream/rustc` is on a `sync/*` branch (vanilla rustc), the `-Zverify` flag will not exist and integration tests will fail.

Build the stage1 compiler:

```bash
cd upstream/rustc
git checkout trust-verify
./x.py build --stage 1
```

The default sysroot used by tRust is `upstream/rustc/build/host/stage1`. Override with `TRUST_SYSROOT=/path/to/stage1`.

## Your First Verified Program

The repository includes a small milestone example at `examples/hello_verified.rs`. It should verify as `VERIFIED`:

```rust
#![trust_level = "verified"]

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
    println!("Clamped: {}", x);
}
```

Compile with verification:

```bash
./bin/trustc examples/hello_verified.rs
```

By default, successful compilation may produce no output. To force verification (bypass cache) and see explicit verification logs, run:

```bash
./bin/trustc --no-cache --verify-verbose examples/hello_verified.rs
```

This should include `Function clamp_positive VERIFIED`. If verification was previously cached, `--verify-verbose` will report a cache hit; use `--no-cache` or `./bin/trustc --cache-clear` to re-run verification.

## Specification Attributes

### `#[requires("...")]` - Preconditions
Conditions the caller must satisfy:

```rust
#[requires("x > 0")]
#[requires("y != 0")]
fn safe_divide(x: i32, y: i32) -> i32 {
    x / y
}
```

### `#[ensures("...")]` - Postconditions
Conditions the function guarantees on return:

```rust
#[ensures("result >= 0")]
fn absolute(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

### `#[invariant("...")]` - Loop Invariants
Properties maintained during loop execution:

```rust
fn sum_to_n(n: u32) -> u32 {
    let mut sum = 0;
    let mut i = 0;
    #[invariant("sum == i * (i - 1) / 2")]
    #[invariant("i <= n + 1")]
    while i <= n {
        sum += i;
        i += 1;
    }
    sum
}
```

### `#[decreases("...")]` - Termination Metrics
Prove loops and recursion terminate:

```rust
#[decreases("n")]
fn factorial(n: u32) -> u32 {
    if n == 0 { 1 } else { n * factorial(n - 1) }
}
```

### `#[pure]` - Pure Functions
Mark functions as side-effect free (can be used in specs):

```rust
#[pure]
fn is_even(n: i32) -> bool {
    n % 2 == 0
}

#[requires("is_even(x)")]
fn process_even(x: i32) { /* ... */ }
```

## Trust Levels

Control verification granularity with crate-level attributes:

```rust
#![trust_level = "verified"]  // Full verification (default for specs)
#![trust_level = "assumed"]   // Skip verification (legacy code)
#![trust_level = "audited"]   // Has specs from external source
```

## Common Patterns

### Bounds Checking

```rust
#[requires("index < arr.len()")]
fn get_element(arr: &[i32], index: usize) -> i32 {
    arr[index]
}
```

### Non-Empty Collections

```rust
#[requires("!items.is_empty()")]
#[ensures("result.is_some()")]
fn first_item<T: Copy>(items: &[T]) -> Option<T> {
    items.first().copied()
}
```

### State Machine Invariants

```rust
struct Counter { value: u32, max: u32 }

impl Counter {
    #[requires("self.value < self.max")]
    #[ensures("self.value == old(self.value) + 1")]
    fn increment(&mut self) {
        self.value += 1;
    }
}
```

## Running Tests

```bash
# Run all integration tests
./run_tests.sh

# Run unit tests
cargo test --workspace

# Run Clippy
cargo clippy --workspace
```

## Development Setup

For contributors, install the pre-commit hook to catch issues before committing:

```bash
./scripts/install-hooks.sh
```

This hook runs:
1. Submodule SHA validation (ensures pushed)
2. rustc_vc build check
3. Workspace unit tests (~1,316 tests)

Note: Integration tests (`./run_tests.sh`) require `-Zverify` flag which is not yet
in a vanilla rustc. Build stage1 from the `trust-verify` branch to enable it.

Skip with `TRUST_SKIP_HOOKS=1` for emergency commits. Run full stage 1 build check with `TRUST_FULL_BUILD=1`.

## Troubleshooting

### "Specification parse error"
- Check string quotes in specs: `#[requires("x > 0")]` not `#[requires(x > 0)]`
- Ensure variables referenced in specs are in scope

### "DISPROVEN" or "UNKNOWN"
- The spec may be incorrect or too strong
- Add intermediate assertions or strengthen preconditions
- Check for integer overflow in arithmetic

### "Cannot find function in spec"
- Functions used in specs must be marked `#[pure]`
- Pure functions cannot have side effects

### Build Errors
```bash
# Rebuild from scratch
./rebuild.sh

# Update dependencies
git submodule update --init --recursive
```

## Further Reading

- `ROADMAP.md` - Project status and phases
- `README.md` - Project overview and architecture
- `deps/kani_fast/docs/SOUNDNESS_LIMITATIONS.md` - Known soundness limitations
- `examples/` - More verified examples
