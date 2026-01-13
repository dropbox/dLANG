# Cargo Integration

tRust integrates with Cargo through the `cargo-trust` tool, enabling verification as part of your normal build workflow.

## Installation

The `cargo-trust` wrapper is included in the tRust distribution:

```bash
# From tRust directory
./rebuild.sh  # Builds cargo-trust along with trustc
```

Or link it manually:

```bash
ln -s /path/to/tRust/bin/cargo-trust ~/.cargo/bin/cargo-trust
```

## Basic Usage

### Verify a Package

```bash
cargo trust check
```

This:
1. Compiles dependencies normally
2. Verifies your crate's functions with specifications
3. Reports verification results

### Build with Verification

```bash
cargo trust build
```

Verifies then compiles if verification succeeds.

### Test with Verification

```bash
cargo trust test
```

Runs verification then executes tests.

## Commands

| Command | Description |
|---------|-------------|
| `cargo trust check` | Verify without building |
| `cargo trust build` | Verify then build |
| `cargo trust test` | Verify then run tests |
| `cargo trust run` | Verify then run binary |
| `cargo trust verify` | Only verification (alias for check) |

## Configuration

Configure tRust in your `Cargo.toml`:

```toml
[package]
name = "myproject"
version = "0.1.0"

[package.metadata.trust]
# Verification settings
verify = true              # Enable verification (default: true)
trust_level = "verified"   # verified, assumed, or audited
json_output = false        # Output JSON format
use_cache = true           # Enable verification cache

# Solver settings
solver_timeout = 30000     # Timeout per query (ms)
solver_verbose = false     # Show solver output

# Cache settings
cache_dir = ".trust_cache"
use_global_cache = false
```

## Environment Variables

Override config with environment variables:

| Variable | Description |
|----------|-------------|
| `TRUST_VERIFY` | Enable/disable verification (0/1) |
| `TRUST_JSON_OUTPUT` | Enable JSON output (0/1) |
| `TRUST_SYSROOT` | Override sysroot path |
| `TRUST_CACHE_DIR` | Cache directory |
| `TRUST_USE_GLOBAL_CACHE` | Use global cache (0/1) |

Example:

```bash
TRUST_JSON_OUTPUT=1 cargo trust check
```

## Workspace Support

For workspaces, verify all members:

```bash
cargo trust check --workspace
```

Or specific packages:

```bash
cargo trust check -p mylib
cargo trust check -p mybin
```

## Dependency Verification

### Verifying Dependencies

Dependencies compiled with trustc preserve their contracts:

```toml
[dependencies]
verified_math = { git = "...", features = ["trust-specs"] }
```

### External Crates

For crates without tRust specs:

```toml
[package.metadata.trust.dependencies]
# Assume contracts for external crates
serde = { trust_level = "assumed" }
tokio = { trust_level = "audited" }
```

## Build Scripts

Verification runs after build scripts:

```rust,ignore
// build.rs
fn main() {
    // Build script runs normally
    // Then verification runs
}
```

## Feature Flags

Control verification with features:

```toml
[features]
default = ["verify"]
verify = []  # Enable verification specs

[package.metadata.trust]
# Only verify when feature enabled
verify_feature = "verify"
```

```bash
cargo trust check                  # Verification enabled
cargo trust check --no-default-features  # Verification disabled
```

## CI/CD Integration

### GitHub Actions

```yaml
name: Verify
on: [push, pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3

      - name: Install tRust
        run: |
          git clone https://github.com/dropbox/dLANG/tRust.git
          cd tRust && ./rebuild.sh

      - name: Verify
        run: |
          export PATH="$PWD/tRust:$PATH"
          cargo trust check

      - name: Lock specs
        run: |
          TRUST_WRITE_SPEC_LOCKFILE=trust-specs.lock cargo trust check
          git diff --exit-code trust-specs.lock
```

### GitLab CI

```yaml
verify:
  script:
    - ./setup-trust.sh
    - cargo trust check --json > verification.json
  artifacts:
    paths:
      - verification.json
```

## Output Formats

### Standard Output

```console
Verifying src/lib.rs...
  clamp_positive: PROVEN (2/2 postconditions)
  bad_abs: DISPROVEN (counterexample: x = -2147483648)

Verification: 1/2 functions verified
```

### JSON Output

```bash
cargo trust check --json
```

```json
{
  "package": "myproject",
  "functions": [...],
  "summary": {
    "total": 2,
    "proven": 1,
    "disproven": 1
  }
}
```

## Troubleshooting

### "Cannot find crate"

Ensure dependencies are compiled first:

```bash
cargo build  # Compile deps
cargo trust check  # Then verify
```

### Verification Timeout

Increase timeout:

```toml
[package.metadata.trust]
solver_timeout = 60000  # 60 seconds
```

Or simplify specifications.

### Cache Issues

Clear and rebuild cache:

```bash
cargo trust cache clear
cargo trust check
```

## Next Steps

- [JSON Output](./json.md) - Detailed JSON format
- [Error Codes](../reference/errors.md) - Understanding verification errors
