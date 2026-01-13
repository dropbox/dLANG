# tRust Spec File Format

Specification files define contracts for external crate functions.

## File Structure

Each TOML file specifies contracts for a single crate:

```toml
[crate]
name = "crate_name"
version = "1.0"           # Minimum version (optional)
trust_level = "audited"   # verified | audited | assumed

[[function]]
name = "crate_name::module::function"
# Contract fields...

[[method]]
name = "crate_name::Type::method"
# Contract fields...
```

## Crate Section

| Field | Type | Required | Description |
|-------|------|----------|-------------|
| `name` | string | yes | Crate name (as in Cargo.toml) |
| `version` | string | no | Minimum version these specs apply to |
| `trust_level` | string | yes | `verified`, `audited`, or `assumed` |

## Function/Method Sections

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `name` | string | required | Full path: `crate::module::function` |
| `preconditions` | array[string] | [] | Precondition expressions |
| `postconditions` | array[string] | [] | Postcondition expressions |
| `pure` | bool | false | Function has no side effects |
| `may_diverge` | bool | false | Function may not terminate |
| `effects` | array[string] | null | Effect annotations: IO, Alloc, Panic, Diverge, Unsafe, GlobalState |

## Expression Syntax

Preconditions and postconditions use SMT-LIB S-expression syntax:

```toml
preconditions = [
    "(> arg0 0)",           # arg0 > 0
    "(not (= arg1 0))",     # arg1 != 0
    "(<= arg0 arg1)"        # arg0 <= arg1
]

postconditions = [
    "(>= result 0)",        # result >= 0
    "(= result (+ arg0 arg1))"  # result == arg0 + arg1
]
```

### Variables

- `arg0`, `arg1`, ...: Function arguments (positional)
- `self`: Receiver for methods
- `result`: Return value (postconditions only)
- `old(expr)`: Value of expr before call (postconditions only)

## Examples

### Simple Function

```toml
[[function]]
name = "regex::Regex::new"
preconditions = []
postconditions = []  # Result type handles errors
effects = ["Alloc"]
```

### Method with Precondition

```toml
[[method]]
name = "indexmap::IndexMap::get_index"
preconditions = ["(< arg0 (len self))"]  # index < len
postconditions = []
pure = true
```

### Pure Function with Postcondition

```toml
[[function]]
name = "num_traits::identities::one"
preconditions = []
postconditions = ["(not (= result 0))"]  # one() != 0
pure = true
```

### Function with Effects

```toml
[[function]]
name = "tokio::fs::read_to_string"
preconditions = []
postconditions = []
effects = ["IO", "Alloc"]
may_diverge = true
```

## Trust Levels

- `verified`: Specs have been formally verified against the implementation
- `audited`: Specs have been manually reviewed for correctness
- `assumed`: Specs are provided but not verified (use with caution)

## Version Compatibility

The `version` field specifies the minimum crate version these specs apply to.
Specs may be invalidated by breaking changes in newer versions.

When a crate updates its API, specs should be reviewed and updated accordingly.
