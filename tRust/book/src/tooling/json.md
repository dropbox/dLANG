# JSON Output for AI Agents

tRust provides machine-readable JSON output, designed for integration with AI coding assistants and automated tools.

## Enabling JSON Output

```bash
trustc --output-format=json example.rs
# or
TRUST_JSON_OUTPUT=1 trustc example.rs
```

## Output Structure

```json
{
  "version": "1.0",
  "crate_name": "example",
  "trust_level": "verified",
  "timestamp": "2026-01-05T12:00:00Z",
  "summary": {...},
  "functions": [...],
  "overflow_errors": [...],
  "bounds_errors": [...],
  "effect_errors": [...],
  "temporal_specs": [...],
  "external_contracts": [...],
  "optimization_hints": {...},
  "refinement_types": [...],
  "refinement_mismatches": [...]
}
```

## Function Results

Each verified function has an entry:

```json
{
  "name": "clamp_positive",
  "status": "verified",
  "specs_count": 3,
  "message": null,
  "counterexample": null,
  "location": null,
  "function_hash": "d55772edc99d1e72",
  "spec_hash": "eb1cbc576ab72194",
  "proof_hints": null,
  "tactic": null
}
```

### Status Values

| Status | Meaning |
|--------|---------|
| `"verified"` | All postconditions verified |
| `"disproven"` | At least one postcondition failed |
| `"unknown"` | Solver timeout or complexity |
| `"assumed"` | Trust level is `assumed` |
| `"no_specs"` | Function has no specifications |

### Counterexamples

When status is `"disproven"`:

```json
{
  "name": "should_fail",
  "status": "disproven",
  "specs_count": 2,
  "message": "Postcondition may be violated",
  "counterexample": {
    "inputs": [],
    "description": "Counterexample:\nsat\n(\n  (define-fun _1 () Int\n    1)\n)\n\nKnown facts: (> _1 0)\nGoal: (< _1 0)"
  },
  "location": {"file": "example.rs", "line": 34, "column": 1},
  "function_hash": "c241e2ed30045b4b",
  "spec_hash": "e66c3479f3adeb83",
  "proof_hints": null,
  "tactic": null
}
```

## Summary

```json
{
  "summary": {
    "total_functions": 10,
    "verified": 8,
    "disproven": 1,
    "unknown": 0,
    "no_specs": 1,
    "assumed": 0,
    "overflow_errors": 0,
    "bounds_errors": 0,
    "effect_errors": 0,
    "temporal_specs": 0,
    "temporal_parse_errors": 0,
    "nn_specs": 0,
    "external_contracts": 0,
    "wiring_errors": 0,
    "safe_operations": 2,
    "refinement_types": 0,
    "refinement_mismatches": 0
  }
}
```

## External Contracts

When your code uses contracts from dependencies:

```json
{
  "external_contracts": [
    {
      "crate_name": "mylib",
      "function_name": "sqrt",
      "spec_hash": "abc123...",
      "trust_level": "verified"
    }
  ]
}
```

## Effect Errors

When effect checking finds violations:

```json
{
  "effect_errors": [
    {
      "caller": "invalid_pure_calling_io",
      "callee": "io_function",
      "missing_effects": ["IO"],
      "location": {"file": "example.rs", "line": 88, "column": 5},
      "suggestion": "add #[effects(IO)] to invalid_pure_calling_io or remove the call"
    }
  ]
}
```

## Optimization Hints

Information for potential optimizations:

```json
{
  "optimization_hints": {
    "summary": {
      "safe_overflow_checks": 3,
      "safe_bounds_checks": 2,
      "total_optimizable": 5
    },
    "safe_operations": [
      {
        "kind": "overflow",
        "location": {"file": "example.rs", "line": 10, "column": 8},
        "reason": "proven safe by verification"
      }
    ]
  }
}
```

## Integration Examples

### Python Script

```python
import json
import subprocess

result = subprocess.run(
    ["trustc", "--output-format=json", "src/lib.rs"],
    capture_output=True,
    text=True
)

data = json.loads(result.stdout)

for func in data["functions"]:
    if func["status"] == "disproven":
        print(f"Bug in {func['name']}:")
        print(f"  {func['message']}")
        if func["counterexample"]:
            print(f"  {func['counterexample']['description']}")
```

### AI Agent Integration

```python
import tempfile
import json
import subprocess

def verify_code(code: str) -> dict:
    """Verify Rust code and return structured results."""
    with tempfile.NamedTemporaryFile(suffix=".rs", delete=False) as f:
        f.write(code.encode())
        f.flush()

        result = subprocess.run(
            ["trustc", "--output-format=json", f.name],
            capture_output=True,
            text=True
        )

        return json.loads(result.stdout)

def suggest_fix(verification_result: dict) -> str:
    """Generate fix suggestions from verification results."""
    suggestions = []

    for func in verification_result["functions"]:
        if func["status"] == "disproven":
            if func["counterexample"]:
                ce = func["counterexample"]
                suggestions.append(
                    f"Function {func['name']}: {func['message']}\n"
                    f"  {ce['description']}"
                )

    return "\n".join(suggestions)
```

### CI Integration Example

```bash
#!/bin/bash
# verify_and_check.sh
trustc --output-format=json src/lib.rs > results.json

# Check for failures using jq
DISPROVEN=$(jq '.summary.disproven' results.json)
if [ "$DISPROVEN" -gt 0 ]; then
    echo "Verification failed: $DISPROVEN functions disproven"
    jq '.functions[] | select(.status == "disproven")' results.json
    exit 1
fi
```

## Spec Hashes

Each function includes hashes for tracking changes:

```json
{
  "function_hash": "d55772edc99d1e72",
  "spec_hash": "eb1cbc576ab72194"
}
```

- `function_hash`: Hash of the function body (changes when implementation changes)
- `spec_hash`: Hash of the specifications (changes when contracts change)

Use hashes to:
- Detect specification changes
- Implement incremental verification
- Track contract evolution

## Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All functions verified (verified or assumed) |
| 1 | At least one disproven |
| 2 | At least one unknown (but no disproven) |
| 3 | Compilation error |

## Best Practices

1. **Parse defensively**: Handle missing fields (many can be null)
2. **Cache results**: Use function_hash for caching
3. **Log everything**: Store full JSON for debugging
4. **Monitor trends**: Track verification success over time
5. **Automate fixes**: Generate preconditions from counterexamples

## Next Steps

- [Error Codes](../reference/errors.md) - Understanding error codes in JSON
- [Specification Attributes](../reference/attributes.md) - All available attributes
