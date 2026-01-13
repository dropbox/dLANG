# Understanding Verification Output

tRust provides detailed feedback about verification results. This guide explains how to interpret the output.

## Verification Status

Each function specification gets one of these statuses:

| Status | Meaning |
|--------|---------|
| **PROVEN** | The property was mathematically proven to hold for all valid inputs |
| **DISPROVEN** | A counterexample was found that violates the property |
| **UNKNOWN** | The solver couldn't determine if the property holds (timeout or complexity) |
| **ASSUMED** | The function is in a crate with `trust_level = "assumed"` and was not verified |

## Standard Output Format

The default output looks like:

```console
Verifying function_name...
  requires(precondition): assumed
  ensures(postcondition1): PROVEN
  ensures(postcondition2): DISPROVEN
    Counterexample: x = 42, y = -1

Verification: N/M functions verified
```

### Line-by-Line Breakdown

1. **Function header**: Shows which function is being verified
2. **Preconditions**: Marked as "assumed" (callers must satisfy them)
3. **Postconditions**: Shows PROVEN, DISPROVEN, or UNKNOWN
4. **Counterexamples**: For DISPROVEN, shows input values that violate the property
5. **Summary**: Shows how many functions were fully verified

## JSON Output Mode

For machine-readable output (useful for AI agents and tooling), use JSON mode:

```bash
./bin/trustc --output-format=json example.rs
```

Output:

```json
{
  "file": "example.rs",
  "functions": [
    {
      "name": "clamp_positive",
      "status": "PROVEN",
      "preconditions": [
        {"formula": "n > 0", "status": "assumed"}
      ],
      "postconditions": [
        {"formula": "result >= 1", "status": "PROVEN"},
        {"formula": "result <= n", "status": "PROVEN"}
      ],
      "function_hash": "abc123...",
      "timing_ms": 42
    }
  ],
  "summary": {
    "total": 1,
    "proven": 1,
    "disproven": 0,
    "unknown": 0
  }
}
```

## Verbose Mode

For detailed solver output, use verbose mode:

```bash
./bin/trustc --verify-verbose example.rs
```

This shows:
- The SMT-LIB formula sent to the solver
- Solver configuration
- Intermediate verification steps

## Performance Profiling

To see timing breakdown:

```bash
./bin/trustc --profile example.rs
```

Output:

```console
Profile: example.rs
  Parsing:      12ms
  Type check:   45ms
  MIR gen:      23ms
  VC gen:       67ms
  SMT solving:  234ms
  Total:        381ms
```

## Counterexample Interpretation

When verification fails, tRust shows a counterexample:

```console
ensures(result > 0): DISPROVEN
  Counterexample: x = 0
```

This means: "When `x = 0`, the property `result > 0` does not hold."

### Complex Counterexamples

For functions with multiple parameters or struct fields:

```console
ensures(result.x > 0 && result.y > 0): DISPROVEN
  Counterexample:
    input.x = -5
    input.y = 10
```

The counterexample shows the specific input values that lead to a violation.

## Error Codes

Verification errors have codes starting with E09xx:

| Code | Meaning |
|------|---------|
| E0900 | General verification failure |
| E0901 | Precondition might not be satisfied at call site |
| E0902 | Postcondition could not be proven |
| E0903 | Invariant violation |
| E0904 | Potential overflow |
| E0905 | Potential array bounds violation |

Get detailed explanation with:

```bash
./bin/trustc --explain E0902
```

## Cache Status

When using the verification cache, you'll see cache indicators:

```console
Verifying foo... (cached)
  ensures(result >= 0): PROVEN

Verifying bar... (computing)
  ensures(result < 100): PROVEN
```

To see cache statistics:

```bash
./bin/trustc --cache-stats
```

## Next Steps

Now that you understand the output, learn about writing specifications in [Preconditions and Postconditions](../basic/pre-post.md).
