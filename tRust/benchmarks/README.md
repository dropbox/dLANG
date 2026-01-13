# tRust Verification Benchmarks

Performance benchmarks for tRust verification timing.

## Usage

```bash
./benchmarks/run_benchmarks.sh [iterations] [solver]
```

Default: 5 iterations per benchmark.

Solver options:
- `z3` (default)
- `z4`
- `both` (run z3 and z4 back-to-back)

Examples:
```bash
./benchmarks/run_benchmarks.sh
./benchmarks/run_benchmarks.sh 10
./benchmarks/run_benchmarks.sh 10 z4
./benchmarks/run_benchmarks.sh both --iterations 3
```

## Benchmark Files

| File | Specs | Functions | Description |
|------|-------|-----------|-------------|
| `simple_1spec.rs` | 1 | 1 | Single precondition, trivial logic |
| `simple_3spec.rs` | 3 | 1 | Pre/postconditions with branching |
| `complex_5spec.rs` | 5 | 1 | Multiple constraints on inputs/outputs |
| `complex_multi.rs` | 16 | 5 | Multiple functions, mixed spec counts |

## Sample Results (2026-01-05)

System: Darwin (macOS), tRust 1.92.0-dev, solver=z3

| Benchmark | Avg Time | Min | Max |
|-----------|----------|-----|-----|
| simple_1spec (1 spec, 1 fn) | 0.80 ms | 0.75 ms | 0.87 ms |
| simple_3spec (3 specs, 1 fn) | 12.91 ms | 10.98 ms | 13.78 ms |
| complex_5spec (5 specs, 1 fn) | 11.85 ms | 11.14 ms | 13.33 ms |
| complex_multi (16 specs, 5 fns) | 134.51 ms | 128.30 ms | 138.87 ms |

## Observations

1. **Baseline overhead**: ~0.8ms for minimal verification (1 spec)
2. **Spec complexity**: 3 specs adds ~12ms over baseline
3. **Function count scaling**: 5 functions with 16 total specs = ~135ms
4. **Per-function average**: ~27ms per function in multi-function case

## Profiling Details

Run with `--profile` to get detailed timing breakdown:

```bash
./bin/trustc --profile --no-cache benchmarks/simple_3spec.rs
```

Output includes:
- Total verification time
- Contract registry time
- Spec verification time (per function)
- Overflow/bounds/division checking time

## Notes

- Results exclude compilation time (verification only)
- `--no-cache` ensures fresh verification each run
- Times depend on spec complexity, not just count
- CHC solver invocation adds significant time for conditional logic

## Solver Notes

tRust selects the SMT backend via the `TRUST_SOLVER` environment variable:
- `TRUST_SOLVER=z3` (default)
- `TRUST_SOLVER=z4`

`run_benchmarks.sh` sets this automatically when you pass `z3`, `z4`, or `both`.
