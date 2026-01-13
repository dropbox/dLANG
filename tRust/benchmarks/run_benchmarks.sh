#!/bin/bash
# run_benchmarks.sh - Verification timing benchmarks for tRust
#
# Usage:
#   ./benchmarks/run_benchmarks.sh [iterations] [solver]
#   ./benchmarks/run_benchmarks.sh --iterations N --solver {z3|z4|both}
#
#   iterations: Number of times to run each benchmark (default: 5)
#   solver:
#     - z3   (default)
#     - z4
#     - both (run z3 and z4 back-to-back)
#
# Outputs timing statistics for:
# - Simple functions (1 spec)
# - Medium functions (3 specs)
# - Complex functions (5+ specs)
# - Multi-function files

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TRUST_ROOT="$(dirname "$SCRIPT_DIR")"
TRUSTC="$TRUST_ROOT/bin/trustc"

usage() {
    cat <<EOF
Usage: $0 [iterations] [solver]
       $0 --iterations N --solver {z3|z4|both}

Examples:
  $0
  $0 10
  $0 10 z4
  $0 both --iterations 3
EOF
}

ITERATIONS=5
SOLVER_MODE="z3"

while [ $# -gt 0 ]; do
    case "$1" in
        -h|--help)
            usage
            exit 0
            ;;
        --iterations)
            ITERATIONS="${2:?missing value for --iterations}"
            shift 2
            ;;
        --solver)
            SOLVER_MODE="${2:?missing value for --solver}"
            shift 2
            ;;
        *)
            if [[ "$1" =~ ^[0-9]+$ ]]; then
                ITERATIONS="$1"
            else
                SOLVER_MODE="$1"
            fi
            shift
            ;;
    esac
done

case "$SOLVER_MODE" in
    z3|z4)
        SOLVERS=("$SOLVER_MODE")
        ;;
    both|all)
        SOLVERS=("z3" "z4")
        ;;
    *)
        echo "ERROR: unknown solver mode '$SOLVER_MODE' (expected: z3, z4, both)" >&2
        exit 2
        ;;
esac

# Colors for output (disabled if not terminal)
if [ -t 1 ]; then
    GREEN='\033[0;32m'
    YELLOW='\033[1;33m'
    NC='\033[0m'
else
    GREEN=''
    YELLOW=''
    NC=''
fi

echo "=========================================="
echo "tRust Verification Benchmarks"
echo "=========================================="
echo "Date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "Iterations per benchmark: $ITERATIONS"
echo "Solvers: ${SOLVERS[*]}"
echo ""

# Extract time from profiling output and convert to ms
extract_total_time() {
    local output="$1"
    local line
    line=$(echo "$output" | grep "Total verification time:" | head -1)

    # Extract value and unit
    local value unit
    value=$(echo "$line" | sed 's/.*: \([0-9.]*\).*/\1/')

    # Check if microseconds (µs) or milliseconds (ms)
    if echo "$line" | grep -q "µs"; then
        # Convert µs to ms
        echo "scale=3; $value / 1000" | bc
    else
        echo "$value"
    fi
}

# Run a benchmark and collect statistics
run_benchmark() {
    local name="$1"
    local file="$2"
    local solver="$3"
    local times=()

    echo -e "${YELLOW}Running: $name (solver=$solver)${NC}"

    # Verify the file works first
    if ! TRUST_SOLVER="$solver" "$TRUSTC" --no-cache "$file" 2>&1 | grep -q "VERIFIED\\|Verification pass complete"; then
        echo "  ERROR: Benchmark file failed verification"
        return 1
    fi

    for ((i=1; i<=ITERATIONS; i++)); do
        # Clear cache and run with profiling
        local output
        output=$(TRUST_SOLVER="$solver" "$TRUSTC" --profile --no-cache "$file" 2>&1)
        local time_ms
        time_ms=$(extract_total_time "$output")
        if [ -n "$time_ms" ]; then
            times+=("$time_ms")
            printf "  Run %d: %s ms\n" "$i" "$time_ms"
        else
            echo "  Run $i: Failed to extract time"
        fi
    done

    # Calculate statistics
    if [ ${#times[@]} -gt 0 ]; then
        local sum=0
        local min="${times[0]}"
        local max="${times[0]}"

        for t in "${times[@]}"; do
            sum=$(echo "$sum + $t" | bc)
            if (( $(echo "$t < $min" | bc -l) )); then
                min="$t"
            fi
            if (( $(echo "$t > $max" | bc -l) )); then
                max="$t"
            fi
        done

        local avg
        avg=$(echo "scale=3; $sum / ${#times[@]}" | bc)

        echo -e "${GREEN}  Summary: avg=${avg}ms min=${min}ms max=${max}ms${NC}"
        echo ""

        # Return average for comparison
        echo "$avg" > "/tmp/benchmark_${solver}_${name// /_}.avg"
    fi
}

# Run benchmarks
for solver in "${SOLVERS[@]}"; do
    echo "------------------------------------------"
    echo "Benchmark Results (solver=$solver)"
    echo "------------------------------------------"
    echo ""

    run_benchmark "simple_1spec" "$SCRIPT_DIR/simple_1spec.rs" "$solver"
    run_benchmark "simple_3spec" "$SCRIPT_DIR/simple_3spec.rs" "$solver"
    run_benchmark "complex_5spec" "$SCRIPT_DIR/complex_5spec.rs" "$solver"
    run_benchmark "complex_multi" "$SCRIPT_DIR/complex_multi.rs" "$solver"
done

# Summary comparison
echo "=========================================="
echo "Summary Comparison"
echo "=========================================="
echo ""

for solver in "${SOLVERS[@]}"; do
    echo "solver=$solver"
    for bench in simple_1spec simple_3spec complex_5spec complex_multi; do
        if [ -f "/tmp/benchmark_${solver}_${bench}.avg" ]; then
            avg=$(cat "/tmp/benchmark_${solver}_${bench}.avg")
            printf "  %-20s %8s ms (avg)\n" "$bench:" "$avg"
            rm -f "/tmp/benchmark_${solver}_${bench}.avg"
        fi
    done
    echo ""
done

echo ""
echo "Benchmark complete."

# Clean up compiled binaries (from both SCRIPT_DIR and root where compilation happens)
for src in "$SCRIPT_DIR"/*.rs; do
    base=$(basename "${src%.rs}")
    # Clean from benchmarks directory
    if [ -f "$SCRIPT_DIR/$base" ]; then
        rm -f "$SCRIPT_DIR/$base"
    fi
    # Clean from root directory (where trustc outputs by default)
    if [ -f "$base" ]; then
        rm -f "$base"
    fi
done
