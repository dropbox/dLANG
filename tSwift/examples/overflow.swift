// overflow.swift
//
// Demonstrates overflow detection via auto-VCs and Kani bitvector mode.
//
// Run:
//   ./bin/tswiftv verify examples/overflow.swift --run-kani --kani-bitvector --verbose
//
// Expected:
//   - Auto-VC for "arithmetic overflow" fails (overflow is possible for some inputs)
//   - With --run-kani, Kani reports a failing harness with a counterexample

@inline(never)
func overflow_add(_ x: Int) -> Int {
    // Overflow is possible when x == Int.max
    return x + 1
}

// Keep the function referenced to avoid dead stripping in some build modes.
_ = overflow_add(0)

