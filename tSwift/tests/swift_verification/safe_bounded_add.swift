// Test: Safe bounded addition (should verify)
// The preconditions constrain inputs to prevent overflow

@_requires("a >= 0 && a <= 1000000000")
@_requires("b >= 0 && b <= 1000000000")
func safeAdd(_ a: Int, _ b: Int) -> Int {
    return a + b  // Max result is 2B, well within Int64 range
}
