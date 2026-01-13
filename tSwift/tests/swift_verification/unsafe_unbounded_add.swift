// Test: Unsafe unbounded addition (should fail)
// No preconditions, so overflow is possible

func unsafeAdd(_ a: Int, _ b: Int) -> Int {
    return a + b  // Can overflow when a + b > Int64.max
}
