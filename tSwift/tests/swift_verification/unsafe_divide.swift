// Test: Unsafe division without precondition (should fail)
// No precondition, so division by zero is possible

func unsafeDivide(_ dividend: Int, by divisor: Int) -> Int {
    return dividend / divisor  // Can divide by zero
}
