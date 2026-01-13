// Swift source with @_requires/@_ensures verification attributes
// Used to test end-to-end verification pipeline with real swift-frontend

@_requires("x > 0")
@_ensures("result > 0")
func keepPositive(_ x: Int) -> Int {
    return x
}

@_requires("a >= 0")
@_requires("b >= 0")
@_ensures("result >= 0")
func safeAdd(_ a: Int, _ b: Int) -> Int {
    return a + b
}

@_trusted
func unsafeOperation() -> Int {
    // Trusted functions skip verification
    return 42
}
