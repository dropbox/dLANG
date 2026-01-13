// Auto-VC Bounds Check Test
//
// Tests that the mock parser detects array subscripts (`arr[index]`) and generates
// BoundsCheck auto-VCs that can be proven using:
// - Guard/if path conditions
// - Explicit @_requires preconditions

// Test 1: Bounds check guarded by a guard (should verify)
@_ensures("true")
func safeGetGuarded(_ arr: [Int], _ index: Int) -> Int {
    guard index >= 0 && index < arr.count else { return 0 }
    return arr[index]
}

// Test 2: Bounds check guarded by an if (should verify)
@_ensures("true")
func safeGetIf(_ arr: [Int], _ index: Int) -> Int {
    if index >= 0 && index < arr.count {
        return arr[index]
    } else {
        return 0
    }
}

// Test 3: Bounds check proven by explicit precondition (should verify)
@_requires("index >= 0 && index < arr.count")
@_ensures("true")
func safeGetRequires(_ arr: [Int], _ index: Int) -> Int {
    return arr[index]
}

