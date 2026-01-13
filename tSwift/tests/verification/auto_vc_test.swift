// tests/verification/auto_vc_test.swift
//
// Test file for automatic verification condition detection
// Tests overflow, division, and bounds check detection

/// Function that performs addition (should detect overflow VC)
func add(_ a: Int, _ b: Int) -> Int {
    return a + b
}

/// Function that performs division (should detect div-by-zero VC)
func divide(_ a: Int, _ b: Int) -> Int {
    return a / b
}

/// Function that accesses array (should detect bounds check VC)
func getElement(_ arr: [Int], _ index: Int) -> Int {
    return arr[index]
}

/// Function with no safety-critical operations
func identity(_ x: Int) -> Int {
    return x
}
