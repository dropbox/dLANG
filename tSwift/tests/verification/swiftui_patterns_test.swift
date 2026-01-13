// SwiftUI Pattern Verification Tests
//
// This file tests auto-VC detection for common SwiftUI patterns:
// - State counter overflow
// - Array/ForEach bounds checking
// - Optional unwrap safety
// - Division validation
//
// Run: ./bin/tswift verify tests/verification/swiftui_patterns_test.swift -v

// ==================== Counter State Pattern ====================
// SwiftUI @State var count: Int = 0 pattern

/// Unsafe increment - triggers overflow auto-VC
/// In SwiftUI: count += 1 in Button action
func incrementUnsafe(_ count: inout Int) {
    count += 1  // OVERFLOW VC: count can be Int.max
}

/// Safe increment with bounds check
/// SwiftUI pattern: guard count < Int.max else { return }
func incrementSafe(_ count: inout Int) {
    if count < Int.max {
        count += 1  // Safe: guard ensures no overflow
    }
}

// ==================== Array Access Pattern ====================
// SwiftUI ForEach(items.indices) { i in items[i] } pattern

/// Unsafe array access - triggers bounds check auto-VC
/// In SwiftUI: Text(items[selectedIndex])
func getItemUnsafe(_ items: [String], _ index: Int) -> String {
    return items[index]  // BOUNDS VC: index can be out of range
}

/// Safe array access with guard
/// SwiftUI pattern: if let item = items[safe: index]
func getItemSafe(_ items: [String], _ index: Int) -> String? {
    if index >= 0 && index < items.count {
        return items[index]  // Safe: guard ensures valid index
    }
    return nil
}

// ==================== Optional Unwrap Pattern ====================
// SwiftUI @Binding var data: String? pattern

/// Unsafe force unwrap - triggers nil check auto-VC
/// In SwiftUI: Text(data!) when data might be nil
func unwrapUnsafe(_ value: String?) -> String {
    return value!  // NIL VC: value can be nil
}

/// Safe optional unwrap with guard
/// SwiftUI pattern: if let text = data { Text(text) }
func unwrapSafe(_ value: String?) -> String {
    if let text = value {
        return text
    }
    return "default"  // Safe: nil case handled
}

// ==================== Division Pattern ====================
// SwiftUI computed property: var percentage: Double { completed / total }

/// Unsafe division - triggers div-by-zero auto-VC
func divideUnsafe(_ a: Int, _ b: Int) -> Int {
    return a / b  // DIV-BY-ZERO VC: b can be 0
}

/// Safe division with guard
func divideSafe(_ dividend: Int, _ divisor: Int) -> Int? {
    if divisor != 0 {
        return dividend / divisor  // Safe: guard ensures non-zero
    }
    return nil
}

// ==================== Combined Patterns ====================
// SwiftUI ViewModel with multiple safety concerns

/// Multiple VCs in one function
/// SwiftUI: items[selectedIndex!] where selectedIndex: Int?
func getSelectedItemUnsafe(_ items: [String], _ selectedIndex: Int?) -> String {
    let index = selectedIndex!  // NIL VC
    return items[index]         // BOUNDS VC
}

/// Safe version with proper guards
func getSelectedItemSafe(_ items: [String], _ selectedIndex: Int?) -> String? {
    guard let index = selectedIndex else {
        return nil
    }
    guard index >= 0 && index < items.count else {
        return nil
    }
    return items[index]
}

// ==================== Test Harness ====================

func main() {
    // Test safe operations
    var count = 0
    incrementSafe(&count)

    let items = ["A", "B", "C"]
    _ = getItemSafe(items, 0)

    _ = unwrapSafe("test")
    _ = unwrapSafe(nil)

    _ = divideSafe(10, 2)

    if let item = getSelectedItemSafe(items, 1) {
        print("Selected: \(item)")
    }

    print("SwiftUI pattern verification tests complete")
}
