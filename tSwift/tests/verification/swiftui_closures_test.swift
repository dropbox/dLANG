// SwiftUI Closure Pattern Verification Tests
//
// This file tests auto-VC detection for common SwiftUI closure patterns:
// - State class mutation (mimics @State/@ObservableObject)
// - Closure returning closures (factory pattern)
// - Closures with captured values
// - Optional chains in closures
//
// Run: ./bin/tswift verify tests/verification/swiftui_closures_test.swift -v

// ==================== State Class Pattern ====================
// SwiftUI @StateObject/@ObservableObject pattern

class CounterState {
    var count: Int = 0
    var selectedIndex: Int? = nil
}

/// Unsafe increment via state - triggers overflow auto-VC
/// SwiftUI: Button { viewModel.count += 1 }
func buttonActionUnsafe(_ state: CounterState) {
    state.count += 1  // OVERFLOW VC: count can be Int.max
}

/// Safe increment with bounds check
/// SwiftUI pattern: guard count < Int.max else { return }
func buttonActionSafe(_ state: CounterState) {
    if state.count < Int.max {
        state.count += 1  // Safe: guard ensures no overflow
    }
}

// ==================== Closure Returning Value ====================
// SwiftUI computed property pattern

/// Closure that returns unsafe array access
func createItemAccessor(_ items: [String]) -> (Int) -> String {
    return { index in
        return items[index]  // BOUNDS VC: index can be out of range
    }
}

/// Safe closure with bounds check
func createSafeItemAccessor(_ items: [String]) -> (Int) -> String? {
    return { index in
        if index >= 0 && index < items.count {
            return items[index]
        }
        return nil
    }
}

// ==================== State Mutation via Closure Parameter ====================
// Pattern for closures that receive state to mutate

/// Closure type that mutates state
typealias StateUpdater = (CounterState) -> Void

/// Factory for unsafe increment closure
func createIncrementAction() -> StateUpdater {
    return { state in
        state.count += 1  // OVERFLOW VC
    }
}

/// Factory for safe increment closure
func createSafeIncrementAction() -> StateUpdater {
    return { state in
        if state.count < Int.max {
            state.count += 1
        }
    }
}

// ==================== Optional Chain in Closure ====================
// SwiftUI pattern: optional state access

/// Closure with force unwrap - unsafe
func getSelectedItemUnsafe(_ state: CounterState, _ items: [String]) -> String {
    let index = state.selectedIndex!  // NIL VC
    return items[index]               // BOUNDS VC
}

/// Safe closure with guards
func getSelectedItemSafe(_ state: CounterState, _ items: [String]) -> String? {
    guard let index = state.selectedIndex else {
        return nil
    }
    guard index >= 0 && index < items.count else {
        return nil
    }
    return items[index]
}

// ==================== Closure Composition ====================
// SwiftUI pattern: chained view modifiers

/// Compose two operations - both unsafe
func composeOperationsUnsafe(_ x: Int) -> Int {
    let double = { (n: Int) -> Int in n * 2 }  // OVERFLOW VC
    let addTen = { (n: Int) -> Int in n + 10 } // OVERFLOW VC
    return addTen(double(x))
}

/// Safe composition with checks
func composeOperationsSafe(_ x: Int) -> Int? {
    // Check double doesn't overflow
    guard x <= Int.max / 2 && x >= Int.min / 2 else {
        return nil
    }
    let doubled = x * 2

    // Check add doesn't overflow
    guard doubled <= Int.max - 10 else {
        return nil
    }
    return doubled + 10
}

// ==================== Escaping Closure with Capture ====================
// SwiftUI async pattern - closure captures value type

/// Returns closure that captures count value - unsafe
func createCounter(_ initial: Int) -> () -> Int {
    var count = initial
    return {
        count += 1  // OVERFLOW VC: captured count can be Int.max
        return count
    }
}

/// Safe counter factory
func createSafeCounter(_ initial: Int) -> () -> Int {
    var count = initial
    return {
        if count < Int.max {
            count += 1
        }
        return count
    }
}

// ==================== Nested Closure Capture ====================
// Pattern for nested action handlers

/// Outer closure captures items, returns inner closure
func createNestedAccessor(_ items: [String]) -> () -> (Int) -> String {
    return {
        return { index in
            items[index]  // BOUNDS VC: nested closure array access
        }
    }
}

/// Safe nested accessor
func createSafeNestedAccessor(_ items: [String]) -> () -> (Int) -> String? {
    return {
        return { index in
            if index >= 0 && index < items.count {
                return items[index]
            }
            return nil
        }
    }
}

// ==================== Arithmetic in Closure ====================
// SwiftUI computed value pattern

/// Closure performing division - unsafe
func createDivider() -> (Int, Int) -> Int {
    return { a, b in
        a / b  // DIV-BY-ZERO VC: b can be 0
    }
}

/// Safe divider closure
func createSafeDivider() -> (Int, Int) -> Int? {
    return { a, b in
        if b != 0 {
            return a / b
        }
        return nil
    }
}

// ==================== Multiple VCs in Single Closure ====================
// Complex unsafe operation

/// Multiple unsafe operations in closure
func createComplexAction(_ state: CounterState, _ items: [String]) -> () -> String {
    return {
        state.count += 1          // OVERFLOW VC
        let index = state.count
        return items[index]       // BOUNDS VC
    }
}

/// Safe complex action
func createSafeComplexAction(_ state: CounterState, _ items: [String]) -> () -> String? {
    return {
        if state.count < Int.max {
            state.count += 1
        }
        let index = state.count
        if index >= 0 && index < items.count {
            return items[index]
        }
        return nil
    }
}

// ==================== Test Harness ====================

func main() {
    let state = CounterState()
    buttonActionSafe(state)

    let items = ["A", "B", "C"]
    let accessor = createSafeItemAccessor(items)
    _ = accessor(0)

    let incrementAction = createSafeIncrementAction()
    incrementAction(state)

    state.selectedIndex = 0
    _ = getSelectedItemSafe(state, items)

    _ = composeOperationsSafe(5)

    let counter = createSafeCounter(0)
    _ = counter()

    let nestedAccessor = createSafeNestedAccessor(items)
    let innerAccessor = nestedAccessor()
    _ = innerAccessor(0)

    let divider = createSafeDivider()
    _ = divider(10, 2)

    let complexAction = createSafeComplexAction(state, items)
    _ = complexAction()

    print("SwiftUI closure pattern verification tests complete")
}
