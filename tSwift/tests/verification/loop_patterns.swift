// Test file for real swiftc SIL loop patterns
// Used to verify loop termination detection on actual compiler output

// Simple while loop with increment
func incrementingWhile(_ n: Int) -> Int {
    var i = 0
    while i < n {
        i += 1
    }
    return i
}

// Simple while loop with decrement
func decrementingWhile(_ n: Int) -> Int {
    var count = n
    while count > 0 {
        count -= 1
    }
    return count
}

// For-in range loop (most common Swift pattern)
func forInRange(_ n: Int) -> Int {
    var sum = 0
    for i in 0..<n {
        sum += i
    }
    return sum
}

// For-in closed range
func forInClosedRange(_ n: Int) -> Int {
    var sum = 0
    for i in 1...n {
        sum += i
    }
    return sum
}

// Nested loops (only outer should be detected)
func nestedLoops(_ rows: Int, _ cols: Int) -> Int {
    var count = 0
    for i in 0..<rows {
        for j in 0..<cols {
            count += 1
        }
    }
    return count
}

// While loop with step > 1
func stepByTwo(_ n: Int) -> Int {
    var i = 0
    while i < n {
        i += 2
    }
    return i
}

// Countdown with repeat-while
func repeatWhileCountdown(_ n: Int) -> Int {
    var count = n
    if count > 0 {
        repeat {
            count -= 1
        } while count > 0
    }
    return count
}

// For-in with stride
func strideLoop(_ n: Int) -> Int {
    var sum = 0
    for i in stride(from: 0, to: n, by: 2) {
        sum += i
    }
    return sum
}
