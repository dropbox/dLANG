// main.swift - Example Swift app using verified FFI
//
// This demonstrates calling Rust functions from Swift
// with FFI verification ensuring type and spec compatibility.

import Foundation

print("=== Verified FFI Example ===\n")

// Factorial
print("factorial(5) = \(factorial(5))")
print("factorial(10) = \(factorial(10))")
print("factorial(20) = \(factorial(20))")

print("")

// Safe division
print("safeDivide(100, 7) = \(safeDivide(100, 7))")
print("safeDivide(42, 6) = \(safeDivide(42, 6))")

print("")

// Clamping
print("clamp(50, min: 0, max: 100) = \(clamp(50, min: 0, max: 100))")
print("clamp(-10, min: 0, max: 100) = \(clamp(-10, min: 0, max: 100))")
print("clamp(200, min: 0, max: 100) = \(clamp(200, min: 0, max: 100))")

print("\n=== Done ===")
