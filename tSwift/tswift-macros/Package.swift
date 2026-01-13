// swift-tools-version: 5.9
// The swift-tools-version declares the minimum version of Swift required to build this package.

import PackageDescription
import CompilerPluginSupport

let package = Package(
    name: "tSwiftMacros",
    platforms: [.macOS(.v10_15), .iOS(.v13), .tvOS(.v13), .watchOS(.v6), .macCatalyst(.v13)],
    products: [
        .library(
            name: "tSwiftMacros",
            targets: ["tSwiftMacros"]
        ),
        .executable(
            name: "tSwiftMacrosClient",
            targets: ["tSwiftMacrosClient"]
        ),
    ],
    dependencies: [
        .package(url: "https://github.com/apple/swift-syntax.git", from: "509.0.0"),
    ],
    targets: [
        // Macro implementation that performs the source transformation
        .macro(
            name: "tSwiftMacrosPlugin",
            dependencies: [
                .product(name: "SwiftSyntaxMacros", package: "swift-syntax"),
                .product(name: "SwiftCompilerPlugin", package: "swift-syntax"),
            ]
        ),

        // Library that exposes macros as part of its API
        .target(name: "tSwiftMacros", dependencies: ["tSwiftMacrosPlugin"]),

        // Client for testing macros in development
        // Run with: swift run tSwiftMacrosClient
        // This also serves as verification tests since it exercises all macros
        .executableTarget(name: "tSwiftMacrosClient", dependencies: ["tSwiftMacros"]),

        // Note: XCTest-based tests require full Xcode installation.
        // The tSwiftMacrosClient executable serves as the test suite for CI environments.
        // For macro expansion tests, use Xcode or run: swift run tSwiftMacrosClient
    ]
)
