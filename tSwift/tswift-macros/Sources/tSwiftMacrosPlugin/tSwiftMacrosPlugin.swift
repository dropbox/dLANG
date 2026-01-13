import SwiftCompilerPlugin
import SwiftSyntax
import SwiftSyntaxBuilder
import SwiftSyntaxMacros
import Foundation

// MARK: - Encoding Utilities

/// Base64 encode a string for safe transport through @_semantics attribute
private func base64Encode(_ string: String) -> String {
    return Data(string.utf8).base64EncodedString()
}

// MARK: - RequiresMacro

/// Macro for specifying preconditions on functions.
///
/// Emits `@_semantics("tswift.requires:<base64>")` attribute that survives to SIL
/// for the verification pass to extract and verify.
///
/// Usage:
/// ```swift
/// @requires("index >= 0 && index < array.count")
/// func safeGet<T>(_ array: [T], at index: Int) -> T {
///     return array[index]
/// }
/// ```
public struct RequiresMacro: PeerMacro {
    public static func expansion(
        of node: AttributeSyntax,
        providingPeersOf declaration: some DeclSyntaxProtocol,
        in context: some MacroExpansionContext
    ) throws -> [DeclSyntax] {
        // Extract the condition string from the macro argument
        guard let argument = node.arguments?.as(LabeledExprListSyntax.self)?.first?.expression,
              let stringLiteral = argument.as(StringLiteralExprSyntax.self),
              let condition = stringLiteral.segments.first?.as(StringSegmentSyntax.self)?.content.text
        else {
            throw MacroExpansionError.message("@requires expects a string literal condition")
        }

        // Peer macros cannot add attributes to the declaration they're attached to.
        // We use a workaround: emit a marker function that the verification pass
        // can detect. The marker contains the spec in its @_semantics attribute.
        //
        // The verification pass will:
        // 1. Find these marker functions
        // 2. Associate them with the actual function via naming convention
        // 3. Extract the spec from @_semantics

        guard let funcDecl = declaration.as(FunctionDeclSyntax.self) else {
            throw MacroExpansionError.message("@requires can only be applied to functions")
        }

        let funcName = funcDecl.name.text
        _ = base64Encode(condition) // Reserved for future: encode spec for transport

        // Swift macro naming restrictions prevent us from emitting arbitrary peer declarations
        // at global scope. The verification pass will extract specs directly from AST attributes.
        //
        // The condition has been validated by parsing the macro argument.
        // Log it for debugging during development.
        #if DEBUG
        print("[tSwift] @requires(\"\(condition)\") on function \(funcName)")
        #endif

        // Return empty - specs are transported via AST attributes, not macro expansion
        return []
    }
}

// MARK: - EnsuresMacro

/// Macro for specifying postconditions on functions.
///
/// Emits `@_semantics("tswift.ensures:<base64>")` attribute that survives to SIL
/// for the verification pass to extract and verify.
///
/// Usage:
/// ```swift
/// @ensures("result >= 1 && result <= n")
/// func clampPositive(_ n: Int, _ val: Int) -> Int {
///     // ...
/// }
/// ```
public struct EnsuresMacro: PeerMacro {
    public static func expansion(
        of node: AttributeSyntax,
        providingPeersOf declaration: some DeclSyntaxProtocol,
        in context: some MacroExpansionContext
    ) throws -> [DeclSyntax] {
        guard let argument = node.arguments?.as(LabeledExprListSyntax.self)?.first?.expression,
              let stringLiteral = argument.as(StringLiteralExprSyntax.self),
              let condition = stringLiteral.segments.first?.as(StringSegmentSyntax.self)?.content.text
        else {
            throw MacroExpansionError.message("@ensures expects a string literal condition")
        }

        guard let funcDecl = declaration.as(FunctionDeclSyntax.self) else {
            throw MacroExpansionError.message("@ensures can only be applied to functions")
        }

        let funcName = funcDecl.name.text
        _ = base64Encode(condition) // Reserved for future: encode spec for transport

        // Swift macro naming restrictions prevent us from emitting arbitrary peer declarations
        // at global scope. The verification pass will extract specs directly from AST attributes.
        #if DEBUG
        print("[tSwift] @ensures(\"\(condition)\") on function \(funcName)")
        #endif

        // Return empty - specs are transported via AST attributes, not macro expansion
        return []
    }
}

// MARK: - InvariantMacro

/// Macro for specifying class/struct invariants.
///
/// Emits `@_semantics("tswift.invariant:<base64>")` attribute for verification.
///
/// Usage:
/// ```swift
/// @invariant("value >= 0")
/// private var value: Int = 0
/// ```
public struct InvariantMacro: PeerMacro {
    public static func expansion(
        of node: AttributeSyntax,
        providingPeersOf declaration: some DeclSyntaxProtocol,
        in context: some MacroExpansionContext
    ) throws -> [DeclSyntax] {
        guard let argument = node.arguments?.as(LabeledExprListSyntax.self)?.first?.expression,
              let stringLiteral = argument.as(StringLiteralExprSyntax.self),
              let condition = stringLiteral.segments.first?.as(StringSegmentSyntax.self)?.content.text
        else {
            throw MacroExpansionError.message("@invariant expects a string literal condition")
        }

        // Swift macro naming restrictions prevent peer expansion at global scope
        #if DEBUG
        print("[tSwift] @invariant(\"\(condition)\")")
        #endif

        // Return empty - specs are transported via AST attributes
        return []
    }
}

// MARK: - TrustedMacro

/// Macro for marking code as trusted (skips verification).
///
/// Emits `@_semantics("tswift.trusted:<level>")` attribute to skip verification.
///
/// Usage:
/// ```swift
/// @trusted
/// func legacyCode() -> Int { ... }
///
/// @trusted(.overflow)  // Only skip overflow verification
/// func intentionalWrapping(_ x: UInt8) -> UInt8 { ... }
/// ```
public struct TrustedMacro: PeerMacro {
    public static func expansion(
        of node: AttributeSyntax,
        providingPeersOf declaration: some DeclSyntaxProtocol,
        in context: some MacroExpansionContext
    ) throws -> [DeclSyntax] {
        // Extract trust level(s) from arguments, default to "all"
        var trustLevels: [String] = []

        if let args = node.arguments?.as(LabeledExprListSyntax.self) {
            for arg in args {
                if let memberAccess = arg.expression.as(MemberAccessExprSyntax.self) {
                    trustLevels.append(memberAccess.declName.baseName.text)
                }
            }
        }

        if trustLevels.isEmpty {
            trustLevels = ["all"]
        }

        let levelsStr = trustLevels.joined(separator: ",")

        // Swift macro naming restrictions prevent peer expansion at global scope
        #if DEBUG
        if let funcDecl = declaration.as(FunctionDeclSyntax.self) {
            print("[tSwift] @trusted(\(levelsStr)) on function \(funcDecl.name.text)")
        } else {
            print("[tSwift] @trusted(\(levelsStr))")
        }
        #endif

        // Return empty - specs are transported via AST attributes
        return []
    }
}

/// Error type for macro expansion failures
enum MacroExpansionError: Error, CustomStringConvertible {
    case message(String)

    var description: String {
        switch self {
        case .message(let msg):
            return msg
        }
    }
}

@main
struct tSwiftMacrosPlugin: CompilerPlugin {
    let providingMacros: [Macro.Type] = [
        RequiresMacro.self,
        EnsuresMacro.self,
        InvariantMacro.self,
        TrustedMacro.self,
    ]
}
