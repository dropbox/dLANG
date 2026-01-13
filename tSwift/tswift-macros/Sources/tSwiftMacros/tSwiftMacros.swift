// tSwift Verification Macros
//
// These macros annotate Swift code with verification specifications.
// The tSwift compiler uses these annotations to generate verification conditions
// and prove properties about the code.

/// Specifies a precondition that must hold when the function is called.
///
/// The condition is verified at compile time using formal verification.
/// If the compiler cannot prove the precondition is satisfied at all call sites,
/// compilation fails with a counterexample.
///
/// Usage:
/// ```swift
/// @requires("index >= 0 && index < array.count")
/// func safeGet<T>(_ array: [T], at index: Int) -> T {
///     return array[index]
/// }
/// ```
@attached(peer)
public macro requires(_ condition: String) = #externalMacro(
    module: "tSwiftMacrosPlugin",
    type: "RequiresMacro"
)

/// Specifies a postcondition that is guaranteed when the function returns.
///
/// The condition is verified at compile time. If the compiler cannot prove
/// the postcondition always holds, compilation fails with a counterexample.
///
/// Use `result` to refer to the return value.
/// Use `old(expr)` to refer to the value of an expression at function entry.
///
/// Usage:
/// ```swift
/// @ensures("result >= 1 && result <= n")
/// func clampPositive(_ n: Int, _ val: Int) -> Int {
///     if val < 1 { return 1 }
///     else if val > n { return n }
///     else { return val }
/// }
///
/// @ensures("account.balance == old(account.balance) - amount")
/// func withdraw(from account: inout Account, amount: UInt) {
///     account.balance -= amount
/// }
/// ```
@attached(peer)
public macro ensures(_ condition: String) = #externalMacro(
    module: "tSwiftMacrosPlugin",
    type: "EnsuresMacro"
)

/// Specifies an invariant that must hold for a property or type.
///
/// For properties: the invariant must hold after every mutation.
/// For types: the invariant must hold after initialization and every method call.
///
/// Usage:
/// ```swift
/// actor Counter {
///     @invariant("value >= 0")
///     private var value: Int = 0
///
///     func increment() {
///         value += 1  // Verified: maintains invariant
///     }
/// }
/// ```
@attached(peer)
public macro invariant(_ condition: String) = #externalMacro(
    module: "tSwiftMacrosPlugin",
    type: "InvariantMacro"
)

/// Marks code as trusted, skipping verification.
///
/// Use sparingly. Trusted code is assumed correct without proof.
///
/// Can optionally specify which checks to skip:
/// - `.overflow` - Skip integer overflow checks
/// - `.bounds` - Skip array bounds checks
/// - `.nil` - Skip optional unwrap checks
///
/// Usage:
/// ```swift
/// @trusted
/// func legacyCode() -> Int { ... }
///
/// @trusted(.overflow)
/// func intentionalWrapping(_ x: UInt8) -> UInt8 {
///     return x &+ 1  // Wrapping addition, intentional
/// }
/// ```
@attached(peer)
public macro trusted(_ checks: TrustLevel...) = #externalMacro(
    module: "tSwiftMacrosPlugin",
    type: "TrustedMacro"
)

/// Specifies which verification checks to skip for @trusted.
public enum TrustLevel {
    /// Skip integer overflow verification
    case overflow
    /// Skip array bounds verification
    case bounds
    /// Skip optional nil verification
    case `nil`
    /// Skip division by zero verification
    case division
    /// Skip all verification (default for @trusted with no arguments)
    case all
}
