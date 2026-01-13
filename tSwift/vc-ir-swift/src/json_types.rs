//! JSON schema types for Swift verification conditions.
//!
//! These types mirror tSwift's C++ `ConditionExpr` AST and are designed for
//! easy JSON serialization/deserialization.

use serde::{Deserialize, Serialize};

/// A complete verification bundle for a Swift function.
///
/// This contains all the information needed to verify a function:
/// - Function signature (name, parameters, return type)
/// - Source location for error reporting
/// - Manual verification conditions (@requires/@ensures)
/// - Automatic verification conditions (overflow, bounds, etc.)
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct SwiftVcBundle {
    /// Function name
    pub function_name: String,

    /// Source file path
    #[serde(default)]
    pub source_file: String,

    /// Source line number
    #[serde(default)]
    pub source_line: u32,

    /// Source column number
    #[serde(default)]
    pub source_column: u32,

    /// Function parameters
    #[serde(default)]
    pub parameters: Vec<SwiftParam>,

    /// Return type (optional for Void functions)
    #[serde(default)]
    pub return_type: Option<SwiftType>,

    /// Preconditions from @requires (as parsed expressions)
    #[serde(default)]
    pub requires: Vec<SwiftExpr>,

    /// Postconditions from @ensures (as parsed expressions)
    #[serde(default)]
    pub ensures: Vec<SwiftExpr>,

    /// Loop invariants from @invariant (as parsed expressions)
    #[serde(default)]
    pub invariants: Vec<SwiftExpr>,

    /// Preconditions as strings (alternative to `requires`)
    ///
    /// Condition strings like "x > 0" that get parsed into `SwiftExpr`.
    /// Use `resolve_condition_strings()` to parse these into `requires`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub requires_str: Vec<String>,

    /// Postconditions as strings (alternative to `ensures`)
    ///
    /// Condition strings like "result >= x" that get parsed into `SwiftExpr`.
    /// Use `resolve_condition_strings()` to parse these into `ensures`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub ensures_str: Vec<String>,

    /// Loop invariants as strings (alternative to `invariants`)
    ///
    /// Condition strings that get parsed into `SwiftExpr`.
    /// Use `resolve_condition_strings()` to parse these into `invariants`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub invariants_str: Vec<String>,

    /// Automatic verification conditions (overflow, bounds, nil check, etc.)
    #[serde(default)]
    pub auto_vcs: Vec<SwiftAutoVc>,

    /// Whether the function is marked @trusted
    #[serde(default)]
    pub is_trusted: bool,

    /// Body constraints from symbolic execution.
    ///
    /// These are equality constraints derived from the function body, e.g.,
    /// `result == x * 2` for `return x * 2`. When verifying, these are
    /// conjoined with requires to form the full precondition:
    ///
    /// `(requires AND body_constraints) => ensures`
    ///
    /// This enables verification of specs that depend on function semantics.
    #[serde(default)]
    pub body_constraints: Vec<SwiftExpr>,

    /// Warnings from spec parsing (e.g., undefined variables, malformed syntax).
    ///
    /// These are informational messages about potential issues in specs
    /// that don't prevent verification but may indicate user errors.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub spec_warnings: Vec<String>,
}

impl SwiftVcBundle {
    /// Parse condition strings and merge them into the expression fields.
    ///
    /// This method parses `requires_str`, `ensures_str`, and `invariants_str`
    /// and appends the resulting expressions to `requires`, `ensures`, and
    /// `invariants` respectively.
    ///
    /// # Example
    ///
    /// ```
    /// use vc_ir_swift::SwiftVcBundle;
    ///
    /// let mut bundle = SwiftVcBundle {
    ///     function_name: "test".to_string(),
    ///     requires_str: vec!["x > 0".to_string()],
    ///     ensures_str: vec!["result >= x".to_string()],
    ///     ..Default::default()
    /// };
    ///
    /// bundle.resolve_condition_strings();
    ///
    /// assert_eq!(bundle.requires.len(), 1);
    /// assert_eq!(bundle.ensures.len(), 1);
    /// ```
    pub fn resolve_condition_strings(&mut self) {
        use crate::condition_parser::parse_condition;
        use std::collections::HashMap;

        // Build parameter map from parameters
        let params: HashMap<String, usize> = self
            .parameters
            .iter()
            .map(|p| (p.name.clone(), p.index))
            .collect();

        // Parse requires_str
        for cond_str in self.requires_str.drain(..) {
            let expr = parse_condition(&cond_str, &params);
            self.requires.push(expr);
        }

        // Parse ensures_str
        for cond_str in self.ensures_str.drain(..) {
            let expr = parse_condition(&cond_str, &params);
            self.ensures.push(expr);
        }

        // Parse invariants_str
        for cond_str in self.invariants_str.drain(..) {
            let expr = parse_condition(&cond_str, &params);
            self.invariants.push(expr);
        }
    }
}

/// A function parameter.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SwiftParam {
    /// Parameter name
    pub name: String,

    /// Parameter type
    #[serde(rename = "type")]
    pub param_type: SwiftType,

    /// Parameter index (position in argument list)
    #[serde(default)]
    pub index: usize,
}

/// Swift type representation for verification purposes.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum SwiftType {
    /// Integer types (`Int`, `Int8`, `Int16`, `Int32`, `Int64`, `UInt`, etc.)
    Int {
        /// Whether the type is signed
        #[serde(default = "default_true")]
        signed: bool,
        /// Bit width (8, 16, 32, 64)
        #[serde(default = "default_bits")]
        bits: u32,
    },

    /// Boolean type (Bool)
    Bool,

    /// Floating point types (Float, Double)
    Float {
        /// Bit width (32 for Float, 64 for Double)
        #[serde(default = "default_float_bits")]
        bits: u32,
    },

    /// Optional type (T?)
    Optional {
        /// The wrapped type
        inner: Box<SwiftType>,
    },

    /// Array type (`[T]`)
    Array {
        /// Element type
        element: Box<SwiftType>,
    },

    /// Reference/pointer type (`UnsafePointer`, etc.)
    Pointer {
        /// Whether the pointer is mutable
        #[serde(default)]
        mutable: bool,
        /// Pointee type
        pointee: Box<SwiftType>,
    },

    /// Void type (for functions with no return)
    Void,

    /// Named type (for user-defined types, structs, etc.)
    Named {
        /// Type name
        name: String,
    },
}

const fn default_true() -> bool {
    true
}

const fn default_bits() -> u32 {
    64
}

const fn default_bits_u8() -> u8 {
    64
}

const fn default_float_bits() -> u32 {
    64
}

/// An expression in a verification condition.
///
/// This mirrors tSwift's `ConditionExpr` AST.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum SwiftExpr {
    // === Literals ===
    /// Integer literal: 0, 1, -5, 42
    IntLit { value: i64 },

    /// Boolean literal: true, false
    BoolLit { value: bool },

    /// Nil literal for optionals
    NilLit,

    // === References ===
    /// Parameter reference: x, y, count
    ParamRef {
        name: String,
        /// Parameter index (-1 if unresolved)
        #[serde(default = "default_neg_one")]
        index: i32,
    },

    /// Result reference: result (return value in @ensures)
    ResultRef,

    // === Binary Operators - Arithmetic ===
    /// Addition: +
    Add {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    /// Subtraction: -
    Sub {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    /// Multiplication: *
    Mul {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    /// Division: /
    Div {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    /// Modulo: %
    Mod {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    // === Binary Operators - Comparison ===
    /// Equal: ==
    Eq {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    /// Not equal: !=
    Ne {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    /// Less than: <
    Lt {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    /// Less than or equal: <=
    Le {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    /// Greater than: >
    Gt {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    /// Greater than or equal: >=
    Ge {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    // === Binary Operators - Logical ===
    /// Logical AND: &&
    And {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    /// Logical OR: ||
    Or {
        lhs: Box<SwiftExpr>,
        rhs: Box<SwiftExpr>,
    },

    // === Unary Operators ===
    /// Unary negation: -
    Neg { operand: Box<SwiftExpr> },

    /// Logical NOT: !
    Not { operand: Box<SwiftExpr> },

    // === Advanced (for future use) ===
    /// Old value reference (for postconditions): old(x)
    Old { expr: Box<SwiftExpr> },

    /// Array/collection index access
    Index {
        base: Box<SwiftExpr>,
        index: Box<SwiftExpr>,
    },

    /// Struct/class field access
    Field { base: Box<SwiftExpr>, field: String },

    /// Function call in spec (e.g., abs(x), count(array))
    Call { func: String, args: Vec<SwiftExpr> },

    /// Conditional expression (ternary)
    Ite {
        cond: Box<SwiftExpr>,
        then_expr: Box<SwiftExpr>,
        else_expr: Box<SwiftExpr>,
    },

    /// Universal quantification
    Forall {
        vars: Vec<(String, SwiftType)>,
        body: Box<SwiftExpr>,
    },

    /// Existential quantification
    Exists {
        vars: Vec<(String, SwiftType)>,
        body: Box<SwiftExpr>,
    },

    /// Type literal (for symbolic type representation)
    TypeLit { ty: String },

    /// String literal
    StringLit { value: String },
}

const fn default_neg_one() -> i32 {
    -1
}

/// An automatic verification condition generated by the compiler.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum SwiftAutoVc {
    /// Arithmetic overflow check
    Overflow {
        /// Operation that may overflow (add, sub, mul, neg)
        operation: String,
        /// Operands involved
        operands: Vec<SwiftExpr>,
        /// Human-readable description
        description: String,
        /// Source location
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
        /// Path condition that must be true for this operation to be reachable
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
        /// Whether the operation is signed (true) or unsigned (false). Defaults to true (signed).
        #[serde(default = "default_true")]
        signed: bool,
        /// Number of bits in the integer type (8, 16, 32, 64). Defaults to 64.
        #[serde(default = "default_bits_u8")]
        bits: u8,
    },

    /// Division by zero check
    DivByZero {
        /// The divisor expression
        divisor: SwiftExpr,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
        /// Path condition that must be true for this operation to be reachable
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
    },

    /// Array/pointer bounds check
    BoundsCheck {
        /// Index expression
        index: SwiftExpr,
        /// Length/count expression
        length: SwiftExpr,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
        /// Path condition that must be true for this operation to be reachable
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
    },

    /// Nil/optional unwrap check
    NilCheck {
        /// Expression being unwrapped
        value: SwiftExpr,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
        /// Path condition that must be true for this operation to be reachable
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
    },

    /// Forced type cast check (as!)
    CastCheck {
        /// Expression being cast
        value: SwiftExpr,
        /// Source type name
        source_type: String,
        /// Target type name
        target_type: String,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
        /// Path condition that must be true for this operation to be reachable
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
    },

    /// Condition failure from SIL `cond_fail` instruction
    CondFail {
        /// The condition that must hold to avoid failure
        condition: SwiftExpr,
        /// Message from the `cond_fail` instruction
        message: String,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
        /// Path condition that must be true for this operation to be reachable
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
    },

    /// Function call precondition check
    CallPrecondition {
        /// Name of the function being called
        callee_name: String,
        /// The precondition that must hold (with arguments substituted)
        condition: SwiftExpr,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
        /// Path condition that must be true for this call to be reachable
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
    },

    /// Loop termination check
    Termination {
        /// Loop header block label
        loop_label: String,
        /// The decreasing measure expression (e.g., n - i)
        measure: SwiftExpr,
        /// Initial value of the measure (at loop entry)
        #[serde(default, skip_serializing_if = "Option::is_none")]
        initial_measure: Option<SwiftExpr>,
        /// Value of measure after one iteration (must be strictly less)
        next_measure: SwiftExpr,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
    },

    /// Recursive function termination check
    ///
    /// Verifies that recursive function calls terminate by checking that
    /// a parameter (the measure) decreases on each recursive call and
    /// that there's a base case where recursion stops.
    RecursiveTermination {
        /// Function name being analyzed
        function_name: String,
        /// Name of the parameter that decreases
        decreasing_param: String,
        /// Index of the decreasing parameter (0-based)
        param_index: usize,
        /// The measure expression (typically just the parameter, e.g., n)
        measure: SwiftExpr,
        /// The measure value at the recursive call site (e.g., n - 1)
        recursive_measure: SwiftExpr,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
    },

    /// Mutual recursion termination check
    ///
    /// Verifies that mutually recursive function calls terminate by checking
    /// that a measure decreases across the cycle of calls. For example:
    /// - isEven(n) calls isOdd(n-1)
    /// - isOdd(n) calls isEven(n-1)
    ///
    /// Together, these terminate because n decreases on each call.
    MutualRecursiveTermination {
        /// The cycle of functions involved (e.g., `["isEven", "isOdd"]`)
        function_cycle: Vec<String>,
        /// The measure parameter that decreases across the cycle
        decreasing_param: String,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
    },

    /// Lexicographic termination check for recursive functions with multiple measures
    ///
    /// Verifies that recursive function calls terminate using lexicographic
    /// ordering of multiple parameters. For example:
    /// - ackermann(m, n) calls ackermann(m-1, 1) when n == 0
    /// - ackermann(m, n) calls ackermann(m, n-1) and ackermann(m-1, _)
    ///
    /// Terminates because (m, n) decreases lexicographically: either m decreases,
    /// or m stays the same and n decreases.
    LexicographicTermination {
        /// Function name being analyzed
        function_name: String,
        /// Ordered tuple of parameters in the lexicographic measure (e.g., `["m", "n"]`)
        measure_params: Vec<String>,
        /// For each recursive call site, which parameter decreases
        /// Each entry is (`call_site_description`, `primary_decreasing_param_index`)
        call_site_decreases: Vec<(String, usize)>,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
    },

    /// Lexicographic termination check for mutually recursive functions
    ///
    /// Verifies that mutually recursive function calls terminate using lexicographic
    /// ordering of multiple parameters across the cycle. For example:
    /// - `ack_even(m, n)` calls `ack_odd(m-1, ...)` when m > 0, and `ack_even(m, n-1)` when n > 0
    /// - `ack_odd(m, n)` calls `ack_even(m-1, ...)` when m > 0, and `ack_odd(m, n-1)` when n > 0
    ///
    /// Terminates because (m, n) decreases lexicographically across the cycle: each call
    /// either decreases m, or keeps m the same and decreases n.
    ///
    /// This extends `MutualRecursiveTermination` (single decreasing param) to support
    /// multiple parameters in lexicographic order.
    LexicographicMutualRecursiveTermination {
        /// The cycle of functions involved (e.g., `["ack_even", "ack_odd"]`)
        function_cycle: Vec<String>,
        /// Ordered tuple of parameters in the lexicographic measure (e.g., `["m", "n"]`)
        measure_params: Vec<String>,
        /// Human-readable description
        description: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
    },

    /// State invariant check for `SwiftUI` `@State`/`@StateObject` variables
    ///
    /// Verifies that type invariants hold after state mutations. This is used
    /// for `SwiftUI` state machine verification where `@State` variables have
    /// associated invariants that must hold after any mutation.
    StateInvariant {
        /// Name of the type containing the invariant
        type_name: String,
        /// Name of the property being mutated
        property_name: String,
        /// The invariant expression that must hold
        invariant: SwiftExpr,
        /// Human-readable description
        description: String,
        /// Path condition that must be true for this mutation to occur
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
    },

    /// Type-level invariant check for class/struct definitions
    ///
    /// Verifies that type-level invariants (defined on init or the type itself)
    /// hold after any state mutation within any method of that type. Unlike
    /// `StateInvariant` which applies only to functions with `@_invariant`, `TypeInvariant`
    /// applies to ALL methods that mutate state of a type that has registered invariants.
    ///
    /// Type invariants are extracted from:
    /// - init functions with `@_invariant` attributes (most common)
    /// - explicit type invariant declarations
    TypeInvariant {
        /// Name of the type with the invariant (e.g., "Counter", "`ViewModel`")
        type_name: String,
        /// Name of the property being mutated
        property_name: String,
        /// The invariant expression that must hold
        invariant: SwiftExpr,
        /// Human-readable description
        description: String,
        /// Path condition that must be true for this mutation to occur
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
        /// Method where the mutation occurs
        #[serde(default)]
        mutating_method: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
    },

    /// Cross-method state effect verification
    ///
    /// Verifies that type invariants hold after a method call that may modify state.
    /// This enables cross-method state flow tracking: when method A (with invariants)
    /// calls method B (which modifies state), we generate VCs to verify A's invariants
    /// still hold after B returns.
    ///
    /// This tracks the transitive effects of method calls on type invariants,
    /// closing the gap where direct mutations are verified but indirect mutations
    /// through callee methods were previously unverified.
    MethodCallStateEffect {
        /// Name of the type with the invariant
        type_name: String,
        /// The invariant that must hold after the call
        invariant: SwiftExpr,
        /// Name of the method being called (the callee)
        callee_method: String,
        /// Properties that the callee may modify
        affected_properties: Vec<String>,
        /// Human-readable description
        description: String,
        /// Path condition at the call site
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
        /// Method where the call occurs (the caller)
        #[serde(default)]
        caller_method: String,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
        /// Call chain for transitive effects (empty for direct callee effects).
        /// When non-empty, shows the path: [intermediate1, intermediate2, ..., `ultimate_modifier`]
        /// where `ultimate_modifier` is the method that directly modifies the property.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        call_chain: Vec<String>,
    },

    /// Shift overflow check for shift operations (<<, >>)
    ///
    /// Verifies that shift amount is within valid range [0, `bit_width`).
    /// Shifting by >= `bit_width` is undefined behavior in LLVM and can
    /// cause unpredictable results.
    ShiftOverflow {
        /// Operation: "shl" (shift left), "lshr" (logical shift right), "ashr" (arithmetic shift right)
        operation: String,
        /// The value being shifted
        value: SwiftExpr,
        /// The shift amount expression
        shift_amount: SwiftExpr,
        /// Bit width of the integer type (8, 16, 32, 64)
        #[serde(default = "default_bits_u8")]
        bits: u8,
        /// Human-readable description
        description: String,
        /// Path condition that must be true for this operation to be reachable
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
    },

    /// Unowned reference access safety check
    ///
    /// Verifies that an unowned reference is accessed while the referenced object
    /// is still alive. In Swift, accessing an unowned reference after the object
    /// is deallocated causes a runtime trap (or undefined behavior for unowned(unsafe)).
    ///
    /// Generated when `load_unowned` SIL instruction is encountered. Since static
    /// lifetime tracking is complex, these VCs often return UNKNOWN without additional
    /// user-provided preconditions about reference validity.
    UnownedAccess {
        /// The unowned reference expression being accessed
        reference: SwiftExpr,
        /// Name or description of the reference (for error messages)
        reference_name: String,
        /// Human-readable description
        description: String,
        /// Path condition that must be true for this access to occur
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
    },

    /// Actor isolation crossing check
    ///
    /// Flags when a function call crosses actor boundaries. Swift's actor model
    /// provides compile-time isolation checking, but this VC provides visibility
    /// into where actor boundaries are crossed for:
    /// - FFI verification (ensuring Rust code is safe to call from actor context)
    /// - Auditing actor isolation patterns
    /// - Verifying custom isolation requirements
    ///
    /// Generated when a SIL apply instruction has caller/callee isolation attributes
    /// that indicate a boundary crossing (e.g., nonisolated caller calling actor-isolated callee).
    ActorIsolationCrossing {
        /// Name of the function being called
        callee_name: String,
        /// Caller's isolation context (nonisolated, `actor_instance`, global actor name)
        caller_isolation: String,
        /// Callee's isolation requirement
        callee_isolation: String,
        /// Human-readable description
        description: String,
        /// Path condition at the call site
        #[serde(default, skip_serializing_if = "Option::is_none")]
        path_condition: Option<SwiftExpr>,
        #[serde(default)]
        source_line: u32,
        #[serde(default)]
        source_column: u32,
    },
}

/// Verification result from the backend.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "result")]
pub enum SwiftVerifyResult {
    /// Verification succeeded (condition proven)
    Verified {
        /// Time taken in seconds
        time_seconds: f64,
    },

    /// Verification failed (counterexample found)
    Failed {
        /// Counterexample variable assignments
        counterexample: Vec<(String, String)>,
        /// Time taken in seconds
        time_seconds: f64,
    },

    /// Verification status unknown
    Unknown {
        /// Reason for unknown result
        reason: String,
        /// Time taken in seconds
        time_seconds: f64,
    },

    /// Verification timed out
    Timeout {
        /// Timeout in seconds
        timeout_seconds: f64,
    },

    /// Error during verification
    Error {
        /// Error message
        message: String,
    },
}

/// Complete verification response for a function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SwiftVerifyResponse {
    /// Function name
    pub function_name: String,

    /// Source file path
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub source_file: String,

    /// Source line number where function is defined
    #[serde(default, skip_serializing_if = "is_zero")]
    pub source_line: u32,

    /// Whether the function is marked @_trusted (verification skipped)
    ///
    /// When true, `spec_result` will be `Verified` with `time_seconds`=0.0 but
    /// no actual proof was performed. This allows consumers to distinguish
    /// "proven safe" from "trusted without proof".
    #[serde(default, skip_serializing_if = "is_false")]
    pub is_trusted: bool,

    /// Result of manual spec verification (@requires/@ensures)
    pub spec_result: Option<SwiftVerifyResult>,

    /// Results for each auto-VC
    pub auto_vc_results: Vec<SwiftAutoVcResult>,

    /// Overall status summary
    pub summary: VerificationSummary,

    /// Warnings from spec parsing (e.g., undefined variables, malformed syntax).
    ///
    /// These are informational messages about potential issues in specs
    /// that don't prevent verification but may indicate user errors.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub spec_warnings: Vec<String>,
}

/// Result for a single auto-VC.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SwiftAutoVcResult {
    /// Description of the auto-VC
    pub description: String,

    /// Source file path (empty if unknown)
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub source_file: String,

    /// Source line number (0 if unknown)
    #[serde(default, skip_serializing_if = "is_zero")]
    pub source_line: u32,

    /// Source column number (0 if unknown)
    #[serde(default, skip_serializing_if = "is_zero")]
    pub source_column: u32,

    /// Verification result
    pub result: SwiftVerifyResult,

    /// Suggested fix for failed verifications (empty if none)
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub suggestion: String,

    /// Kani verification result (if --run-kani was used)
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub kani_result: Option<KaniVcResult>,

    /// Call chain for `MethodCallStateEffect` VCs (empty if not applicable or direct modification)
    /// Shows the path from the callee to the ultimate state modifier, e.g., `["mid", "helper"]`
    /// means the callee calls "mid" which calls "helper" which modifies state.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub call_chain: Vec<String>,
}

/// Result of Kani verification for a single VC.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "status")]
pub enum KaniVcResult {
    /// Kani verification succeeded
    Verified {
        /// Harness name in Kani output
        harness_name: String,
        /// Time taken in seconds
        time_seconds: f64,
    },
    /// Kani verification failed (found a counterexample)
    Failed {
        /// Harness name in Kani output
        harness_name: String,
        /// Failure description
        description: String,
        /// Time taken in seconds
        time_seconds: f64,
    },
    /// Kani encountered an error
    Error {
        /// Harness name in Kani output
        harness_name: String,
        /// Error message
        message: String,
    },
    /// VC was not exported to Kani (unsupported construct)
    NotExported {
        /// Reason for not exporting
        reason: String,
    },
}

// serde skip_serializing_if requires &T signature
#[allow(clippy::trivially_copy_pass_by_ref)]
const fn is_zero(v: &u32) -> bool {
    *v == 0
}

// serde skip_serializing_if requires &T signature
#[allow(clippy::trivially_copy_pass_by_ref)]
const fn is_false(v: &bool) -> bool {
    !*v
}

/// Summary of verification results.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct VerificationSummary {
    /// Total number of VCs checked
    pub total_vcs: u32,

    /// Number of VCs verified (proven safe), including trusted VCs for backward compatibility
    pub verified: u32,

    /// Number of VCs treated as trusted (verification skipped)
    ///
    /// When non-zero, `verified` includes these trusted VCs for historical
    /// compatibility. Consumers can compute "proven verified" as
    /// `verified - trusted`.
    #[serde(default, skip_serializing_if = "is_zero")]
    pub trusted: u32,

    /// Number of VCs that failed (counterexample found)
    pub failed: u32,

    /// Number of VCs with unknown result
    pub unknown: u32,

    /// Number of VCs that timed out
    pub timeout: u32,

    /// Total verification time in seconds
    pub total_time_seconds: f64,

    /// Spec verification counts (from @requires/@ensures)
    #[serde(default)]
    pub spec_verified: u32,
    #[serde(default)]
    pub spec_failed: u32,
    #[serde(default)]
    pub spec_unknown: u32,

    /// Auto-VC verification counts
    #[serde(default)]
    pub auto_vc_verified: u32,
    #[serde(default)]
    pub auto_vc_failed: u32,
    #[serde(default)]
    pub auto_vc_unknown: u32,
}

#[cfg(test)]
mod tests {
    use super::*;

    // ==================== SwiftType Tests ====================

    #[test]
    fn test_swift_type_int_serialization() {
        let ty = SwiftType::Int {
            signed: true,
            bits: 32,
        };
        let json = serde_json::to_string(&ty).unwrap();
        assert!(json.contains("\"kind\":\"Int\""));
        assert!(json.contains("\"signed\":true"));
        assert!(json.contains("\"bits\":32"));
    }

    #[test]
    fn test_swift_type_int_defaults() {
        // Test that defaults are applied (signed=true, bits=64)
        let json = r#"{"kind":"Int"}"#;
        let ty: SwiftType = serde_json::from_str(json).unwrap();
        match ty {
            SwiftType::Int { signed, bits } => {
                assert!(signed);
                assert_eq!(bits, 64);
            }
            _ => panic!("Expected Int type"),
        }
    }

    #[test]
    fn test_swift_type_bool() {
        let ty = SwiftType::Bool;
        let json = serde_json::to_string(&ty).unwrap();
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    #[test]
    fn test_swift_type_float_defaults() {
        let json = r#"{"kind":"Float"}"#;
        let ty: SwiftType = serde_json::from_str(json).unwrap();
        match ty {
            SwiftType::Float { bits } => assert_eq!(bits, 64),
            _ => panic!("Expected Float type"),
        }
    }

    #[test]
    fn test_swift_type_optional() {
        let ty = SwiftType::Optional {
            inner: Box::new(SwiftType::Int {
                signed: true,
                bits: 64,
            }),
        };
        let json = serde_json::to_string(&ty).unwrap();
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    #[test]
    fn test_swift_type_array() {
        let ty = SwiftType::Array {
            element: Box::new(SwiftType::Bool),
        };
        let json = serde_json::to_string(&ty).unwrap();
        assert!(json.contains("\"kind\":\"Array\""));
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    #[test]
    fn test_swift_type_pointer() {
        let ty = SwiftType::Pointer {
            mutable: true,
            pointee: Box::new(SwiftType::Int {
                signed: false,
                bits: 8,
            }),
        };
        let json = serde_json::to_string(&ty).unwrap();
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    #[test]
    fn test_swift_type_pointer_default_mutable() {
        let json = r#"{"kind":"Pointer","pointee":{"kind":"Bool"}}"#;
        let ty: SwiftType = serde_json::from_str(json).unwrap();
        match ty {
            SwiftType::Pointer { mutable, pointee } => {
                assert!(!mutable);
                assert!(matches!(*pointee, SwiftType::Bool));
            }
            _ => panic!("Expected Pointer type"),
        }
    }

    #[test]
    fn test_swift_type_void() {
        let ty = SwiftType::Void;
        let json = serde_json::to_string(&ty).unwrap();
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    #[test]
    fn test_swift_type_named() {
        let ty = SwiftType::Named {
            name: "MyCustomType".to_string(),
        };
        let json = serde_json::to_string(&ty).unwrap();
        assert!(json.contains("MyCustomType"));
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    // ==================== SwiftExpr Tests ====================

    #[test]
    fn test_swift_expr_int_lit() {
        let expr = SwiftExpr::IntLit { value: 42 };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_bool_lit() {
        let expr = SwiftExpr::BoolLit { value: true };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_nil_lit() {
        let expr = SwiftExpr::NilLit;
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_param_ref_default_index() {
        let json = r#"{"kind":"ParamRef","name":"x"}"#;
        let parsed: SwiftExpr = serde_json::from_str(json).unwrap();
        match parsed {
            SwiftExpr::ParamRef { name, index } => {
                assert_eq!(name, "x");
                assert_eq!(index, -1); // default
            }
            _ => panic!("Expected ParamRef"),
        }
    }

    #[test]
    fn test_swift_expr_result_ref() {
        let expr = SwiftExpr::ResultRef;
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_binary_operators() {
        let lhs = Box::new(SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        });
        let rhs = Box::new(SwiftExpr::IntLit { value: 1 });

        // Test all binary operators
        let ops = vec![
            SwiftExpr::Add {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Sub {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Mul {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Div {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Mod {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Eq {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Ne {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Lt {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Le {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Gt {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Ge {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::And {
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            SwiftExpr::Or { lhs, rhs },
        ];

        for op in ops {
            let json = serde_json::to_string(&op).unwrap();
            let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
            assert_eq!(op, parsed);
        }
    }

    #[test]
    fn test_swift_expr_unary_operators() {
        let operand = Box::new(SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        });

        let neg = SwiftExpr::Neg {
            operand: operand.clone(),
        };
        let not = SwiftExpr::Not { operand };

        let json_neg = serde_json::to_string(&neg).unwrap();
        let json_not = serde_json::to_string(&not).unwrap();

        let parsed_neg: SwiftExpr = serde_json::from_str(&json_neg).unwrap();
        let parsed_not: SwiftExpr = serde_json::from_str(&json_not).unwrap();

        assert_eq!(neg, parsed_neg);
        assert_eq!(not, parsed_not);
    }

    #[test]
    fn test_swift_expr_old() {
        let expr = SwiftExpr::Old {
            expr: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_index() {
        let expr = SwiftExpr::Index {
            base: Box::new(SwiftExpr::ParamRef {
                name: "arr".to_string(),
                index: 0,
            }),
            index: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_field() {
        let expr = SwiftExpr::Field {
            base: Box::new(SwiftExpr::ParamRef {
                name: "obj".to_string(),
                index: 0,
            }),
            field: "count".to_string(),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_call() {
        let expr = SwiftExpr::Call {
            func: "abs".to_string(),
            args: vec![SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            }],
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_ite() {
        let expr = SwiftExpr::Ite {
            cond: Box::new(SwiftExpr::BoolLit { value: true }),
            then_expr: Box::new(SwiftExpr::IntLit { value: 1 }),
            else_expr: Box::new(SwiftExpr::IntLit { value: 0 }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_forall() {
        let expr = SwiftExpr::Forall {
            vars: vec![(
                "i".to_string(),
                SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: -1,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_exists() {
        let expr = SwiftExpr::Exists {
            vars: vec![("x".to_string(), SwiftType::Bool)],
            body: Box::new(SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: -1,
            }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_type_lit() {
        let expr = SwiftExpr::TypeLit {
            ty: "Int".to_string(),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_swift_expr_string_lit() {
        let expr = SwiftExpr::StringLit {
            value: "hello".to_string(),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    // ==================== SwiftParam Tests ====================

    #[test]
    fn test_swift_param_serialization() {
        let param = SwiftParam {
            name: "count".to_string(),
            param_type: SwiftType::Int {
                signed: true,
                bits: 64,
            },
            index: 0,
        };
        let json = serde_json::to_string(&param).unwrap();
        assert!(json.contains("\"name\":\"count\""));
        let parsed: SwiftParam = serde_json::from_str(&json).unwrap();
        assert_eq!(param.name, parsed.name);
        assert_eq!(param.index, parsed.index);
    }

    #[test]
    fn test_swift_param_default_index() {
        let json = r#"{"name":"x","type":{"kind":"Bool"}}"#;
        let param: SwiftParam = serde_json::from_str(json).unwrap();
        assert_eq!(param.index, 0); // default
    }

    // ==================== SwiftAutoVc Tests ====================

    #[test]
    fn test_swift_auto_vc_overflow() {
        let vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                },
                SwiftExpr::IntLit { value: 1 },
            ],
            description: "x + 1 may overflow".to_string(),
            source_line: 10,
            source_column: 5,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let json = serde_json::to_string(&vc).unwrap();
        let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftAutoVc::Overflow { operation, .. } => assert_eq!(operation, "add"),
            _ => panic!("Expected Overflow"),
        }
    }

    #[test]
    fn test_swift_auto_vc_overflow_defaults_on_deserialize() {
        let json = r#"{"kind":"Overflow","operation":"add","operands":[{"kind":"IntLit","value":1},{"kind":"IntLit","value":2}],"description":"desc"}"#;
        let vc: SwiftAutoVc = serde_json::from_str(json).unwrap();
        match vc {
            SwiftAutoVc::Overflow {
                signed,
                bits,
                source_line,
                source_column,
                path_condition,
                ..
            } => {
                assert!(signed);
                assert_eq!(bits, 64);
                assert_eq!(source_line, 0);
                assert_eq!(source_column, 0);
                assert!(path_condition.is_none());
            }
            _ => panic!("Expected Overflow"),
        }
    }

    #[test]
    fn test_swift_auto_vc_div_by_zero() {
        let vc = SwiftAutoVc::DivByZero {
            divisor: SwiftExpr::ParamRef {
                name: "d".to_string(),
                index: 1,
            },
            description: "d may be zero".to_string(),
            source_line: 5,
            source_column: 3,
            path_condition: Some(SwiftExpr::BoolLit { value: true }),
        };
        let json = serde_json::to_string(&vc).unwrap();
        let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftAutoVc::DivByZero { path_condition, .. } => {
                assert!(path_condition.is_some());
            }
            _ => panic!("Expected DivByZero"),
        }
    }

    #[test]
    fn test_swift_auto_vc_bounds_check() {
        let vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::IntLit { value: 10 },
            description: "index bounds".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: None,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"kind\":\"BoundsCheck\""));
    }

    #[test]
    fn test_swift_auto_vc_nil_check() {
        let vc = SwiftAutoVc::NilCheck {
            value: SwiftExpr::ParamRef {
                name: "opt".to_string(),
                index: 0,
            },
            description: "force unwrap".to_string(),
            source_line: 1,
            source_column: 1,
            path_condition: None,
        };
        let json = serde_json::to_string(&vc).unwrap();
        let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftAutoVc::NilCheck { description, .. } => {
                assert_eq!(description, "force unwrap");
            }
            _ => panic!("Expected NilCheck"),
        }
    }

    #[test]
    fn test_swift_auto_vc_cast_check() {
        let vc = SwiftAutoVc::CastCheck {
            value: SwiftExpr::ParamRef {
                name: "any".to_string(),
                index: 0,
            },
            source_type: "Any".to_string(),
            target_type: "String".to_string(),
            description: "force cast".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: None,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"target_type\":\"String\""));
    }

    #[test]
    fn test_swift_auto_vc_cond_fail() {
        let vc = SwiftAutoVc::CondFail {
            condition: SwiftExpr::BoolLit { value: false },
            message: "assertion failed".to_string(),
            description: "cond_fail".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: None,
        };
        let json = serde_json::to_string(&vc).unwrap();
        let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftAutoVc::CondFail { message, .. } => {
                assert_eq!(message, "assertion failed");
            }
            _ => panic!("Expected CondFail"),
        }
    }

    #[test]
    fn test_swift_auto_vc_call_precondition() {
        let vc = SwiftAutoVc::CallPrecondition {
            callee_name: "divide".to_string(),
            condition: SwiftExpr::Ne {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "y".to_string(),
                    index: 1,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            },
            description: "precondition check".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: None,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"callee_name\":\"divide\""));
    }

    #[test]
    fn test_swift_auto_vc_termination() {
        let vc = SwiftAutoVc::Termination {
            loop_label: "bb1".to_string(),
            measure: SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 0,
            },
            initial_measure: Some(SwiftExpr::IntLit { value: 10 }),
            next_measure: SwiftExpr::Sub {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "n".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            },
            description: "loop terminates".to_string(),
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"loop_label\":\"bb1\""));
    }

    #[test]
    fn test_swift_auto_vc_recursive_termination() {
        let vc = SwiftAutoVc::RecursiveTermination {
            function_name: "factorial".to_string(),
            decreasing_param: "n".to_string(),
            param_index: 0,
            measure: SwiftExpr::ParamRef {
                name: "n".to_string(),
                index: 0,
            },
            recursive_measure: SwiftExpr::Sub {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "n".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            },
            description: "recursive termination".to_string(),
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"function_name\":\"factorial\""));
    }

    #[test]
    fn test_swift_auto_vc_mutual_recursive_termination() {
        let vc = SwiftAutoVc::MutualRecursiveTermination {
            function_cycle: vec!["isEven".to_string(), "isOdd".to_string()],
            decreasing_param: "n".to_string(),
            description: "mutual recursion".to_string(),
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("isEven"));
        assert!(json.contains("isOdd"));
    }

    #[test]
    fn test_swift_auto_vc_lexicographic_termination() {
        let vc = SwiftAutoVc::LexicographicTermination {
            function_name: "ackermann".to_string(),
            measure_params: vec!["m".to_string(), "n".to_string()],
            call_site_decreases: vec![("base case".to_string(), 0)],
            description: "lex termination".to_string(),
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("ackermann"));
    }

    #[test]
    fn test_swift_auto_vc_state_invariant() {
        let vc = SwiftAutoVc::StateInvariant {
            type_name: "Counter".to_string(),
            property_name: "count".to_string(),
            invariant: SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "count".to_string(),
                    index: -1,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            },
            description: "count >= 0".to_string(),
            path_condition: None,
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"type_name\":\"Counter\""));
    }

    #[test]
    fn test_swift_auto_vc_type_invariant() {
        let vc = SwiftAutoVc::TypeInvariant {
            type_name: "ViewModel".to_string(),
            property_name: "items".to_string(),
            invariant: SwiftExpr::BoolLit { value: true },
            description: "type inv".to_string(),
            path_condition: None,
            mutating_method: "addItem".to_string(),
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"mutating_method\":\"addItem\""));
    }

    #[test]
    fn test_swift_auto_vc_method_call_state_effect() {
        let vc = SwiftAutoVc::MethodCallStateEffect {
            type_name: "Store".to_string(),
            invariant: SwiftExpr::BoolLit { value: true },
            callee_method: "update".to_string(),
            affected_properties: vec!["state".to_string()],
            description: "method effect".to_string(),
            path_condition: None,
            caller_method: "process".to_string(),
            source_line: 0,
            source_column: 0,
            call_chain: vec!["intermediate".to_string()],
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"caller_method\":\"process\""));
        assert!(json.contains("intermediate"));
    }

    #[test]
    fn test_swift_auto_vc_shift_overflow() {
        let vc = SwiftAutoVc::ShiftOverflow {
            operation: "shl".to_string(),
            value: SwiftExpr::ParamRef {
                name: "x".to_string(),
                index: 0,
            },
            shift_amount: SwiftExpr::IntLit { value: 3 },
            bits: 32,
            description: "shift overflow".to_string(),
            path_condition: None,
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"operation\":\"shl\""));
    }

    #[test]
    fn test_swift_auto_vc_unowned_access() {
        let vc = SwiftAutoVc::UnownedAccess {
            reference: SwiftExpr::ParamRef {
                name: "ref".to_string(),
                index: 0,
            },
            reference_name: "ref".to_string(),
            description: "unowned access".to_string(),
            path_condition: None,
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"kind\":\"UnownedAccess\""));
    }

    #[test]
    fn test_swift_auto_vc_actor_isolation_crossing() {
        let vc = SwiftAutoVc::ActorIsolationCrossing {
            callee_name: "updateState".to_string(),
            caller_isolation: "nonisolated".to_string(),
            callee_isolation: "MainActor".to_string(),
            description: "actor crossing".to_string(),
            path_condition: None,
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(json.contains("\"callee_isolation\":\"MainActor\""));
    }

    // ==================== SwiftVerifyResult Tests ====================

    #[test]
    fn test_swift_verify_result_verified() {
        let result = SwiftVerifyResult::Verified { time_seconds: 0.5 };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("\"result\":\"Verified\""));
        let parsed: SwiftVerifyResult = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftVerifyResult::Verified { time_seconds } => {
                assert!((time_seconds - 0.5).abs() < 0.001);
            }
            _ => panic!("Expected Verified"),
        }
    }

    #[test]
    fn test_swift_verify_result_failed() {
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![("x".to_string(), "0".to_string())],
            time_seconds: 1.0,
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("\"result\":\"Failed\""));
    }

    #[test]
    fn test_swift_verify_result_unknown() {
        let result = SwiftVerifyResult::Unknown {
            reason: "nonlinear".to_string(),
            time_seconds: 2.0,
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("nonlinear"));
    }

    #[test]
    fn test_swift_verify_result_timeout() {
        let result = SwiftVerifyResult::Timeout {
            timeout_seconds: 30.0,
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("\"result\":\"Timeout\""));
    }

    #[test]
    fn test_swift_verify_result_error() {
        let result = SwiftVerifyResult::Error {
            message: "internal error".to_string(),
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("internal error"));
    }

    // ==================== KaniVcResult Tests ====================

    #[test]
    fn test_kani_vc_result_verified() {
        let result = KaniVcResult::Verified {
            harness_name: "test_harness".to_string(),
            time_seconds: 5.0,
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("\"status\":\"Verified\""));
    }

    #[test]
    fn test_kani_vc_result_failed() {
        let result = KaniVcResult::Failed {
            harness_name: "test_harness".to_string(),
            description: "assertion failed".to_string(),
            time_seconds: 3.0,
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("assertion failed"));
    }

    #[test]
    fn test_kani_vc_result_error() {
        let result = KaniVcResult::Error {
            harness_name: "test_harness".to_string(),
            message: "compilation error".to_string(),
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("compilation error"));
    }

    #[test]
    fn test_kani_vc_result_not_exported() {
        let result = KaniVcResult::NotExported {
            reason: "unsupported".to_string(),
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("\"status\":\"NotExported\""));
    }

    // ==================== SwiftVcBundle Tests ====================

    #[test]
    fn test_swift_vc_bundle_default() {
        let bundle = SwiftVcBundle::default();
        assert!(bundle.function_name.is_empty());
        assert!(bundle.parameters.is_empty());
        assert!(bundle.requires.is_empty());
        assert!(bundle.ensures.is_empty());
        assert!(!bundle.is_trusted);
    }

    #[test]
    fn test_swift_vc_bundle_minimal() {
        let json = r#"{"function_name":"test"}"#;
        let bundle: SwiftVcBundle = serde_json::from_str(json).unwrap();
        assert_eq!(bundle.function_name, "test");
        assert!(bundle.parameters.is_empty());
        assert!(bundle.source_file.is_empty());
        assert_eq!(bundle.source_line, 0);
    }

    #[test]
    fn test_swift_vc_bundle_full() {
        let bundle = SwiftVcBundle {
            function_name: "increment".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 10,
            source_column: 5,
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
                index: 0,
            }],
            return_type: Some(SwiftType::Int {
                signed: true,
                bits: 64,
            }),
            requires: vec![SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }],
            ensures: vec![SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
            }],
            invariants: vec![],
            requires_str: vec![],
            ensures_str: vec![],
            invariants_str: vec![],
            auto_vcs: vec![],
            is_trusted: false,
            body_constraints: vec![],
            spec_warnings: vec![],
        };

        let json = serde_json::to_string(&bundle).unwrap();
        let parsed: SwiftVcBundle = serde_json::from_str(&json).unwrap();

        assert_eq!(bundle.function_name, parsed.function_name);
        assert_eq!(bundle.source_file, parsed.source_file);
        assert_eq!(bundle.parameters.len(), parsed.parameters.len());
        assert_eq!(bundle.requires.len(), parsed.requires.len());
        assert_eq!(bundle.ensures.len(), parsed.ensures.len());
    }

    #[test]
    fn test_swift_vc_bundle_str_fields_not_serialized_when_empty() {
        let bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            ..Default::default()
        };
        let json = serde_json::to_string(&bundle).unwrap();
        // requires_str, ensures_str, invariants_str should be skipped
        assert!(!json.contains("requires_str"));
        assert!(!json.contains("ensures_str"));
        assert!(!json.contains("invariants_str"));
    }

    #[test]
    fn test_swift_vc_bundle_resolve_condition_strings_parses_and_drains() {
        let mut bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
                index: 3,
            }],
            requires_str: vec![" x  >  0 ".to_string()],
            ensures_str: vec!["result >= x".to_string()],
            invariants_str: vec!["x >= 0".to_string()],
            ..Default::default()
        };

        bundle.resolve_condition_strings();

        assert!(bundle.requires_str.is_empty());
        assert!(bundle.ensures_str.is_empty());
        assert!(bundle.invariants_str.is_empty());

        assert_eq!(bundle.requires.len(), 1);
        assert_eq!(bundle.ensures.len(), 1);
        assert_eq!(bundle.invariants.len(), 1);

        match &bundle.requires[0] {
            SwiftExpr::Gt { lhs, rhs } => {
                assert!(matches!(
                    **lhs,
                    SwiftExpr::ParamRef {
                        ref name,
                        index: 3
                    } if name == "x"
                ));
                assert!(matches!(**rhs, SwiftExpr::IntLit { value: 0 }));
            }
            _ => panic!("Expected Gt in requires"),
        }
    }

    #[test]
    fn test_swift_vc_bundle_resolve_condition_strings_appends_to_existing() {
        let mut bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            parameters: vec![SwiftParam {
                name: "x".to_string(),
                param_type: SwiftType::Int {
                    signed: true,
                    bits: 64,
                },
                index: 0,
            }],
            requires: vec![SwiftExpr::BoolLit { value: true }],
            requires_str: vec!["x > 0".to_string()],
            ..Default::default()
        };

        bundle.resolve_condition_strings();

        assert_eq!(bundle.requires.len(), 2);
        assert!(matches!(
            bundle.requires[0],
            SwiftExpr::BoolLit { value: true }
        ));
        assert!(matches!(bundle.requires[1], SwiftExpr::Gt { .. }));
    }

    // ==================== SwiftAutoVcResult Tests ====================

    #[test]
    fn test_swift_auto_vc_result_serialization() {
        let result = SwiftAutoVcResult {
            description: "overflow check".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 5,
            source_column: 10,
            result: SwiftVerifyResult::Verified { time_seconds: 0.1 },
            suggestion: String::new(),
            kani_result: None,
            call_chain: vec![],
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("\"description\":\"overflow check\""));
    }

    #[test]
    fn test_swift_auto_vc_result_with_suggestion() {
        let result = SwiftAutoVcResult {
            description: "bounds check".to_string(),
            source_file: String::new(),
            source_line: 0,
            source_column: 0,
            result: SwiftVerifyResult::Failed {
                counterexample: vec![],
                time_seconds: 0.5,
            },
            suggestion: "Add bounds check before indexing".to_string(),
            kani_result: None,
            call_chain: vec![],
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("Add bounds check"));
    }

    #[test]
    fn test_swift_auto_vc_result_with_call_chain() {
        let result = SwiftAutoVcResult {
            description: "state effect".to_string(),
            source_file: String::new(),
            source_line: 0,
            source_column: 0,
            result: SwiftVerifyResult::Verified { time_seconds: 0.1 },
            suggestion: String::new(),
            kani_result: None,
            call_chain: vec!["mid".to_string(), "helper".to_string()],
        };
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains("mid"));
        assert!(json.contains("helper"));
    }

    // ==================== SwiftVerifyResponse Tests ====================

    #[test]
    fn test_swift_verify_response_serialization() {
        let response = SwiftVerifyResponse {
            function_name: "test".to_string(),
            source_file: "test.swift".to_string(),
            source_line: 1,
            is_trusted: false,
            spec_result: Some(SwiftVerifyResult::Verified { time_seconds: 0.1 }),
            auto_vc_results: vec![],
            summary: VerificationSummary::default(),
            spec_warnings: vec![],
        };
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("\"function_name\":\"test\""));
    }

    #[test]
    fn test_swift_verify_response_trusted() {
        let response = SwiftVerifyResponse {
            function_name: "trusted_fn".to_string(),
            source_file: String::new(),
            source_line: 0,
            is_trusted: true,
            spec_result: Some(SwiftVerifyResult::Verified { time_seconds: 0.0 }),
            auto_vc_results: vec![],
            summary: VerificationSummary::default(),
            spec_warnings: vec![],
        };
        let json = serde_json::to_string(&response).unwrap();
        assert!(json.contains("\"is_trusted\":true"));
    }

    #[test]
    fn test_swift_verify_response_empty_fields_skipped() {
        let response = SwiftVerifyResponse {
            function_name: "test".to_string(),
            source_file: String::new(), // empty
            source_line: 0,             // zero
            is_trusted: false,          // false
            spec_result: None,
            auto_vc_results: vec![],
            summary: VerificationSummary::default(),
            spec_warnings: vec![],
        };
        let json = serde_json::to_string(&response).unwrap();
        // These should be skipped when empty/zero/false
        assert!(!json.contains("\"source_file\""));
        assert!(!json.contains("\"source_line\""));
        assert!(!json.contains("\"is_trusted\""));
    }

    // ==================== VerificationSummary Tests ====================

    #[test]
    fn test_verification_summary_default() {
        let summary = VerificationSummary::default();
        assert_eq!(summary.total_vcs, 0);
        assert_eq!(summary.verified, 0);
        assert_eq!(summary.failed, 0);
        assert_eq!(summary.unknown, 0);
        assert_eq!(summary.timeout, 0);
        assert!((summary.total_time_seconds - 0.0).abs() < 0.001);
    }

    #[test]
    fn test_verification_summary_serialization() {
        let summary = VerificationSummary {
            total_vcs: 10,
            verified: 8,
            trusted: 1,
            failed: 1,
            unknown: 0,
            timeout: 0,
            total_time_seconds: 5.5,
            spec_verified: 2,
            spec_failed: 0,
            spec_unknown: 0,
            auto_vc_verified: 6,
            auto_vc_failed: 1,
            auto_vc_unknown: 0,
        };
        let json = serde_json::to_string(&summary).unwrap();
        let parsed: VerificationSummary = serde_json::from_str(&json).unwrap();
        assert_eq!(summary.total_vcs, parsed.total_vcs);
        assert_eq!(summary.verified, parsed.verified);
        assert_eq!(summary.trusted, parsed.trusted);
    }

    #[test]
    fn test_verification_summary_trusted_skipped_when_zero() {
        let summary = VerificationSummary {
            trusted: 0,
            ..Default::default()
        };
        let json = serde_json::to_string(&summary).unwrap();
        assert!(!json.contains("\"trusted\""));
    }

    // ==================== Edge Cases ====================

    #[test]
    fn test_negative_int_literal() {
        let expr = SwiftExpr::IntLit {
            value: -9_223_372_036_854_775_808,
        }; // i64::MIN
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_empty_string_fields() {
        let param = SwiftParam {
            name: String::new(),
            param_type: SwiftType::Void,
            index: 0,
        };
        let json = serde_json::to_string(&param).unwrap();
        let parsed: SwiftParam = serde_json::from_str(&json).unwrap();
        assert!(parsed.name.is_empty());
    }

    #[test]
    fn test_deeply_nested_expression() {
        // Build: ((((x + 1) + 2) + 3) + 4)
        let mut expr = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        for i in 1..=4 {
            expr = SwiftExpr::Add {
                lhs: Box::new(expr),
                rhs: Box::new(SwiftExpr::IntLit { value: i }),
            };
        }
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_unicode_in_names() {
        let param = SwiftParam {
            name: "名前".to_string(), // Japanese for "name"
            param_type: SwiftType::Int {
                signed: true,
                bits: 64,
            },
            index: 0,
        };
        let json = serde_json::to_string(&param).unwrap();
        let parsed: SwiftParam = serde_json::from_str(&json).unwrap();
        assert_eq!(param.name, parsed.name);
    }

    #[test]
    fn test_special_chars_in_strings() {
        let expr = SwiftExpr::StringLit {
            value: "hello\nworld\t\"quoted\"\\backslash".to_string(),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    // ==================== Default Function Tests ====================

    #[test]
    fn test_default_true_returns_true() {
        assert!(super::default_true());
    }

    #[test]
    fn test_default_bits_returns_64() {
        assert_eq!(super::default_bits(), 64);
    }

    #[test]
    fn test_default_bits_u8_returns_64() {
        assert_eq!(super::default_bits_u8(), 64);
    }

    #[test]
    fn test_default_float_bits_returns_64() {
        assert_eq!(super::default_float_bits(), 64);
    }

    #[test]
    fn test_default_neg_one_returns_neg_one() {
        assert_eq!(super::default_neg_one(), -1);
    }

    #[test]
    fn test_is_zero_true_for_zero() {
        assert!(super::is_zero(&0));
    }

    #[test]
    fn test_is_zero_false_for_nonzero() {
        assert!(!super::is_zero(&1));
        assert!(!super::is_zero(&100));
        assert!(!super::is_zero(&u32::MAX));
    }

    #[test]
    fn test_is_false_true_for_false() {
        assert!(super::is_false(&false));
    }

    #[test]
    fn test_is_false_false_for_true() {
        assert!(!super::is_false(&true));
    }

    // ==================== Nested Type Tests ====================

    #[test]
    fn test_nested_optional_types() {
        // Optional<Optional<Int>>
        let ty = SwiftType::Optional {
            inner: Box::new(SwiftType::Optional {
                inner: Box::new(SwiftType::Int {
                    signed: true,
                    bits: 32,
                }),
            }),
        };
        let json = serde_json::to_string(&ty).unwrap();
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    #[test]
    fn test_array_of_optionals() {
        // [Int?]
        let ty = SwiftType::Array {
            element: Box::new(SwiftType::Optional {
                inner: Box::new(SwiftType::Int {
                    signed: true,
                    bits: 64,
                }),
            }),
        };
        let json = serde_json::to_string(&ty).unwrap();
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    #[test]
    fn test_optional_array() {
        // [Int]?
        let ty = SwiftType::Optional {
            inner: Box::new(SwiftType::Array {
                element: Box::new(SwiftType::Int {
                    signed: true,
                    bits: 64,
                }),
            }),
        };
        let json = serde_json::to_string(&ty).unwrap();
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    #[test]
    fn test_pointer_to_pointer() {
        // UnsafePointer<UnsafeMutablePointer<Int>>
        let ty = SwiftType::Pointer {
            mutable: false,
            pointee: Box::new(SwiftType::Pointer {
                mutable: true,
                pointee: Box::new(SwiftType::Int {
                    signed: true,
                    bits: 64,
                }),
            }),
        };
        let json = serde_json::to_string(&ty).unwrap();
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    #[test]
    fn test_array_of_named_types() {
        let ty = SwiftType::Array {
            element: Box::new(SwiftType::Named {
                name: "MyStruct".to_string(),
            }),
        };
        let json = serde_json::to_string(&ty).unwrap();
        let parsed: SwiftType = serde_json::from_str(&json).unwrap();
        assert_eq!(ty, parsed);
    }

    // ==================== SwiftExpr Additional Tests ====================

    #[test]
    fn test_call_with_no_args() {
        let expr = SwiftExpr::Call {
            func: "random".to_string(),
            args: vec![],
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_call_with_multiple_args() {
        let expr = SwiftExpr::Call {
            func: "max".to_string(),
            args: vec![
                SwiftExpr::IntLit { value: 1 },
                SwiftExpr::IntLit { value: 2 },
                SwiftExpr::IntLit { value: 3 },
            ],
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_forall_with_multiple_vars() {
        let expr = SwiftExpr::Forall {
            vars: vec![
                (
                    "i".to_string(),
                    SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
                (
                    "j".to_string(),
                    SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
            ],
            body: Box::new(SwiftExpr::Le {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: -1,
                }),
                rhs: Box::new(SwiftExpr::ParamRef {
                    name: "j".to_string(),
                    index: -1,
                }),
            }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_exists_with_bool_type() {
        let expr = SwiftExpr::Exists {
            vars: vec![("flag".to_string(), SwiftType::Bool)],
            body: Box::new(SwiftExpr::ParamRef {
                name: "flag".to_string(),
                index: -1,
            }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_nested_index_access() {
        // arr[i][j]
        let expr = SwiftExpr::Index {
            base: Box::new(SwiftExpr::Index {
                base: Box::new(SwiftExpr::ParamRef {
                    name: "arr".to_string(),
                    index: 0,
                }),
                index: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: 1,
                }),
            }),
            index: Box::new(SwiftExpr::ParamRef {
                name: "j".to_string(),
                index: 2,
            }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_chained_field_access() {
        // obj.a.b.c
        let expr = SwiftExpr::Field {
            base: Box::new(SwiftExpr::Field {
                base: Box::new(SwiftExpr::Field {
                    base: Box::new(SwiftExpr::ParamRef {
                        name: "obj".to_string(),
                        index: 0,
                    }),
                    field: "a".to_string(),
                }),
                field: "b".to_string(),
            }),
            field: "c".to_string(),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_old_with_complex_expr() {
        // old(x + 1)
        let expr = SwiftExpr::Old {
            expr: Box::new(SwiftExpr::Add {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "x".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_nested_ite() {
        // cond1 ? (cond2 ? 1 : 2) : 3
        let expr = SwiftExpr::Ite {
            cond: Box::new(SwiftExpr::BoolLit { value: true }),
            then_expr: Box::new(SwiftExpr::Ite {
                cond: Box::new(SwiftExpr::BoolLit { value: false }),
                then_expr: Box::new(SwiftExpr::IntLit { value: 1 }),
                else_expr: Box::new(SwiftExpr::IntLit { value: 2 }),
            }),
            else_expr: Box::new(SwiftExpr::IntLit { value: 3 }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_double_negation() {
        // !!x
        let expr = SwiftExpr::Not {
            operand: Box::new(SwiftExpr::Not {
                operand: Box::new(SwiftExpr::BoolLit { value: true }),
            }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_double_neg_arithmetic() {
        // --x
        let expr = SwiftExpr::Neg {
            operand: Box::new(SwiftExpr::Neg {
                operand: Box::new(SwiftExpr::IntLit { value: 5 }),
            }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_complex_boolean_expr() {
        // (x > 0 && y < 10) || z == 0
        let expr = SwiftExpr::Or {
            lhs: Box::new(SwiftExpr::And {
                lhs: Box::new(SwiftExpr::Gt {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
                }),
                rhs: Box::new(SwiftExpr::Lt {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "y".to_string(),
                        index: 1,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 10 }),
                }),
            }),
            rhs: Box::new(SwiftExpr::Eq {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "z".to_string(),
                    index: 2,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    // ==================== SwiftAutoVc Additional Tests ====================

    #[test]
    fn test_overflow_with_path_condition() {
        let vc = SwiftAutoVc::Overflow {
            operation: "mul".to_string(),
            operands: vec![
                SwiftExpr::ParamRef {
                    name: "a".to_string(),
                    index: 0,
                },
                SwiftExpr::ParamRef {
                    name: "b".to_string(),
                    index: 1,
                },
            ],
            description: "a * b may overflow".to_string(),
            source_line: 5,
            source_column: 10,
            path_condition: Some(SwiftExpr::Gt {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "a".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
            signed: false,
            bits: 32,
        };
        let json = serde_json::to_string(&vc).unwrap();
        let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftAutoVc::Overflow {
                signed,
                bits,
                path_condition,
                ..
            } => {
                assert!(!signed);
                assert_eq!(bits, 32);
                assert!(path_condition.is_some());
            }
            _ => panic!("Expected Overflow"),
        }
    }

    #[test]
    fn test_bounds_check_with_path_condition() {
        let vc = SwiftAutoVc::BoundsCheck {
            index: SwiftExpr::ParamRef {
                name: "i".to_string(),
                index: 0,
            },
            length: SwiftExpr::Call {
                func: "count".to_string(),
                args: vec![SwiftExpr::ParamRef {
                    name: "arr".to_string(),
                    index: 1,
                }],
            },
            description: "array access".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: Some(SwiftExpr::Ge {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "i".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 0 }),
            }),
        };
        let json = serde_json::to_string(&vc).unwrap();
        let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftAutoVc::BoundsCheck { path_condition, .. } => {
                assert!(path_condition.is_some());
            }
            _ => panic!("Expected BoundsCheck"),
        }
    }

    #[test]
    fn test_termination_without_initial_measure() {
        let vc = SwiftAutoVc::Termination {
            loop_label: "bb2".to_string(),
            measure: SwiftExpr::ParamRef {
                name: "counter".to_string(),
                index: 0,
            },
            initial_measure: None,
            next_measure: SwiftExpr::Sub {
                lhs: Box::new(SwiftExpr::ParamRef {
                    name: "counter".to_string(),
                    index: 0,
                }),
                rhs: Box::new(SwiftExpr::IntLit { value: 1 }),
            },
            description: "loop terminates".to_string(),
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(!json.contains("initial_measure")); // should be skipped
    }

    #[test]
    fn test_lexicographic_mutual_recursive_termination() {
        let vc = SwiftAutoVc::LexicographicMutualRecursiveTermination {
            function_cycle: vec!["ack_even".to_string(), "ack_odd".to_string()],
            measure_params: vec!["m".to_string(), "n".to_string()],
            description: "lexicographic mutual termination".to_string(),
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftAutoVc::LexicographicMutualRecursiveTermination {
                function_cycle,
                measure_params,
                ..
            } => {
                assert_eq!(function_cycle.len(), 2);
                assert_eq!(measure_params.len(), 2);
            }
            _ => panic!("Expected LexicographicMutualRecursiveTermination"),
        }
    }

    #[test]
    fn test_method_call_state_effect_empty_call_chain() {
        let vc = SwiftAutoVc::MethodCallStateEffect {
            type_name: "Service".to_string(),
            invariant: SwiftExpr::BoolLit { value: true },
            callee_method: "reset".to_string(),
            affected_properties: vec!["state".to_string(), "counter".to_string()],
            description: "reset effect".to_string(),
            path_condition: None,
            caller_method: "handleError".to_string(),
            source_line: 0,
            source_column: 0,
            call_chain: vec![],
        };
        let json = serde_json::to_string(&vc).unwrap();
        assert!(!json.contains("call_chain")); // should be skipped when empty
    }

    #[test]
    fn test_shift_overflow_all_operations() {
        for op in &["shl", "lshr", "ashr"] {
            let vc = SwiftAutoVc::ShiftOverflow {
                operation: (*op).to_string(),
                value: SwiftExpr::IntLit { value: 1 },
                shift_amount: SwiftExpr::IntLit { value: 4 },
                bits: 64,
                description: format!("{op} overflow check"),
                path_condition: None,
                source_line: 0,
                source_column: 0,
            };
            let json = serde_json::to_string(&vc).unwrap();
            assert!(json.contains(op));
        }
    }

    // ==================== SwiftVcBundle Additional Tests ====================

    #[test]
    fn test_bundle_with_body_constraints() {
        let bundle = SwiftVcBundle {
            function_name: "double".to_string(),
            body_constraints: vec![SwiftExpr::Eq {
                lhs: Box::new(SwiftExpr::ResultRef),
                rhs: Box::new(SwiftExpr::Mul {
                    lhs: Box::new(SwiftExpr::ParamRef {
                        name: "x".to_string(),
                        index: 0,
                    }),
                    rhs: Box::new(SwiftExpr::IntLit { value: 2 }),
                }),
            }],
            ..Default::default()
        };
        let json = serde_json::to_string(&bundle).unwrap();
        assert!(json.contains("body_constraints"));
    }

    #[test]
    fn test_bundle_with_auto_vcs() {
        let bundle = SwiftVcBundle {
            function_name: "divide".to_string(),
            auto_vcs: vec![SwiftAutoVc::DivByZero {
                divisor: SwiftExpr::ParamRef {
                    name: "d".to_string(),
                    index: 1,
                },
                description: "division by zero".to_string(),
                source_line: 0,
                source_column: 0,
                path_condition: None,
            }],
            ..Default::default()
        };
        let json = serde_json::to_string(&bundle).unwrap();
        let parsed: SwiftVcBundle = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.auto_vcs.len(), 1);
    }

    #[test]
    fn test_bundle_trusted_flag() {
        let bundle = SwiftVcBundle {
            function_name: "unsafe_op".to_string(),
            is_trusted: true,
            ..Default::default()
        };
        let json = serde_json::to_string(&bundle).unwrap();
        assert!(json.contains("\"is_trusted\":true"));
    }

    #[test]
    fn test_bundle_multiple_parameters() {
        let bundle = SwiftVcBundle {
            function_name: "multiParam".to_string(),
            parameters: vec![
                SwiftParam {
                    name: "a".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "b".to_string(),
                    param_type: SwiftType::Bool,
                    index: 1,
                },
                SwiftParam {
                    name: "c".to_string(),
                    param_type: SwiftType::Float { bits: 32 },
                    index: 2,
                },
            ],
            ..Default::default()
        };
        let json = serde_json::to_string(&bundle).unwrap();
        let parsed: SwiftVcBundle = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.parameters.len(), 3);
    }

    #[test]
    fn test_bundle_resolve_multiple_conditions() {
        let mut bundle = SwiftVcBundle {
            function_name: "test".to_string(),
            parameters: vec![
                SwiftParam {
                    name: "x".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 0,
                },
                SwiftParam {
                    name: "y".to_string(),
                    param_type: SwiftType::Int {
                        signed: true,
                        bits: 64,
                    },
                    index: 1,
                },
            ],
            requires_str: vec!["x > 0".to_string(), "y >= 0".to_string()],
            ensures_str: vec!["result > x".to_string()],
            ..Default::default()
        };

        bundle.resolve_condition_strings();

        assert_eq!(bundle.requires.len(), 2);
        assert_eq!(bundle.ensures.len(), 1);
    }

    // ==================== Empty Collection Tests ====================

    #[test]
    fn test_empty_counterexample() {
        let result = SwiftVerifyResult::Failed {
            counterexample: vec![],
            time_seconds: 0.1,
        };
        let json = serde_json::to_string(&result).unwrap();
        let parsed: SwiftVerifyResult = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftVerifyResult::Failed { counterexample, .. } => {
                assert!(counterexample.is_empty());
            }
            _ => panic!("Expected Failed"),
        }
    }

    #[test]
    fn test_empty_auto_vc_results() {
        let response = SwiftVerifyResponse {
            function_name: "empty".to_string(),
            source_file: String::new(),
            source_line: 0,
            is_trusted: false,
            spec_result: None,
            auto_vc_results: vec![],
            summary: VerificationSummary::default(),
            spec_warnings: vec![],
        };
        let json = serde_json::to_string(&response).unwrap();
        let parsed: SwiftVerifyResponse = serde_json::from_str(&json).unwrap();
        assert!(parsed.auto_vc_results.is_empty());
    }

    #[test]
    fn test_empty_function_cycle() {
        let vc = SwiftAutoVc::MutualRecursiveTermination {
            function_cycle: vec![],
            decreasing_param: "n".to_string(),
            description: "empty cycle".to_string(),
            source_line: 0,
            source_column: 0,
        };
        let json = serde_json::to_string(&vc).unwrap();
        let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftAutoVc::MutualRecursiveTermination { function_cycle, .. } => {
                assert!(function_cycle.is_empty());
            }
            _ => panic!("Expected MutualRecursiveTermination"),
        }
    }

    // ==================== Large Value Tests ====================

    #[test]
    fn test_max_i64_value() {
        let expr = SwiftExpr::IntLit { value: i64::MAX };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_large_source_line() {
        let vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![],
            description: String::new(),
            source_line: u32::MAX,
            source_column: u32::MAX,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let json = serde_json::to_string(&vc).unwrap();
        let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftAutoVc::Overflow {
                source_line,
                source_column,
                ..
            } => {
                assert_eq!(source_line, u32::MAX);
                assert_eq!(source_column, u32::MAX);
            }
            _ => panic!("Expected Overflow"),
        }
    }

    #[test]
    fn test_large_time_seconds() {
        let result = SwiftVerifyResult::Verified {
            time_seconds: f64::MAX,
        };
        let json = serde_json::to_string(&result).unwrap();
        // f64::MAX serializes to a very large number - just verify it doesn't panic
        assert!(!json.is_empty());
    }

    // ==================== Unicode Edge Cases ====================

    #[test]
    fn test_unicode_emoji_in_description() {
        let vc = SwiftAutoVc::Overflow {
            operation: "add".to_string(),
            operands: vec![],
            description: "overflow 🔥 detected".to_string(),
            source_line: 0,
            source_column: 0,
            path_condition: None,
            signed: true,
            bits: 64,
        };
        let json = serde_json::to_string(&vc).unwrap();
        let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
        match parsed {
            SwiftAutoVc::Overflow { description, .. } => {
                assert!(description.contains("🔥"));
            }
            _ => panic!("Expected Overflow"),
        }
    }

    #[test]
    fn test_unicode_combining_chars() {
        let expr = SwiftExpr::StringLit {
            value: "cafe\u{0301}".to_string(), // café with combining acute
        };
        let json = serde_json::to_string(&expr).unwrap();
        let parsed: SwiftExpr = serde_json::from_str(&json).unwrap();
        assert_eq!(expr, parsed);
    }

    #[test]
    fn test_rtl_unicode() {
        let param = SwiftParam {
            name: "مرحبا".to_string(), // Arabic "hello"
            param_type: SwiftType::Int {
                signed: true,
                bits: 64,
            },
            index: 0,
        };
        let json = serde_json::to_string(&param).unwrap();
        let parsed: SwiftParam = serde_json::from_str(&json).unwrap();
        assert_eq!(param.name, parsed.name);
    }

    // ==================== Comparison Operator Symmetry Tests ====================

    #[test]
    fn test_lt_le_symmetry() {
        let x = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let y = SwiftExpr::ParamRef {
            name: "y".to_string(),
            index: 1,
        };

        let lt = SwiftExpr::Lt {
            lhs: Box::new(x.clone()),
            rhs: Box::new(y.clone()),
        };
        let le = SwiftExpr::Le {
            lhs: Box::new(x),
            rhs: Box::new(y),
        };

        let lt_json = serde_json::to_string(&lt).unwrap();
        let le_json = serde_json::to_string(&le).unwrap();

        assert!(lt_json.contains("\"kind\":\"Lt\""));
        assert!(le_json.contains("\"kind\":\"Le\""));
    }

    #[test]
    fn test_gt_ge_symmetry() {
        let x = SwiftExpr::ParamRef {
            name: "x".to_string(),
            index: 0,
        };
        let y = SwiftExpr::ParamRef {
            name: "y".to_string(),
            index: 1,
        };

        let gt = SwiftExpr::Gt {
            lhs: Box::new(x.clone()),
            rhs: Box::new(y.clone()),
        };
        let ge = SwiftExpr::Ge {
            lhs: Box::new(x),
            rhs: Box::new(y),
        };

        let gt_json = serde_json::to_string(&gt).unwrap();
        let ge_json = serde_json::to_string(&ge).unwrap();

        assert!(gt_json.contains("\"kind\":\"Gt\""));
        assert!(ge_json.contains("\"kind\":\"Ge\""));
    }

    #[test]
    fn test_eq_ne_symmetry() {
        let x = SwiftExpr::IntLit { value: 5 };
        let y = SwiftExpr::IntLit { value: 10 };

        let eq = SwiftExpr::Eq {
            lhs: Box::new(x.clone()),
            rhs: Box::new(y.clone()),
        };
        let ne = SwiftExpr::Ne {
            lhs: Box::new(x),
            rhs: Box::new(y),
        };

        let eq_json = serde_json::to_string(&eq).unwrap();
        let ne_json = serde_json::to_string(&ne).unwrap();

        assert!(eq_json.contains("\"kind\":\"Eq\""));
        assert!(ne_json.contains("\"kind\":\"Ne\""));
    }

    // ==================== SwiftType Bit Width Tests ====================

    #[test]
    fn test_int_all_bit_widths() {
        for bits in [8, 16, 32, 64] {
            for signed in [true, false] {
                let ty = SwiftType::Int { signed, bits };
                let json = serde_json::to_string(&ty).unwrap();
                let parsed: SwiftType = serde_json::from_str(&json).unwrap();
                assert_eq!(ty, parsed);
            }
        }
    }

    #[test]
    fn test_float_all_bit_widths() {
        for bits in [32, 64] {
            let ty = SwiftType::Float { bits };
            let json = serde_json::to_string(&ty).unwrap();
            let parsed: SwiftType = serde_json::from_str(&json).unwrap();
            assert_eq!(ty, parsed);
        }
    }

    #[test]
    fn test_overflow_all_bit_widths() {
        for bits in [8u8, 16, 32, 64] {
            let vc = SwiftAutoVc::Overflow {
                operation: "add".to_string(),
                operands: vec![],
                description: String::new(),
                source_line: 0,
                source_column: 0,
                path_condition: None,
                signed: true,
                bits,
            };
            let json = serde_json::to_string(&vc).unwrap();
            let parsed: SwiftAutoVc = serde_json::from_str(&json).unwrap();
            match parsed {
                SwiftAutoVc::Overflow {
                    bits: parsed_bits, ..
                } => {
                    assert_eq!(bits, parsed_bits);
                }
                _ => panic!("Expected Overflow"),
            }
        }
    }

    // ==================== JSON Serialization Edge Cases ====================

    #[test]
    fn test_null_in_json_fails() {
        let json = r#"{"kind":"IntLit","value":null}"#;
        let result: Result<SwiftExpr, _> = serde_json::from_str(json);
        assert!(result.is_err());
    }

    #[test]
    fn test_extra_fields_ignored() {
        let json = r#"{"kind":"Bool","extra_field":"ignored"}"#;
        let ty: SwiftType = serde_json::from_str(json).unwrap();
        assert!(matches!(ty, SwiftType::Bool));
    }

    #[test]
    fn test_missing_required_field() {
        let json = r#"{"kind":"Named"}"#; // missing "name" field
        let result: Result<SwiftType, _> = serde_json::from_str(json);
        assert!(result.is_err());
    }

    #[test]
    fn test_wrong_type_for_field() {
        let json = r#"{"kind":"Int","signed":"yes","bits":64}"#; // signed should be bool
        let result: Result<SwiftType, _> = serde_json::from_str(json);
        assert!(result.is_err());
    }
}
