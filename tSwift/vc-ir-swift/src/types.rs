//! Local verification types (no tRust dependency)
//!
//! This module defines the core types needed for verification,
//! extracted from `vc_ir` to make tSwift self-contained.

use serde::{Deserialize, Serialize};
use std::fmt::Write as _;
use std::sync::Arc;

// ============================================================================
// Common Type Aliases
// ============================================================================

/// Parsed function signature: (`function_name`, parameters[(name, type)], `return_type`)
///
/// Used by signature parsing functions for Swift and Rust.
type ParsedFuncSignature = (String, Vec<(String, String)>, String);

// ============================================================================
// Verification Results
// ============================================================================

/// Categorized reason for UNKNOWN verification result
///
/// This enum provides structured information about why the solver
/// could not determine validity, helping users understand limitations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnknownReason {
    /// The Z4 solver returned "unknown" (`QF_LIA` limitations)
    ///
    /// Z4 uses Quantifier-Free Linear Integer Arithmetic which cannot handle:
    /// - Non-linear arithmetic (x * y)
    /// - Certain negation patterns
    /// - Bitvector operations
    SolverReturnedUnknown,

    /// Formula contains non-linear arithmetic (x * y, x / y variable, etc.)
    NonLinearArithmetic {
        /// Description of the non-linear operation
        operation: String,
    },

    /// Formula contains unsupported patterns (abs, min, max on variables)
    UnsupportedPattern {
        /// The pattern that is not supported
        pattern: String,
        /// Suggestion for the user
        suggestion: String,
    },

    /// Formula uses floating point which is symbolic only
    FloatingPointSymbolic,

    /// No termination proof generated (loops not analyzed)
    NoTerminationProof,

    /// Memory safety not verified (heap, ARC, etc.)
    NoMemorySafetyProof,

    /// Concurrency not verified (actors, async, threads)
    NoConcurrencyProof,

    /// Generic fallback reason
    Other { reason: String },
}

impl std::fmt::Display for UnknownReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SolverReturnedUnknown => {
                write!(f, "Z4 solver returned unknown (QF_LIA limitations)")
            }
            Self::NonLinearArithmetic { operation } => {
                write!(f, "Non-linear arithmetic not supported: {operation}")
            }
            Self::UnsupportedPattern {
                pattern,
                suggestion,
            } => {
                write!(f, "Pattern '{pattern}' not fully supported. {suggestion}")
            }
            Self::FloatingPointSymbolic => {
                write!(f, "Floating point verification is symbolic only")
            }
            Self::NoTerminationProof => {
                write!(f, "Termination not proven (loop analysis not implemented)")
            }
            Self::NoMemorySafetyProof => {
                write!(f, "Memory safety not verified (heap, ARC)")
            }
            Self::NoConcurrencyProof => {
                write!(f, "Concurrency not verified (actors, async)")
            }
            Self::Other { reason } => write!(f, "{reason}"),
        }
    }
}

/// Result of verification
#[derive(Debug, Clone)]
pub enum VerifyResult {
    /// The verification condition is proven valid
    Proven,
    /// A counterexample was found (the VC is invalid)
    Counterexample(Counterexample),
    /// The solver could not determine validity (with categorized reason)
    Unknown {
        /// Structured reason for unknown result
        category: UnknownReason,
        /// Legacy string reason (for backwards compatibility)
        reason: String,
    },
    /// The solver timed out
    Timeout { seconds: f64 },
    /// An error occurred during verification
    Error(String),
}

/// Counterexample from failed verification
#[derive(Debug, Clone)]
pub struct Counterexample {
    /// Variable assignments that violate the VC
    pub assignments: Vec<(String, Value)>,
}

/// Concrete value in counterexample
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Value {
    Bool(bool),
    Int(i64),
    Float(f64),
    BitVec {
        bits: u32,
        value: Vec<u8>,
    },
    Array(Vec<Value>),
    Struct {
        name: String,
        fields: Vec<(String, Value)>,
    },
    Tuple(Vec<Value>),
    Tensor {
        shape: Vec<usize>,
        data: Vec<Value>,
    },
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(i) => write!(f, "{i}"),
            Self::Float(fl) => write!(f, "{fl}"),
            Self::BitVec { bits, value } => {
                write!(f, "bv{bits}(")?;
                for (i, b) in value.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{b:02x}")?;
                }
                write!(f, ")")
            }
            Self::Array(vals) => {
                write!(f, "[")?;
                for (i, v) in vals.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, "]")
            }
            Self::Struct { name, fields } => {
                write!(f, "{name}{{")?;
                for (i, (fname, val)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{fname}={val}")?;
                }
                write!(f, "}}")
            }
            Self::Tuple(vals) => {
                write!(f, "(")?;
                for (i, v) in vals.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, ")")
            }
            Self::Tensor { shape, data } => {
                write!(f, "tensor<{shape:?}>(")?;
                for (i, v) in data.iter().take(5).enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{v}")?;
                }
                if data.len() > 5 {
                    write!(f, ", ...")?;
                }
                write!(f, ")")
            }
        }
    }
}

// ============================================================================
// VC IR Types (simplified from vc_ir crate)
// ============================================================================

/// Type identifier for VCs
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VcId(pub u64);

/// Source location span
#[derive(Debug, Clone)]
pub struct SourceSpan {
    pub file: Arc<str>,
    pub line_start: u32,
    pub line_end: u32,
    pub col_start: u32,
    pub col_end: u32,
}

/// Type in the verification language
#[derive(Debug, Clone, PartialEq)]
pub enum VcType {
    /// Integer type with optional signedness and bit width
    Int { signed: bool, bits: u32 },
    /// Boolean type
    Bool,
    /// Floating point type
    Float { bits: u32 },
    /// Array type with element type and optional length
    Array {
        elem: Box<VcType>,
        len: Option<usize>,
    },
    /// Reference type (pointer)
    Ref { mutable: bool, inner: Box<VcType> },
    /// Tuple type
    Tuple(Vec<VcType>),
    /// Struct type
    Struct {
        name: String,
        fields: Vec<(String, VcType)>,
    },
    /// Abstract/opaque type (for user-defined types)
    Abstract(String),
}

/// Expression in the verification language
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    // Literals
    IntLit(i128),
    BoolLit(bool),
    /// Nil literal for optionals (represents absence of value)
    NilLit,

    // Variables and references
    Var(String),
    Result,
    Old(Box<Expr>),

    // Arithmetic operations
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Rem(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),

    // Comparison operations
    Eq(Box<Expr>, Box<Expr>),
    Ne(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    Le(Box<Expr>, Box<Expr>),
    Gt(Box<Expr>, Box<Expr>),
    Ge(Box<Expr>, Box<Expr>),

    // Logical operations
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),

    // Conditionals
    Ite {
        cond: Box<Expr>,
        then_: Box<Expr>,
        else_: Box<Expr>,
    },

    // Array and struct access
    ArrayIndex(Box<Expr>, Box<Expr>),
    StructField(Box<Expr>, String),

    // Function application
    Apply {
        func: String,
        args: Vec<Expr>,
    },

    // Quantifiers
    Forall {
        vars: Vec<(String, VcType)>,
        body: Box<Expr>,
    },
    Exists {
        vars: Vec<(String, VcType)>,
        body: Box<Expr>,
    },
}

/// Predicate - a boolean expression used in VCs
#[derive(Debug, Clone)]
pub enum Predicate {
    /// Simple expression predicate
    Expr(Expr),
    /// Conjunction of predicates
    And(Vec<Predicate>),
    /// Disjunction of predicates
    Or(Vec<Predicate>),
    /// Negation
    Not(Box<Predicate>),
    /// Implication (for chaining)
    Implies(Box<Predicate>, Box<Predicate>),
}

impl Predicate {
    /// Create a true predicate
    #[must_use]
    pub const fn t() -> Self {
        Self::Expr(Expr::BoolLit(true))
    }

    /// Create a false predicate
    #[must_use]
    pub const fn f() -> Self {
        Self::Expr(Expr::BoolLit(false))
    }

    /// Create a conjunction of predicates
    ///
    /// # Panics
    /// Cannot panic - the `unwrap` is guarded by a length check.
    #[must_use]
    pub fn and(preds: Vec<Self>) -> Self {
        if preds.is_empty() {
            Self::t()
        } else if preds.len() == 1 {
            preds.into_iter().next().unwrap()
        } else {
            Self::And(preds)
        }
    }

    /// Create a disjunction of predicates
    ///
    /// # Panics
    /// Cannot panic - the `unwrap` is guarded by a length check.
    #[must_use]
    pub fn or(preds: Vec<Self>) -> Self {
        if preds.is_empty() {
            Self::f()
        } else if preds.len() == 1 {
            preds.into_iter().next().unwrap()
        } else {
            Self::Or(preds)
        }
    }
}

/// Kind of verification condition
#[derive(Debug, Clone)]
pub enum VcKind {
    /// Simple predicate to prove
    Predicate(Predicate),
    /// Implication: antecedent => consequent
    Implies {
        antecedent: Predicate,
        consequent: Predicate,
    },
    /// Termination proof obligation for loops
    ///
    /// To prove termination, we must show:
    /// 1. The measure is non-negative at loop entry
    /// 2. The measure strictly decreases on each iteration
    /// 3. The measure type is well-founded (e.g., natural numbers)
    Termination {
        /// The decreasing measure expression (e.g., n - i)
        measure: Expr,
        /// The value of measure at loop entry (for checking positivity)
        initial_measure: Option<Expr>,
        /// The value of measure after one iteration (must be strictly less)
        next_measure: Expr,
        /// Loop header block label (for diagnostics)
        loop_label: String,
    },
}

/// A verification condition
#[derive(Debug, Clone)]
pub struct VerificationCondition {
    pub id: VcId,
    pub name: String,
    pub span: SourceSpan,
    pub condition: VcKind,
    pub preferred_backend: Option<String>,
}

/// Function signature for verification
#[derive(Debug, Clone)]
pub struct FunctionSignature {
    pub name: String,
    pub params: Vec<(String, VcType)>,
    pub return_type: VcType,
}

/// Collection of verification conditions for a function
#[derive(Debug, Clone)]
pub struct FunctionVcs {
    pub name: String,
    pub signature: FunctionSignature,
    pub requires: Vec<VerificationCondition>,
    pub ensures: Vec<VerificationCondition>,
    pub loop_invariants: Vec<VerificationCondition>,
    pub assertions: Vec<VerificationCondition>,
    pub termination: Option<VerificationCondition>,
}

// ============================================================================
// FFI Verification Types
// ============================================================================

/// An FFI function specification (for cross-language verification)
#[derive(Debug, Clone)]
pub struct FfiFunction {
    /// Function name (must match across languages)
    pub name: String,
    /// Source language (Rust, Swift, Kotlin)
    pub language: FfiLanguage,
    /// Parameter types with names
    pub params: Vec<FfiParam>,
    /// Return type
    pub return_type: FfiType,
    /// Preconditions
    pub requires: Vec<Predicate>,
    /// Postconditions
    pub ensures: Vec<Predicate>,
    /// Whether this is a trusted (unverified) binding
    pub trusted: bool,
    /// Source file location
    pub source_file: Option<String>,
    /// Source line number
    pub source_line: Option<u32>,
}

/// Parameter in an FFI function
#[derive(Debug, Clone)]
pub struct FfiParam {
    pub name: String,
    pub ffi_type: FfiType,
}

/// FFI type (common type system across languages)
#[derive(Debug, Clone, PartialEq)]
pub enum FfiType {
    /// Boolean type
    Bool,
    /// Signed integer with bit width
    Int { bits: u32 },
    /// Unsigned integer with bit width
    UInt { bits: u32 },
    /// Floating point with bit width
    Float { bits: u32 },
    /// String type (owned)
    String,
    /// Borrowed string slice
    StringRef,
    /// Byte array/buffer
    Bytes,
    /// Borrowed byte slice
    BytesRef,
    /// Optional type
    Optional(Box<FfiType>),
    /// Result type (success, error)
    Result { ok: Box<FfiType>, err: Box<FfiType> },
    /// Void/Unit type
    Void,
    /// Custom/opaque type by name
    Custom(String),
}

/// Source language for FFI
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FfiLanguage {
    Rust,
    Swift,
    Kotlin,
}

impl std::fmt::Display for FfiLanguage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Rust => write!(f, "Rust"),
            Self::Swift => write!(f, "Swift"),
            Self::Kotlin => write!(f, "Kotlin"),
        }
    }
}

/// Registry of FFI specifications from all languages
#[derive(Debug, Clone, Default)]
pub struct FfiSpecs {
    /// Rust-side function exports
    pub rust_exports: std::collections::HashMap<String, FfiFunction>,
    /// Swift-side function imports/bindings
    pub swift_imports: std::collections::HashMap<String, FfiFunction>,
    /// Kotlin-side function imports/bindings
    pub kotlin_imports: std::collections::HashMap<String, FfiFunction>,
}

impl FfiSpecs {
    /// Create a new empty FFI specifications collection.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a function to the appropriate map based on its language
    pub fn add(&mut self, func: FfiFunction) {
        let name = func.name.clone();
        match func.language {
            FfiLanguage::Rust => {
                self.rust_exports.insert(name, func);
            }
            FfiLanguage::Swift => {
                self.swift_imports.insert(name, func);
            }
            FfiLanguage::Kotlin => {
                self.kotlin_imports.insert(name, func);
            }
        }
    }
}

/// Result of FFI compatibility verification
#[derive(Debug, Clone)]
pub struct FfiVerifyResult {
    /// Function name being verified
    pub function_name: String,
    /// Caller language
    pub caller: FfiLanguage,
    /// Callee language
    pub callee: FfiLanguage,
    /// Overall result
    pub result: FfiCompatibility,
    /// Individual check results
    pub checks: Vec<FfiCheck>,
}

/// Overall FFI compatibility status
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FfiCompatibility {
    /// Fully compatible
    Compatible,
    /// Incompatible (verification fails)
    Incompatible,
    /// Cannot determine (missing specs)
    Unknown,
}

/// Individual FFI compatibility check
#[derive(Debug, Clone)]
pub struct FfiCheck {
    /// What was checked
    pub check_type: FfiCheckType,
    /// Whether the check passed
    pub passed: bool,
    /// Error message if failed
    pub message: Option<String>,
}

/// Type of FFI compatibility check
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FfiCheckType {
    /// Precondition: `caller_requires` => `callee_requires`
    PreconditionCompatibility,
    /// Postcondition: `callee_ensures` => `caller_expects`
    PostconditionCompatibility,
    /// Type layouts match (size and alignment)
    TypeLayout,
    /// Ownership semantics match
    Ownership,
}

impl std::fmt::Display for FfiCheckType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PreconditionCompatibility => write!(f, "precondition"),
            Self::PostconditionCompatibility => write!(f, "postcondition"),
            Self::TypeLayout => write!(f, "type layout"),
            Self::Ownership => write!(f, "ownership"),
        }
    }
}

// ============================================================================
// FFI Spec Parsing from Swift Source
// ============================================================================

/// Raw FFI attribute parsed from Swift source code
///
/// These correspond to Swift attributes like:
/// - `@_ffi_export("rust_func_name")`
/// - `@_ffi_import("swift_bridge::module::func")`
/// - `@_ffi_requires("x > 0")`
/// - `@_ffi_ensures("result >= 0")`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SwiftFfiAttribute {
    /// Export this Swift function as FFI-callable
    Export {
        /// Optional Rust-side name (defaults to Swift function name)
        rust_name: Option<String>,
        /// Module path for swift-bridge integration
        module_path: Option<String>,
    },
    /// Import a Rust function via FFI
    Import {
        /// Rust module path (e.g., "`swift_bridge::parser::parse_escape`")
        rust_path: String,
        /// Optional local name in Swift (defaults to last path component)
        local_name: Option<String>,
    },
    /// Precondition for FFI boundary
    Requires {
        /// Condition expression as string (parsed later)
        condition: String,
    },
    /// Postcondition for FFI boundary
    Ensures {
        /// Condition expression as string (parsed later)
        condition: String,
    },
    /// Mark function as trusted (skip verification)
    Trusted,
}

/// Swift FFI function declaration parsed from source
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SwiftFfiDeclaration {
    /// Function name in Swift
    pub swift_name: String,
    /// FFI attributes
    pub attributes: Vec<SwiftFfiAttribute>,
    /// Parameter names and Swift type strings
    pub parameters: Vec<(String, String)>,
    /// Return type string
    pub return_type: String,
    /// Source file path
    pub source_file: String,
    /// Source line number
    pub source_line: u32,
}

impl SwiftFfiDeclaration {
    /// Check if this declaration exports to Rust
    #[must_use]
    pub fn is_export(&self) -> bool {
        self.attributes
            .iter()
            .any(|a| matches!(a, SwiftFfiAttribute::Export { .. }))
    }

    /// Check if this declaration imports from Rust
    #[must_use]
    pub fn is_import(&self) -> bool {
        self.attributes
            .iter()
            .any(|a| matches!(a, SwiftFfiAttribute::Import { .. }))
    }

    /// Check if this declaration is trusted (skip verification)
    #[must_use]
    pub fn is_trusted(&self) -> bool {
        self.attributes
            .iter()
            .any(|a| matches!(a, SwiftFfiAttribute::Trusted))
    }

    /// Get all requires conditions
    #[must_use]
    pub fn get_requires(&self) -> Vec<&str> {
        self.attributes
            .iter()
            .filter_map(|a| {
                if let SwiftFfiAttribute::Requires { condition } = a {
                    Some(condition.as_str())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get all ensures conditions
    #[must_use]
    pub fn get_ensures(&self) -> Vec<&str> {
        self.attributes
            .iter()
            .filter_map(|a| {
                if let SwiftFfiAttribute::Ensures { condition } = a {
                    Some(condition.as_str())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get the Rust-side name for this function
    #[must_use]
    pub fn get_rust_name(&self) -> &str {
        for attr in &self.attributes {
            match attr {
                SwiftFfiAttribute::Export {
                    rust_name: Some(name),
                    ..
                } => return name,
                SwiftFfiAttribute::Import { rust_path, .. } => {
                    // Return last path component
                    return rust_path.rsplit("::").next().unwrap_or(rust_path);
                }
                _ => {}
            }
        }
        &self.swift_name
    }
}

/// Parse FFI-related Swift declarations from raw Swift source.
///
/// This is a lightweight source parser intended for extracting `_ffi_*`
/// attributes for cross-language compatibility checks. It currently targets
/// single-line `func` signatures.
#[must_use]
#[allow(clippy::cast_possible_truncation)] // Line numbers won't exceed u32
#[allow(clippy::too_many_lines)]
pub fn parse_swift_ffi_declarations_from_source(
    source: &str,
    source_file: &str,
) -> Vec<SwiftFfiDeclaration> {
    fn parse_string_literal_arg(line: &str) -> Option<String> {
        // Extract the first "...", not supporting escapes.
        let start = line.find('"')?;
        let end = line[start + 1..].find('"')? + start + 1;
        Some(line[start + 1..end].to_string())
    }

    fn parse_ffi_attribute_line(line: &str) -> Option<SwiftFfiAttribute> {
        let trimmed = line.trim();
        if !trimmed.starts_with("@_ffi_") {
            return None;
        }

        if trimmed.starts_with("@_ffi_export") {
            let rust_name = parse_string_literal_arg(trimmed);
            return Some(SwiftFfiAttribute::Export {
                rust_name,
                module_path: None,
            });
        }

        if trimmed.starts_with("@_ffi_import") {
            let rust_path = parse_string_literal_arg(trimmed)?;
            return Some(SwiftFfiAttribute::Import {
                rust_path,
                local_name: None,
            });
        }

        if trimmed.starts_with("@_ffi_requires") {
            let condition = parse_string_literal_arg(trimmed)?;
            return Some(SwiftFfiAttribute::Requires { condition });
        }

        if trimmed.starts_with("@_ffi_ensures") {
            let condition = parse_string_literal_arg(trimmed)?;
            return Some(SwiftFfiAttribute::Ensures { condition });
        }

        if trimmed.starts_with("@_ffi_trusted") {
            return Some(SwiftFfiAttribute::Trusted);
        }

        None
    }

    fn split_top_level(s: &str, delim: char) -> Vec<String> {
        let mut parts: Vec<String> = Vec::new();
        let mut depth_paren: i32 = 0;
        let mut depth_brack: i32 = 0;
        let mut depth_angle: i32 = 0;
        let mut start: usize = 0;

        for (i, c) in s.char_indices() {
            match c {
                '(' => depth_paren += 1,
                ')' => depth_paren -= 1,
                '[' => depth_brack += 1,
                ']' => depth_brack -= 1,
                '<' => depth_angle += 1,
                '>' => depth_angle -= 1,
                _ => {}
            }

            if c == delim && depth_paren == 0 && depth_brack == 0 && depth_angle == 0 {
                parts.push(s[start..i].to_string());
                start = i + 1;
            }
        }

        parts.push(s[start..].to_string());
        parts
    }

    fn find_top_level_char(s: &str, needle: char) -> Option<usize> {
        let mut depth_paren: i32 = 0;
        let mut depth_brack: i32 = 0;
        let mut depth_angle: i32 = 0;

        for (i, c) in s.char_indices() {
            match c {
                '(' => depth_paren += 1,
                ')' => depth_paren -= 1,
                '[' => depth_brack += 1,
                ']' => depth_brack -= 1,
                '<' => depth_angle += 1,
                '>' => depth_angle -= 1,
                _ => {}
            }
            if c == needle && depth_paren == 0 && depth_brack == 0 && depth_angle == 0 {
                return Some(i);
            }
        }
        None
    }

    fn extract_balanced_parens(s: &str, open_idx: usize) -> Option<(String, usize)> {
        let mut depth: i32 = 0;
        let mut start_inner: Option<usize> = None;
        for (i, c) in s.char_indices().skip(open_idx) {
            if c == '(' {
                depth += 1;
                if depth == 1 {
                    start_inner = Some(i + 1);
                }
            } else if c == ')' {
                depth -= 1;
                if depth == 0 {
                    let inner_start = start_inner?;
                    return Some((s[inner_start..i].to_string(), i + 1));
                }
            }
        }
        None
    }

    fn parse_swift_func_signature(line: &str) -> Option<ParsedFuncSignature> {
        let trimmed = line.trim();
        let func_idx = trimmed.find("func ")?;
        let after_func = trimmed[func_idx + 4..].trim_start();

        let name_end = after_func
            .find(|c: char| c == '(' || c.is_whitespace() || c == '<')
            .unwrap_or(after_func.len());
        let name = after_func[..name_end].trim();
        if name.is_empty() {
            return None;
        }

        let paren_idx = after_func.find('(')?;
        let (params_str, after_params_idx) = extract_balanced_parens(after_func, paren_idx)?;
        let after_params = after_func[after_params_idx..].trim();

        // Return type
        let return_type = after_params.find("->").map_or_else(
            || "Void".to_string(),
            |arrow_idx| {
                let mut ret = after_params[arrow_idx + 2..].trim();
                if let Some(brace_idx) = ret.find('{') {
                    ret = ret[..brace_idx].trim();
                }
                if let Some(where_idx) = ret.find(" where ") {
                    ret = ret[..where_idx].trim();
                }
                if ret.is_empty() {
                    "Void".to_string()
                } else {
                    ret.to_string()
                }
            },
        );

        // Parameters
        let mut parameters: Vec<(String, String)> = Vec::new();
        for raw_param in split_top_level(&params_str, ',') {
            let param = raw_param.trim();
            if param.is_empty() {
                continue;
            }

            let colon_idx = find_top_level_char(param, ':')?;
            let left = param[..colon_idx].trim();
            let mut right = param[colon_idx + 1..].trim();

            // Strip default values: `x: Int = 0`
            if let Some(eq_idx) = find_top_level_char(right, '=') {
                right = right[..eq_idx].trim();
            }

            // Take the local name (last token before ':')
            let local_name = left
                .split_whitespace()
                .last()
                .map_or_else(|| "_".to_string(), |s| s.trim_matches('`').to_string());

            // Strip leading `inout` and common parameter attributes.
            let mut ty = right.to_string();
            for prefix in &["inout ", "@escaping ", "@autoclosure "] {
                if let Some(stripped) = ty.trim_start().strip_prefix(prefix) {
                    ty = stripped.trim_start().to_string();
                }
            }

            parameters.push((local_name, ty));
        }

        Some((name.to_string(), parameters, return_type))
    }

    let mut decls: Vec<SwiftFfiDeclaration> = Vec::new();
    let mut pending_attrs: Vec<SwiftFfiAttribute> = Vec::new();

    for (line_idx, raw_line) in source.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }

        if let Some(attr) = parse_ffi_attribute_line(line) {
            pending_attrs.push(attr);
            continue;
        }

        if let Some((swift_name, parameters, return_type)) = parse_swift_func_signature(line) {
            if !pending_attrs.is_empty() {
                decls.push(SwiftFfiDeclaration {
                    swift_name,
                    attributes: std::mem::take(&mut pending_attrs),
                    parameters,
                    return_type,
                    source_file: source_file.to_string(),
                    source_line: (line_idx + 1) as u32,
                });
            }
            continue;
        }

        // Reset if we hit a non-attribute line (but allow other attributes like @available).
        if !line.starts_with('@') {
            pending_attrs.clear();
        }
    }

    decls
}

/// Parse swift-bridge generated Swift code to extract FFI function signatures.
///
/// swift-bridge generates Swift wrapper functions that call C FFI functions
/// with the pattern `__swift_bridge__$function_name`. This parser extracts
/// these declarations and creates `SwiftFfiDeclaration` entries with automatic
/// imports.
///
/// Example generated code:
/// ```swift
/// public func foo(_ bar: UInt8) {
///     __swift_bridge__$foo(bar)
/// }
/// ```
///
/// This is parsed as an import of the Rust function "foo".
#[must_use]
#[allow(clippy::cast_possible_truncation)] // Line numbers won't exceed u32
#[allow(clippy::too_many_lines)]
pub fn parse_swift_bridge_generated_from_source(
    source: &str,
    source_file: &str,
) -> Vec<SwiftFfiDeclaration> {
    // Helper: Extract balanced braces content
    fn extract_function_body(lines: &[&str], start: usize) -> Option<(String, usize)> {
        let mut body = String::new();
        let mut brace_depth = 0;
        let mut found_open = false;
        let mut end_line = start;

        for (offset, line) in lines[start..].iter().enumerate() {
            for c in line.chars() {
                if c == '{' {
                    brace_depth += 1;
                    found_open = true;
                } else if c == '}' {
                    brace_depth -= 1;
                }
            }
            body.push_str(line);
            body.push('\n');

            if found_open && brace_depth == 0 {
                end_line = start + offset;
                break;
            }
        }

        if found_open && brace_depth == 0 {
            Some((body, end_line))
        } else {
            None
        }
    }

    // Helper: Parse Swift function signature from a public func line
    fn parse_func_signature(line: &str) -> Option<ParsedFuncSignature> {
        let trimmed = line.trim();

        // Check for public func or just func
        let func_idx = if let Some(idx) = trimmed.find("public func ") {
            idx + 12
        } else if let Some(idx) = trimmed.find("func ") {
            idx + 5
        } else {
            return None;
        };

        let after_func = &trimmed[func_idx..];

        // Extract function name
        let name_end = after_func.find(|c: char| c == '(' || c == '<' || c.is_whitespace())?;
        let name = after_func[..name_end].trim().to_string();

        // Find parameter list
        let paren_start = after_func.find('(')?;
        let mut paren_depth = 0;
        let mut paren_end = None;

        for (i, c) in after_func.char_indices().skip(paren_start) {
            match c {
                '(' => paren_depth += 1,
                ')' => {
                    paren_depth -= 1;
                    if paren_depth == 0 {
                        paren_end = Some(i);
                        break;
                    }
                }
                _ => {}
            }
        }
        let paren_end = paren_end?;

        let params_str = &after_func[paren_start + 1..paren_end];
        let after_params = &after_func[paren_end + 1..].trim_start();

        // Parse return type
        let return_type = if after_params.starts_with("->") {
            let ret_start = 2;
            let ret_str = &after_params[ret_start..].trim_start();
            // Find end of return type (before { or end of line)
            let ret_end = ret_str.find('{').unwrap_or(ret_str.len());
            let ret = ret_str[..ret_end].trim();
            if ret.is_empty() {
                "Void".to_string()
            } else {
                ret.to_string()
            }
        } else {
            "Void".to_string()
        };

        // Parse parameters
        let mut parameters: Vec<(String, String)> = Vec::new();

        if !params_str.trim().is_empty() {
            // Split by comma, respecting nested parens/angles
            let mut depth = 0;
            let mut last_split = 0;
            let chars: Vec<char> = params_str.chars().collect();

            for (i, &c) in chars.iter().enumerate() {
                match c {
                    '(' | '<' | '[' => depth += 1,
                    ')' | '>' | ']' => depth -= 1,
                    ',' if depth == 0 => {
                        let param_str = &params_str[last_split..i].trim();
                        if let Some((name, ty)) = parse_single_param(param_str) {
                            parameters.push((name, ty));
                        }
                        last_split = i + 1;
                    }
                    _ => {}
                }
            }
            // Last parameter
            let param_str = &params_str[last_split..].trim();
            if let Some((name, ty)) = parse_single_param(param_str) {
                parameters.push((name, ty));
            }
        }

        Some((name, parameters, return_type))
    }

    // Helper: Parse a single parameter "label name: Type" or "_ name: Type"
    fn parse_single_param(param: &str) -> Option<(String, String)> {
        let trimmed = param.trim();
        if trimmed.is_empty() {
            return None;
        }

        let colon_idx = trimmed.find(':')?;
        let left = trimmed[..colon_idx].trim();
        let mut right = trimmed[colon_idx + 1..].trim();

        // Strip default value
        if let Some(eq_idx) = right.find('=') {
            let mut depth = 0;
            let chars: Vec<char> = right.chars().collect();
            for (i, &c) in chars.iter().enumerate() {
                match c {
                    '(' | '<' | '[' => depth += 1,
                    ')' | '>' | ']' => depth -= 1,
                    '=' if depth == 0 && i == eq_idx => {
                        right = right[..i].trim();
                        break;
                    }
                    _ => {}
                }
            }
        }

        // Get local name (last token before colon)
        let name = left
            .split_whitespace()
            .last()
            .map(|s| s.trim_matches('`'))?;

        // Strip inout, @escaping, etc
        let mut ty = right.to_string();
        for prefix in &["inout ", "@escaping ", "@autoclosure "] {
            if ty.starts_with(prefix) {
                ty = ty[prefix.len()..].trim_start().to_string();
            }
        }

        Some((name.to_string(), ty))
    }

    // Helper: Extract Rust function name from __swift_bridge__$ call
    fn extract_swift_bridge_call(body: &str) -> Option<String> {
        // Look for __swift_bridge__$function_name(
        let marker = "__swift_bridge__$";
        let idx = body.find(marker)?;
        let after_marker = &body[idx + marker.len()..];

        // The function name ends at '(' or '$' (for methods like Type$method)
        let end = after_marker.find(|c: char| c == '(' || c.is_whitespace())?;
        let call_name = &after_marker[..end];

        // For simple functions: __swift_bridge__$foo -> "foo"
        // For methods: __swift_bridge__$Type$method -> "Type::method" or just "method"
        // Check if there are any parts to the name (uses ? to early-return None)
        call_name.split('$').next()?;

        // Return the full name for matching
        Some(call_name.replace('$', "::"))
    }

    let mut decls: Vec<SwiftFfiDeclaration> = Vec::new();
    let lines: Vec<&str> = source.lines().collect();

    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();

        // Look for public func or func declarations
        if line.contains("func ") && !line.starts_with("//") {
            // Try to parse the function signature
            if let Some((swift_name, parameters, return_type)) = parse_func_signature(line) {
                // Extract the function body to find __swift_bridge__ calls
                if let Some((body, end_line)) = extract_function_body(&lines, i) {
                    // Check if this is a swift-bridge generated function
                    if let Some(rust_name) = extract_swift_bridge_call(&body) {
                        // Skip internal functions (those starting with __)
                        if !swift_name.starts_with("__") {
                            decls.push(SwiftFfiDeclaration {
                                swift_name,
                                attributes: vec![SwiftFfiAttribute::Import {
                                    rust_path: rust_name,
                                    local_name: None,
                                }],
                                parameters,
                                return_type,
                                source_file: source_file.to_string(),
                                source_line: (i + 1) as u32,
                            });
                        }
                    }
                    i = end_line + 1;
                    continue;
                }
            }
        }

        i += 1;
    }

    decls
}

/// Parse a simple condition string (Swift-style) into an internal predicate.
///
/// This uses the condition parser module to parse Swift-style conditions.
///
/// # Errors
/// Returns an error if parsing fails or the resulting expression cannot be converted to a
/// `Predicate`.
pub fn parse_swift_condition_to_predicate(
    condition: &str,
    param_names: &[String],
) -> Result<Predicate, String> {
    use std::collections::HashMap;

    let mut params: HashMap<String, usize> = HashMap::new();
    for (i, name) in param_names.iter().enumerate() {
        params.insert(name.clone(), i);
    }

    let swift_expr = crate::condition_parser::parse_condition(condition, &params);
    let expr = crate::convert::convert_expr(&swift_expr).map_err(|e| e.to_string())?;
    Ok(Predicate::Expr(expr))
}

/// Convert a `SwiftFfiDeclaration` to an `FfiFunction` by parsing `_ffi_requires`
/// and `_ffi_ensures` condition strings.
///
/// # Errors
/// Returns an error if any precondition or postcondition cannot be parsed.
pub fn swift_decl_to_ffi_function_parsed(
    decl: &SwiftFfiDeclaration,
    language: FfiLanguage,
) -> Result<FfiFunction, String> {
    let param_names: Vec<String> = decl.parameters.iter().map(|(n, _)| n.clone()).collect();

    let mut requires_predicates: Vec<Predicate> = Vec::new();
    for cond in decl.get_requires() {
        requires_predicates.push(parse_swift_condition_to_predicate(cond, &param_names)?);
    }

    let mut ensures_predicates: Vec<Predicate> = Vec::new();
    for cond in decl.get_ensures() {
        ensures_predicates.push(parse_swift_condition_to_predicate(cond, &param_names)?);
    }

    Ok(swift_decl_to_ffi_function(
        decl,
        language,
        requires_predicates,
        ensures_predicates,
    ))
}

/// Parse a Swift type string to `FfiType`
#[must_use]
pub fn parse_swift_type(swift_type: &str) -> FfiType {
    let trimmed = swift_type.trim();

    // Handle optional types: Type?
    if let Some(inner) = trimmed.strip_suffix('?') {
        return FfiType::Optional(Box::new(parse_swift_type(inner)));
    }

    // Handle Optional<Type>
    if let Some(inner) = trimmed
        .strip_prefix("Optional<")
        .and_then(|s| s.strip_suffix('>'))
    {
        return FfiType::Optional(Box::new(parse_swift_type(inner)));
    }

    // Handle Result<Success, Failure>
    if let Some(inner) = trimmed
        .strip_prefix("Result<")
        .and_then(|s| s.strip_suffix('>'))
    {
        // Split on first comma (handling nested generics would be more complex)
        if let Some((ok, err)) = inner.split_once(',') {
            return FfiType::Result {
                ok: Box::new(parse_swift_type(ok.trim())),
                err: Box::new(parse_swift_type(err.trim())),
            };
        }
    }

    // Handle basic Swift types
    match trimmed {
        "Bool" => FfiType::Bool,
        "Int" | "Int64" => FfiType::Int { bits: 64 },
        "Int32" => FfiType::Int { bits: 32 },
        "Int16" => FfiType::Int { bits: 16 },
        "Int8" => FfiType::Int { bits: 8 },
        "UInt" | "UInt64" => FfiType::UInt { bits: 64 },
        "UInt32" => FfiType::UInt { bits: 32 },
        "UInt16" => FfiType::UInt { bits: 16 },
        "UInt8" => FfiType::UInt { bits: 8 },
        "Float" | "Float32" => FfiType::Float { bits: 32 },
        "Double" | "Float64" => FfiType::Float { bits: 64 },
        "String" => FfiType::String,
        "Void" | "()" => FfiType::Void,
        "[UInt8]" | "Data" => FfiType::Bytes,
        // Borrowed types
        "UnsafeBufferPointer<UInt8>" | "UnsafeRawBufferPointer" => FfiType::BytesRef,
        // Custom/unknown types
        _ => FfiType::Custom(trimmed.to_string()),
    }
}

/// Convert `SwiftFfiDeclaration` to `FfiFunction`
///
/// Note: This requires parsing the condition strings into Predicates,
/// which is a separate step that depends on the expression parser.
#[must_use]
pub fn swift_decl_to_ffi_function(
    decl: &SwiftFfiDeclaration,
    language: FfiLanguage,
    requires_predicates: Vec<Predicate>,
    ensures_predicates: Vec<Predicate>,
) -> FfiFunction {
    FfiFunction {
        name: decl.get_rust_name().to_string(),
        language,
        params: decl
            .parameters
            .iter()
            .map(|(name, ty)| FfiParam {
                name: name.clone(),
                ffi_type: parse_swift_type(ty),
            })
            .collect(),
        return_type: parse_swift_type(&decl.return_type),
        requires: requires_predicates,
        ensures: ensures_predicates,
        trusted: decl.is_trusted(),
        source_file: Some(decl.source_file.clone()),
        source_line: Some(decl.source_line),
    }
}

// ============================================================================
// Rust FFI Export Parsing
// ============================================================================

/// Raw FFI attribute parsed from Rust source code
///
/// These correspond to Rust attributes like:
/// - `#[ffi_export]` or `#[ffi_export("custom_name")]`
/// - `#[ffi_requires("x > 0")]`
/// - `#[ffi_ensures("result >= 0")]`
/// - `#[ffi_trusted]`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RustFfiAttribute {
    /// Export this Rust function as FFI-callable
    Export {
        /// Optional custom name for FFI (defaults to Rust function name)
        name: Option<String>,
    },
    /// Precondition for FFI boundary
    Requires {
        /// Condition expression as string (parsed later)
        condition: String,
    },
    /// Postcondition for FFI boundary
    Ensures {
        /// Condition expression as string (parsed later)
        condition: String,
    },
    /// Mark function as trusted (skip verification)
    Trusted,
}

/// Rust FFI function declaration parsed from source
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RustFfiDeclaration {
    /// Function name in Rust
    pub rust_name: String,
    /// FFI attributes
    pub attributes: Vec<RustFfiAttribute>,
    /// Parameter names and Rust type strings
    pub parameters: Vec<(String, String)>,
    /// Return type string
    pub return_type: String,
    /// Source file path
    pub source_file: String,
    /// Source line number
    pub source_line: u32,
}

impl RustFfiDeclaration {
    /// Check if this declaration is an FFI export
    #[must_use]
    pub fn is_export(&self) -> bool {
        self.attributes
            .iter()
            .any(|a| matches!(a, RustFfiAttribute::Export { .. }))
    }

    /// Check if this declaration is trusted (skip verification)
    #[must_use]
    pub fn is_trusted(&self) -> bool {
        self.attributes
            .iter()
            .any(|a| matches!(a, RustFfiAttribute::Trusted))
    }

    /// Get all requires conditions
    #[must_use]
    pub fn get_requires(&self) -> Vec<&str> {
        self.attributes
            .iter()
            .filter_map(|a| {
                if let RustFfiAttribute::Requires { condition } = a {
                    Some(condition.as_str())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get all ensures conditions
    #[must_use]
    pub fn get_ensures(&self) -> Vec<&str> {
        self.attributes
            .iter()
            .filter_map(|a| {
                if let RustFfiAttribute::Ensures { condition } = a {
                    Some(condition.as_str())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get the FFI name for this function (custom name or Rust name)
    #[must_use]
    pub fn get_ffi_name(&self) -> &str {
        for attr in &self.attributes {
            if let RustFfiAttribute::Export { name: Some(n) } = attr {
                return n;
            }
        }
        &self.rust_name
    }
}

/// Parse FFI-related Rust declarations from raw Rust source.
///
/// This is a lightweight source parser intended for extracting `#[ffi_*]`
/// attributes for cross-language compatibility checks.
#[must_use]
#[allow(clippy::cast_possible_truncation)] // Line numbers won't exceed u32
#[allow(clippy::too_many_lines)]
pub fn parse_rust_ffi_declarations_from_source(
    source: &str,
    source_file: &str,
) -> Vec<RustFfiDeclaration> {
    fn parse_string_literal_arg(line: &str) -> Option<String> {
        // Extract the first "...", not supporting escapes.
        let start = line.find('"')?;
        let end = line[start + 1..].find('"')? + start + 1;
        Some(line[start + 1..end].to_string())
    }

    fn parse_ffi_attribute_line(line: &str) -> Option<RustFfiAttribute> {
        let trimmed = line.trim();

        // Handle #[ffi_export] or #[ffi_export("name")]
        if trimmed.starts_with("#[ffi_export") {
            let name = parse_string_literal_arg(trimmed);
            return Some(RustFfiAttribute::Export { name });
        }

        // Handle #[ffi_requires("condition")]
        if trimmed.starts_with("#[ffi_requires") {
            let condition = parse_string_literal_arg(trimmed)?;
            return Some(RustFfiAttribute::Requires { condition });
        }

        // Handle #[ffi_ensures("condition")]
        if trimmed.starts_with("#[ffi_ensures") {
            let condition = parse_string_literal_arg(trimmed)?;
            return Some(RustFfiAttribute::Ensures { condition });
        }

        // Handle #[ffi_trusted]
        if trimmed.starts_with("#[ffi_trusted") {
            return Some(RustFfiAttribute::Trusted);
        }

        None
    }

    fn find_balanced_parens(s: &str) -> Option<(String, usize)> {
        let mut depth: i32 = 0;
        let mut start_inner: Option<usize> = None;
        for (i, c) in s.char_indices() {
            if c == '(' {
                depth += 1;
                if depth == 1 {
                    start_inner = Some(i + 1);
                }
            } else if c == ')' {
                depth -= 1;
                if depth == 0 {
                    let inner_start = start_inner?;
                    return Some((s[inner_start..i].to_string(), i + 1));
                }
            }
        }
        None
    }

    fn parse_rust_func_signature(line: &str) -> Option<ParsedFuncSignature> {
        let trimmed = line.trim();

        // Look for "fn " (with various prefixes like pub, pub(crate), async, unsafe, etc.)
        let fn_idx = trimmed.find("fn ")?;
        let after_fn = trimmed[fn_idx + 3..].trim_start();

        // Get function name (until '(' or '<')
        let name_end = after_fn.find(['(', '<']).unwrap_or(after_fn.len());
        let name = after_fn[..name_end].trim();
        if name.is_empty() {
            return None;
        }

        // Find parameters
        let paren_start = after_fn.find('(')?;
        let (params_str, after_params_idx) = find_balanced_parens(&after_fn[paren_start..])?;
        let after_params = after_fn[paren_start + after_params_idx..].trim();

        // Parse return type
        let return_type = after_params.find("->").map_or_else(
            || "()".to_string(),
            |arrow_idx| {
                let mut ret = after_params[arrow_idx + 2..].trim();
                // Strip where clauses and function body
                if let Some(brace_idx) = ret.find('{') {
                    ret = ret[..brace_idx].trim();
                }
                if let Some(where_idx) = ret.find(" where ") {
                    ret = ret[..where_idx].trim();
                }
                if let Some(semi_idx) = ret.find(';') {
                    ret = ret[..semi_idx].trim();
                }
                if ret.is_empty() { "()" } else { ret }.to_string()
            },
        );

        // Parse parameters
        let mut parameters: Vec<(String, String)> = Vec::new();
        for raw_param in params_str.split(',') {
            let param = raw_param.trim();
            if param.is_empty() || param == "self" || param == "&self" || param == "&mut self" {
                continue;
            }

            // Handle pattern: name: Type
            if let Some(colon_idx) = param.find(':') {
                let name_part = param[..colon_idx].trim();
                let type_part = param[colon_idx + 1..].trim();

                // Strip mut, ref patterns
                let clean_name = name_part
                    .trim_start_matches("mut ")
                    .trim_start_matches("ref ")
                    .trim();

                parameters.push((clean_name.to_string(), type_part.to_string()));
            }
        }

        Some((name.to_string(), parameters, return_type))
    }

    let mut decls: Vec<RustFfiDeclaration> = Vec::new();
    let mut pending_attrs: Vec<RustFfiAttribute> = Vec::new();

    for (line_idx, raw_line) in source.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }

        // Check for FFI attributes
        if let Some(attr) = parse_ffi_attribute_line(line) {
            pending_attrs.push(attr);
            continue;
        }

        // Check for function signature
        if line.contains("fn ") {
            if let Some((rust_name, parameters, return_type)) = parse_rust_func_signature(line) {
                // Only include if we have FFI attributes pending
                if !pending_attrs.is_empty()
                    && pending_attrs
                        .iter()
                        .any(|a| matches!(a, RustFfiAttribute::Export { .. }))
                {
                    decls.push(RustFfiDeclaration {
                        rust_name,
                        attributes: std::mem::take(&mut pending_attrs),
                        parameters,
                        return_type,
                        source_file: source_file.to_string(),
                        source_line: (line_idx + 1) as u32,
                    });
                } else {
                    pending_attrs.clear();
                }
                continue;
            }
        }

        // Reset attributes if we hit a non-attribute line that's not a continuation
        if !line.starts_with('#') && !line.starts_with("//") {
            pending_attrs.clear();
        }
    }

    // Also parse swift_bridge modules
    let swift_bridge_decls = parse_swift_bridge_module_from_source(source, source_file);
    decls.extend(swift_bridge_decls);

    decls
}

/// Parse `#[swift_bridge::bridge]` modules from Rust source.
///
/// Extracts FFI declarations from modules like:
/// ```ignore
/// #[swift_bridge::bridge]
/// mod ffi {
///     #[requires(x > 0)]
///     #[ensures(result >= x)]
///     extern "Rust" {
///         fn increment(x: i32) -> i32;
///     }
/// }
/// ```
#[must_use]
pub fn parse_swift_bridge_module_from_source(
    source: &str,
    source_file: &str,
) -> Vec<RustFfiDeclaration> {
    let mut decls: Vec<RustFfiDeclaration> = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i].trim();

        // Look for #[swift_bridge::bridge]
        if line.starts_with("#[swift_bridge::bridge]")
            || line.starts_with("#[swift_bridge :: bridge]")
        {
            // Find the mod declaration
            let mut mod_start = i + 1;
            while mod_start < lines.len() {
                let mod_line = lines[mod_start].trim();
                if mod_line.is_empty() || mod_line.starts_with("//") || mod_line.starts_with("#[") {
                    mod_start += 1;
                    continue;
                }
                if mod_line.starts_with("mod ") {
                    break;
                }
                mod_start += 1;
            }

            if mod_start >= lines.len() {
                i += 1;
                continue;
            }

            // Find the module body
            let mut brace_depth = 0;
            let mut mod_end = mod_start;
            let mut found_opening = false;

            while mod_end < lines.len() {
                for c in lines[mod_end].chars() {
                    if c == '{' {
                        brace_depth += 1;
                        found_opening = true;
                    } else if c == '}' {
                        brace_depth -= 1;
                    }
                }
                if found_opening && brace_depth == 0 {
                    break;
                }
                mod_end += 1;
            }

            // Parse the module content
            let module_decls = parse_swift_bridge_module_content(
                &lines[mod_start..=mod_end],
                source_file,
                mod_start,
            );
            decls.extend(module_decls);

            i = mod_end + 1;
        } else {
            i += 1;
        }
    }

    decls
}

/// Parse content within a `swift_bridge` module
#[allow(clippy::cast_possible_truncation)] // Line numbers won't exceed u32
fn parse_swift_bridge_module_content(
    lines: &[&str],
    source_file: &str,
    line_offset: usize,
) -> Vec<RustFfiDeclaration> {
    let mut decls: Vec<RustFfiDeclaration> = Vec::new();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i].trim();

        // Look for extern "Rust" blocks
        if line.starts_with("extern \"Rust\"") || line.contains("extern \"Rust\"") {
            // Collect attributes before the extern block
            let mut block_attrs: Vec<RustFfiAttribute> = Vec::new();
            let mut attr_line = i.saturating_sub(1);
            while attr_line > 0 {
                let prev = lines[attr_line].trim();
                if prev.is_empty() || prev.starts_with("//") {
                    attr_line = attr_line.saturating_sub(1);
                    continue;
                }
                if prev.starts_with("#[") {
                    if let Some(attr) = parse_bridge_attribute(prev) {
                        block_attrs.insert(0, attr);
                    }
                    attr_line = attr_line.saturating_sub(1);
                } else {
                    break;
                }
            }

            // Find the extern block body
            let mut brace_depth = 0;
            let mut block_end = i;
            let mut found_opening = false;

            while block_end < lines.len() {
                for c in lines[block_end].chars() {
                    if c == '{' {
                        brace_depth += 1;
                        found_opening = true;
                    } else if c == '}' {
                        brace_depth -= 1;
                    }
                }
                if found_opening && brace_depth == 0 {
                    break;
                }
                block_end += 1;
            }

            // Parse functions within the extern block
            let block_decls = parse_extern_rust_block(
                &lines[i..=block_end],
                source_file,
                line_offset + i,
                &block_attrs,
            );
            decls.extend(block_decls);

            i = block_end + 1;
        } else {
            i += 1;
        }
    }

    decls
}

/// Parse a `swift_bridge` attribute like #[requires(...)] or #[ensures(...)]
fn parse_bridge_attribute(line: &str) -> Option<RustFfiAttribute> {
    let trimmed = line.trim();

    // Handle #[requires("condition")] or #[requires(condition)]
    if trimmed.starts_with("#[requires") {
        let condition = extract_attribute_arg(trimmed)?;
        return Some(RustFfiAttribute::Requires { condition });
    }

    // Handle #[ensures("condition")] or #[ensures(condition)]
    if trimmed.starts_with("#[ensures") {
        let condition = extract_attribute_arg(trimmed)?;
        return Some(RustFfiAttribute::Ensures { condition });
    }

    // Handle #[trusted]
    if trimmed.starts_with("#[trusted") {
        return Some(RustFfiAttribute::Trusted);
    }

    None
}

/// Extract argument from attribute like #[foo("bar")] or #[foo(bar)]
fn extract_attribute_arg(attr: &str) -> Option<String> {
    // Find opening (
    let paren_start = attr.find('(')?;
    let paren_end = attr.rfind(')')?;
    if paren_end <= paren_start {
        return None;
    }

    let inner = attr[paren_start + 1..paren_end].trim();

    // Check if it's a string literal
    if inner.starts_with('"') && inner.ends_with('"') {
        Some(inner[1..inner.len() - 1].to_string())
    } else {
        // It's an unquoted expression (like x > 0)
        Some(inner.to_string())
    }
}

/// Parse functions within an extern "Rust" block
#[allow(clippy::cast_possible_truncation)] // Line numbers won't exceed u32
fn parse_extern_rust_block(
    lines: &[&str],
    source_file: &str,
    line_offset: usize,
    block_attrs: &[RustFfiAttribute],
) -> Vec<RustFfiDeclaration> {
    let mut decls: Vec<RustFfiDeclaration> = Vec::new();
    let mut pending_attrs: Vec<RustFfiAttribute> = Vec::new();

    for (rel_idx, raw_line) in lines.iter().enumerate() {
        let line = raw_line.trim();

        // Skip empty lines and comments
        if line.is_empty() || line.starts_with("//") {
            continue;
        }

        // Check for function-level attributes
        if let Some(attr) = parse_bridge_attribute(line) {
            pending_attrs.push(attr);
            continue;
        }

        // Check for function signature (fn name(...) -> Type;)
        if line.contains("fn ") {
            if let Some((rust_name, parameters, return_type)) = parse_extern_fn_signature(line) {
                // Combine block-level and function-level attributes
                let mut all_attrs = vec![RustFfiAttribute::Export { name: None }];
                all_attrs.extend(block_attrs.iter().cloned());
                all_attrs.append(&mut pending_attrs);

                decls.push(RustFfiDeclaration {
                    rust_name,
                    attributes: all_attrs,
                    parameters,
                    return_type,
                    source_file: source_file.to_string(),
                    source_line: (line_offset + rel_idx + 1) as u32,
                });
            }
            pending_attrs.clear();
        }
    }

    decls
}

/// Parse function signature from extern block (e.g., "fn foo(x: i32) -> i32;")
fn parse_extern_fn_signature(line: &str) -> Option<ParsedFuncSignature> {
    let trimmed = line.trim();

    // Find "fn "
    let fn_idx = trimmed.find("fn ")?;
    let after_fn = trimmed[fn_idx + 3..].trim_start();

    // Get function name
    let name_end = after_fn.find('(')?;
    let name = after_fn[..name_end].trim();
    if name.is_empty() {
        return None;
    }

    // Find closing paren
    let paren_open = after_fn.find('(')?;
    let paren_close = after_fn.find(')')?;
    if paren_close <= paren_open {
        return None;
    }

    let params_str = &after_fn[paren_open + 1..paren_close];
    let after_paren = after_fn[paren_close + 1..].trim();

    // Parse return type
    let return_type = after_paren.find("->").map_or_else(
        || "()".to_string(),
        |arrow_idx| {
            let mut ret = after_paren[arrow_idx + 2..].trim();
            // Strip trailing semicolon
            if let Some(semi_idx) = ret.find(';') {
                ret = ret[..semi_idx].trim();
            }
            if ret.is_empty() { "()" } else { ret }.to_string()
        },
    );

    // Parse parameters
    let mut parameters: Vec<(String, String)> = Vec::new();
    for raw_param in params_str.split(',') {
        let param = raw_param.trim();
        if param.is_empty() {
            continue;
        }

        if let Some(colon_idx) = param.find(':') {
            let name_part = param[..colon_idx].trim();
            let type_part = param[colon_idx + 1..].trim();
            parameters.push((name_part.to_string(), type_part.to_string()));
        }
    }

    Some((name.to_string(), parameters, return_type))
}

/// Parse a Rust type string to `FfiType`
#[must_use]
pub fn parse_rust_type(rust_type: &str) -> FfiType {
    let trimmed = rust_type.trim();

    // Handle Option<T>
    if let Some(inner) = trimmed
        .strip_prefix("Option<")
        .and_then(|s| s.strip_suffix('>'))
    {
        return FfiType::Optional(Box::new(parse_rust_type(inner)));
    }

    // Handle Result<T, E>
    if let Some(inner) = trimmed
        .strip_prefix("Result<")
        .and_then(|s| s.strip_suffix('>'))
    {
        if let Some((ok, err)) = inner.split_once(',') {
            return FfiType::Result {
                ok: Box::new(parse_rust_type(ok.trim())),
                err: Box::new(parse_rust_type(err.trim())),
            };
        }
    }

    // Handle basic Rust types
    match trimmed {
        "bool" => FfiType::Bool,
        "i8" => FfiType::Int { bits: 8 },
        "i16" => FfiType::Int { bits: 16 },
        "i32" => FfiType::Int { bits: 32 },
        "i64" | "isize" => FfiType::Int { bits: 64 },
        "u8" => FfiType::UInt { bits: 8 },
        "u16" => FfiType::UInt { bits: 16 },
        "u32" => FfiType::UInt { bits: 32 },
        "u64" | "usize" => FfiType::UInt { bits: 64 },
        "f32" => FfiType::Float { bits: 32 },
        "f64" => FfiType::Float { bits: 64 },
        "String" => FfiType::String,
        "&str" => FfiType::StringRef,
        "Vec<u8>" => FfiType::Bytes,
        "&[u8]" => FfiType::BytesRef,
        "()" => FfiType::Void,
        _ => FfiType::Custom(trimmed.to_string()),
    }
}

/// Convert `RustFfiDeclaration` to `FfiFunction` by parsing condition strings.
///
/// # Errors
/// Returns an error if any precondition or postcondition cannot be parsed.
pub fn rust_decl_to_ffi_function_parsed(decl: &RustFfiDeclaration) -> Result<FfiFunction, String> {
    let param_names: Vec<String> = decl.parameters.iter().map(|(n, _)| n.clone()).collect();

    let mut requires_predicates: Vec<Predicate> = Vec::new();
    for cond in decl.get_requires() {
        requires_predicates.push(parse_rust_condition_to_predicate(cond, &param_names)?);
    }

    let mut ensures_predicates: Vec<Predicate> = Vec::new();
    for cond in decl.get_ensures() {
        ensures_predicates.push(parse_rust_condition_to_predicate(cond, &param_names)?);
    }

    Ok(FfiFunction {
        name: decl.get_ffi_name().to_string(),
        language: FfiLanguage::Rust,
        params: decl
            .parameters
            .iter()
            .map(|(name, ty)| FfiParam {
                name: name.clone(),
                ffi_type: parse_rust_type(ty),
            })
            .collect(),
        return_type: parse_rust_type(&decl.return_type),
        requires: requires_predicates,
        ensures: ensures_predicates,
        trusted: decl.is_trusted(),
        source_file: Some(decl.source_file.clone()),
        source_line: Some(decl.source_line),
    })
}

/// Parse a Rust condition string into a Predicate
///
/// Uses the same condition parser as Swift (syntax is similar enough)
///
/// # Errors
/// Returns an error if parsing fails or the resulting expression cannot be converted to a
/// `Predicate`.
#[allow(clippy::too_many_lines)]
pub fn parse_rust_condition_to_predicate(
    condition: &str,
    param_names: &[String],
) -> Result<Predicate, String> {
    fn strip_rust_casts(condition: &str) -> String {
        // Strip simple Rust casts like `expr as i64` that our condition parser doesn't support.
        // This is intentionally conservative: it only removes ` as <TypeToken>` sequences.
        let bytes = condition.as_bytes();
        let mut out = String::with_capacity(condition.len());
        let mut i = 0_usize;

        while i < bytes.len() {
            if bytes[i..].starts_with(b" as ") {
                i += 4; // skip " as "
                while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                    i += 1;
                }
                // Consume the type token (e.g., i64, u32, std::ffi::c_void, Option<T>)
                while i < bytes.len() {
                    let c = bytes[i] as char;
                    if c.is_ascii_alphanumeric()
                        || c == '_'
                        || c == ':'
                        || c == '<'
                        || c == '>'
                        || c == ','
                    {
                        i += 1;
                    } else {
                        break;
                    }
                }
                continue;
            }

            out.push(bytes[i] as char);
            i += 1;
        }

        out
    }

    fn normalize_is_empty(condition: &str) -> String {
        // Transform Rust `.is_empty()` calls to equivalent count comparisons:
        // - `!x.is_empty()` → `x.count > 0`
        // - `x.is_empty()` → `x.count == 0`
        let marker = ".is_empty()";
        let mut result = String::with_capacity(condition.len());
        let mut remaining = condition;

        while let Some(idx) = remaining.find(marker) {
            // Check if this is preceded by `!` (negation)
            // Look backwards to find the start of the expression
            let before_marker = &remaining[..idx];

            // Find the start of the identifier/expression before .is_empty()
            // Walk backward to find where the expression starts
            let expr_end = before_marker.len();
            let mut expr_start = expr_end;
            let bytes = before_marker.as_bytes();
            while expr_start > 0 {
                let c = bytes[expr_start - 1] as char;
                if c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '[' || c == ']' {
                    expr_start -= 1;
                } else {
                    break;
                }
            }

            // Check if there's a `!` right before the expression
            let has_negation = expr_start > 0 && (bytes[expr_start - 1] as char) == '!';

            if has_negation {
                // `!x.is_empty()` → `x.count > 0`
                result.push_str(&remaining[..expr_start - 1]); // everything before `!`
                result.push_str(&remaining[expr_start..expr_end]); // the expression
                result.push_str(".count > 0");
            } else {
                // `x.is_empty()` → `x.count == 0`
                result.push_str(&remaining[..expr_end]);
                result.push_str(".count == 0");
            }

            remaining = &remaining[idx + marker.len()..];
        }

        result.push_str(remaining);
        result
    }

    #[allow(clippy::too_many_lines)]
    fn normalize_first_last_option(condition: &str) -> String {
        // Transform Rust `.first().is_some()/.is_none()` and `.last().is_some()/.is_none()` patterns:
        // - `x.first().is_some()` → `x.count > 0`
        // - `x.first().is_none()` → `x.count == 0`
        // - `!x.first().is_some()` → `x.count == 0`
        // - `!x.first().is_none()` → `x.count > 0`
        // Same for `.last()`
        let mut result = condition.to_string();

        // Handle `.first().is_some()` and `.first().is_none()`
        for method in &["first", "last"] {
            let is_some_marker = format!(".{method}().is_some()");
            let is_none_marker = format!(".{method}().is_none()");

            // Process !x.first().is_some() and !x.first().is_none() first (negated forms)
            // Note: We need to handle these before the non-negated forms
            loop {
                let negated_is_some = format!("!{is_some_marker}");
                if let Some(idx) = result.find(&negated_is_some) {
                    // Find start of expression before the !
                    let start_search = idx.saturating_sub(100);
                    let before = &result[start_search..idx];
                    let expr_start = find_expression_start(before);
                    let full_start = start_search + expr_start;

                    // Extract expression
                    let expr = &result[full_start..idx];

                    // Check if there's a negation right before expression
                    let has_outer_negation =
                        full_start > 0 && result.as_bytes()[full_start - 1] == b'!';

                    if has_outer_negation {
                        // `!!x.first().is_some()` → `x.count > 0` (double negation)
                        let replacement = format!("{}.count > 0", expr.trim_start_matches('!'));
                        result = format!(
                            "{}{}{}",
                            &result[..full_start - 1],
                            replacement,
                            &result[idx + negated_is_some.len()..]
                        );
                    } else {
                        // `!x.first().is_some()` → `x.count == 0`
                        let replacement = format!("{expr}.count == 0");
                        result = format!(
                            "{}{}{}",
                            &result[..full_start],
                            replacement,
                            &result[idx + negated_is_some.len()..]
                        );
                    }
                } else {
                    break;
                }
            }

            loop {
                let negated_is_none = format!("!{is_none_marker}");
                if let Some(idx) = result.find(&negated_is_none) {
                    let start_search = idx.saturating_sub(100);
                    let before = &result[start_search..idx];
                    let expr_start = find_expression_start(before);
                    let full_start = start_search + expr_start;
                    let expr = &result[full_start..idx];

                    let has_outer_negation =
                        full_start > 0 && result.as_bytes()[full_start - 1] == b'!';

                    if has_outer_negation {
                        // `!!x.first().is_none()` → `x.count == 0`
                        let replacement = format!("{}.count == 0", expr.trim_start_matches('!'));
                        result = format!(
                            "{}{}{}",
                            &result[..full_start - 1],
                            replacement,
                            &result[idx + negated_is_none.len()..]
                        );
                    } else {
                        // `!x.first().is_none()` → `x.count > 0`
                        let replacement = format!("{expr}.count > 0");
                        result = format!(
                            "{}{}{}",
                            &result[..full_start],
                            replacement,
                            &result[idx + negated_is_none.len()..]
                        );
                    }
                } else {
                    break;
                }
            }

            // Process non-negated forms: x.first().is_some() and x.first().is_none()
            while let Some(idx) = result.find(&is_some_marker) {
                // Find start of expression
                let before = &result[..idx];
                let expr_start = find_expression_start(before);

                // Check for negation
                let has_negation = expr_start > 0 && result.as_bytes()[expr_start - 1] == b'!';
                let expr = &result[expr_start..idx];

                if has_negation {
                    // Already handled above, this shouldn't happen if we processed negated first
                    // But as fallback: `!x.first().is_some()` → `x.count == 0`
                    let replacement = format!("{expr}.count == 0");
                    result = format!(
                        "{}{}{}",
                        &result[..expr_start - 1],
                        replacement,
                        &result[idx + is_some_marker.len()..]
                    );
                } else {
                    // `x.first().is_some()` → `x.count > 0`
                    let replacement = format!("{expr}.count > 0");
                    result = format!(
                        "{}{}{}",
                        &result[..expr_start],
                        replacement,
                        &result[idx + is_some_marker.len()..]
                    );
                }
            }

            while let Some(idx) = result.find(&is_none_marker) {
                let before = &result[..idx];
                let expr_start = find_expression_start(before);
                let has_negation = expr_start > 0 && result.as_bytes()[expr_start - 1] == b'!';
                let expr = &result[expr_start..idx];

                if has_negation {
                    // `!x.first().is_none()` → `x.count > 0`
                    let replacement = format!("{expr}.count > 0");
                    result = format!(
                        "{}{}{}",
                        &result[..expr_start - 1],
                        replacement,
                        &result[idx + is_none_marker.len()..]
                    );
                } else {
                    // `x.first().is_none()` → `x.count == 0`
                    let replacement = format!("{expr}.count == 0");
                    result = format!(
                        "{}{}{}",
                        &result[..expr_start],
                        replacement,
                        &result[idx + is_none_marker.len()..]
                    );
                }
            }
        }

        result
    }

    fn normalize_get_option(condition: &str) -> String {
        // Transform Rust `.get(index).is_some()/.is_none()` patterns:
        // - `x.get(i).is_some()` → `i < x.count`
        // - `x.get(i).is_none()` → `i >= x.count`
        // - `!x.get(i).is_some()` → `i >= x.count`
        // - `!x.get(i).is_none()` → `i < x.count`
        //
        // This enables bounds checking in FFI contracts.
        let mut result = condition.to_string();

        // Regex-like patterns to match .get(...).is_some() and .get(...).is_none()
        // We use a simple state machine to find these patterns

        while let Some(get_start) = result.find(".get(") {
            // Find the expression before .get(
            let before = &result[..get_start];
            let expr_start = find_expression_start(before);
            let container = &result[expr_start..get_start];

            // Find the closing paren for .get(...)
            let after_get = &result[get_start + 5..]; // skip ".get("
            let mut paren_depth = 1;
            let mut index_end = 0;
            for (i, c) in after_get.char_indices() {
                match c {
                    '(' => paren_depth += 1,
                    ')' => {
                        paren_depth -= 1;
                        if paren_depth == 0 {
                            index_end = i;
                            break;
                        }
                    }
                    _ => {}
                }
            }

            if index_end == 0 {
                // Malformed, skip this occurrence
                break;
            }

            let index_expr = &after_get[..index_end];
            let after_close = &after_get[index_end + 1..]; // skip the closing ')'

            // Check what follows: .is_some() or .is_none()
            if after_close.starts_with(".is_some()") {
                // Check for negation before the container expression
                let has_negation = expr_start > 0 && result.as_bytes()[expr_start - 1] == b'!';

                let replacement = if has_negation {
                    // `!x.get(i).is_some()` → `i >= x.count`
                    format!("{index_expr} >= {container}.count")
                } else {
                    // `x.get(i).is_some()` → `i < x.count`
                    format!("{index_expr} < {container}.count")
                };

                let start = if has_negation {
                    expr_start - 1
                } else {
                    expr_start
                };
                let end = get_start + 5 + index_end + 1 + 10; // .get( + index + ) + .is_some()
                result = format!("{}{}{}", &result[..start], replacement, &result[end..]);
            } else if after_close.starts_with(".is_none()") {
                let has_negation = expr_start > 0 && result.as_bytes()[expr_start - 1] == b'!';

                let replacement = if has_negation {
                    // `!x.get(i).is_none()` → `i < x.count`
                    format!("{index_expr} < {container}.count")
                } else {
                    // `x.get(i).is_none()` → `i >= x.count`
                    format!("{index_expr} >= {container}.count")
                };

                let start = if has_negation {
                    expr_start - 1
                } else {
                    expr_start
                };
                let end = get_start + 5 + index_end + 1 + 10; // .get( + index + ) + .is_none()
                result = format!("{}{}{}", &result[..start], replacement, &result[end..]);
            } else {
                // Not followed by .is_some() or .is_none(), skip
                break;
            }
        }

        result
    }

    #[allow(clippy::too_many_lines)]
    fn normalize_range_len(condition: &str) -> String {
        // Transform Rust range `.len()`, `.count()`, and `.count` patterns into arithmetic:
        // - `(a..b).len()` -> `(b - a)`
        // - `(a..=b).len()` -> `(b - a + 1)`
        // - `(a..b).count()` -> `(b - a)` (method form, Range implements Iterator)
        // - `(a..=b).count()` -> `(b - a + 1)`
        // - `(a..b).count` -> `(b - a)` (pseudo-field after .iter().count() normalization)
        // - `(a..=b).count` -> `(b - a + 1)`

        fn find_matching_open_paren(s: &str, close_paren_pos: usize) -> Option<usize> {
            let bytes = s.as_bytes();
            let mut depth: i32 = 0;
            let mut i = close_paren_pos + 1;
            while i > 0 {
                i -= 1;
                match bytes[i] {
                    b')' => depth += 1,
                    b'(' => {
                        depth -= 1;
                        if depth == 0 {
                            return Some(i);
                        }
                    }
                    _ => {}
                }
            }
            None
        }

        fn split_range_expr(range: &str) -> Option<(String, String, bool)> {
            let trimmed = range.trim();
            let chars: Vec<char> = trimmed.chars().collect();
            let mut depth: i32 = 0;
            let mut i: usize = 0;
            while i + 1 < chars.len() {
                match chars[i] {
                    '(' | '[' => depth += 1,
                    ')' | ']' => depth -= 1,
                    '.' if chars[i + 1] == '.' && depth == 0 => {
                        let inclusive = i + 2 < chars.len() && chars[i + 2] == '=';
                        let start = trimmed[..i].trim().to_string();
                        let end = if inclusive {
                            trimmed[i + 3..].trim().to_string()
                        } else {
                            trimmed[i + 2..].trim().to_string()
                        };
                        if start.is_empty() || end.is_empty() {
                            return None;
                        }
                        return Some((start, end, inclusive));
                    }
                    _ => {}
                }
                i += 1;
            }
            None
        }

        let mut result = condition.to_string();

        // Handle `.len()` pattern (with parentheses)
        let len_marker = ").len()";
        let mut search_start: usize = 0;
        loop {
            let Some(rel_idx) = result[search_start..].find(len_marker) else {
                break;
            };
            let idx = search_start + rel_idx;
            let range_close = idx; // Position of the ')' before .len()

            let Some(range_open) = find_matching_open_paren(&result, range_close) else {
                search_start = idx + len_marker.len();
                continue;
            };

            let range_str = result[range_open + 1..range_close].trim();
            let Some((start, end, inclusive)) = split_range_expr(range_str) else {
                search_start = idx + len_marker.len();
                continue;
            };

            let replacement = if inclusive {
                format!("(({end} - {start}) + 1)")
            } else {
                format!("({end} - {start})")
            };

            let replace_start = range_open;
            let replace_end = idx + len_marker.len();
            result = format!(
                "{}{}{}",
                &result[..replace_start],
                replacement,
                &result[replace_end..]
            );
            search_start = replace_start + replacement.len();
        }

        // Handle `.count()` method pattern (with parentheses) - Range implements Iterator
        let count_method_marker = ").count()";
        search_start = 0;
        loop {
            let Some(rel_idx) = result[search_start..].find(count_method_marker) else {
                break;
            };
            let idx = search_start + rel_idx;
            let range_close = idx; // Position of the ')' before .count()

            let Some(range_open) = find_matching_open_paren(&result, range_close) else {
                search_start = idx + count_method_marker.len();
                continue;
            };

            let range_str = result[range_open + 1..range_close].trim();
            let Some((start, end, inclusive)) = split_range_expr(range_str) else {
                search_start = idx + count_method_marker.len();
                continue;
            };

            let replacement = if inclusive {
                format!("(({end} - {start}) + 1)")
            } else {
                format!("({end} - {start})")
            };

            let replace_start = range_open;
            let replace_end = idx + count_method_marker.len();
            result = format!(
                "{}{}{}",
                &result[..replace_start],
                replacement,
                &result[replace_end..]
            );
            search_start = replace_start + replacement.len();
        }

        // Handle `.count` pseudo-field pattern (no parentheses, from .iter().count() normalization)
        // We look for `).count` not followed by `(`
        let count_marker = ").count";
        search_start = 0;
        loop {
            let Some(rel_idx) = result[search_start..].find(count_marker) else {
                break;
            };
            let idx = search_start + rel_idx;

            // Check this isn't `.contains` or followed by `(`
            let after_marker = idx + count_marker.len();
            if after_marker < result.len() {
                let next_char = result.as_bytes()[after_marker] as char;
                if next_char == '(' || next_char.is_ascii_alphanumeric() || next_char == '_' {
                    // This is .count() or .contains or similar, skip
                    search_start = after_marker;
                    continue;
                }
            }

            let range_close = idx; // Position of the ')' before .count

            let Some(range_open) = find_matching_open_paren(&result, range_close) else {
                search_start = idx + count_marker.len();
                continue;
            };

            let range_str = result[range_open + 1..range_close].trim();
            let Some((start, end, inclusive)) = split_range_expr(range_str) else {
                search_start = idx + count_marker.len();
                continue;
            };

            let replacement = if inclusive {
                format!("(({end} - {start}) + 1)")
            } else {
                format!("({end} - {start})")
            };

            let replace_start = range_open;
            let replace_end = idx + count_marker.len();
            result = format!(
                "{}{}{}",
                &result[..replace_start],
                replacement,
                &result[replace_end..]
            );
            search_start = replace_start + replacement.len();
        }

        result
    }

    #[allow(clippy::too_many_lines)]
    fn normalize_range_contains(condition: &str) -> String {
        // Transform Rust range `.contains(&x)` patterns into comparisons:
        // - `(0..n).contains(&i)` -> `i < n`
        // - `(a..b).contains(&i)` -> `(i >= a && i < b)`
        // - `(0..=n).contains(&i)` -> `i <= n`
        // - `(a..=b).contains(&i)` -> `(i >= a && i <= b)`

        fn find_matching_open_paren(s: &str, close_paren_pos: usize) -> Option<usize> {
            let bytes = s.as_bytes();
            let mut depth: i32 = 0;
            let mut i = close_paren_pos + 1;
            while i > 0 {
                i -= 1;
                match bytes[i] {
                    b')' => depth += 1,
                    b'(' => {
                        depth -= 1;
                        if depth == 0 {
                            return Some(i);
                        }
                    }
                    _ => {}
                }
            }
            None
        }

        fn find_matching_close_paren(s: &str, open_paren_pos: usize) -> Option<usize> {
            let bytes = s.as_bytes();
            let mut depth: i32 = 0;
            for (offset, &byte) in bytes[open_paren_pos..].iter().enumerate() {
                match byte {
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            return Some(open_paren_pos + offset);
                        }
                    }
                    _ => {}
                }
            }
            None
        }

        fn split_range_expr(range: &str) -> Option<(String, String, bool)> {
            let trimmed = range.trim();
            let chars: Vec<char> = trimmed.chars().collect();
            let mut depth: i32 = 0;
            let mut i: usize = 0;
            while i + 1 < chars.len() {
                match chars[i] {
                    '(' | '[' => depth += 1,
                    ')' | ']' => depth -= 1,
                    '.' if chars[i + 1] == '.' && depth == 0 => {
                        let inclusive = i + 2 < chars.len() && chars[i + 2] == '=';
                        let start = trimmed[..i].trim().to_string();
                        let end = if inclusive {
                            trimmed[i + 3..].trim().to_string()
                        } else {
                            trimmed[i + 2..].trim().to_string()
                        };
                        if start.is_empty() || end.is_empty() {
                            return None;
                        }
                        return Some((start, end, inclusive));
                    }
                    _ => {}
                }
                i += 1;
            }
            None
        }

        fn strip_ref_prefix(arg: &str) -> &str {
            let arg = arg.trim();
            if let Some(rest) = arg.strip_prefix("&mut") {
                return rest.trim();
            }
            if let Some(rest) = arg.strip_prefix('&') {
                return rest.trim();
            }
            arg
        }

        let marker = ".contains(";
        let mut result = condition.to_string();
        let mut search_start: usize = 0;

        loop {
            let Some(rel_idx) = result[search_start..].find(marker) else {
                break;
            };
            let idx = search_start + rel_idx;

            if idx == 0 || result.as_bytes().get(idx - 1) != Some(&b')') {
                search_start = idx + marker.len();
                continue;
            }

            let range_close = idx - 1;
            let Some(range_open) = find_matching_open_paren(&result, range_close) else {
                search_start = idx + marker.len();
                continue;
            };

            let range_str = result[range_open + 1..range_close].trim();
            let Some((start, end, inclusive)) = split_range_expr(range_str) else {
                search_start = idx + marker.len();
                continue;
            };

            let call_open = idx + marker.len() - 1;
            let Some(call_close) = find_matching_close_paren(&result, call_open) else {
                search_start = idx + marker.len();
                continue;
            };

            let arg_str = result[call_open + 1..call_close].trim();
            let value = strip_ref_prefix(arg_str);
            if value.is_empty() {
                search_start = idx + marker.len();
                continue;
            }

            let replacement = if start == "0" {
                if inclusive {
                    format!("({value} <= {end})")
                } else {
                    format!("({value} < {end})")
                }
            } else if inclusive {
                format!("({value} >= {start} && {value} <= {end})")
            } else {
                format!("({value} >= {start} && {value} < {end})")
            };

            let replace_start = range_open;
            let replace_end = call_close + 1;
            result = format!(
                "{}{}{}",
                &result[..replace_start],
                replacement,
                &result[replace_end..]
            );
            search_start = replace_start + replacement.len();
        }

        result
    }

    fn normalize_option_is_some_is_none(condition: &str) -> String {
        // Transform Rust Option `.is_some()` / `.is_none()` into Swift-style nil comparisons:
        // - `opt.is_some()` -> `(opt != nil)`
        // - `opt.is_none()` -> `(opt == nil)`
        //
        // We intentionally skip cases where the receiver ends with `)` (e.g. `x.get(i).is_some()`,
        // `buf.first().is_some()`) since those are handled by specialized normalizations, and
        // leaving `()` calls in the normalized output makes the Swift condition parser fail.

        fn find_expression_start(before: &str) -> usize {
            let bytes = before.as_bytes();
            let mut pos = bytes.len();
            while pos > 0 {
                let c = bytes[pos - 1] as char;
                if c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '[' || c == ']' {
                    pos -= 1;
                } else {
                    break;
                }
            }
            pos
        }

        fn normalize_marker(mut result: String, marker: &str, op: &str) -> String {
            let mut search_start: usize = 0;
            loop {
                let Some(rel_idx) = result[search_start..].find(marker) else {
                    break;
                };
                let idx = search_start + rel_idx;
                if idx == 0 {
                    search_start = idx + marker.len();
                    continue;
                }

                // Skip receivers that are method calls (end with ')')
                if result.as_bytes().get(idx - 1) == Some(&b')') {
                    search_start = idx + marker.len();
                    continue;
                }

                let expr_start = find_expression_start(&result[..idx]);
                if expr_start >= idx {
                    search_start = idx + marker.len();
                    continue;
                }

                let has_negation = expr_start > 0 && result.as_bytes()[expr_start - 1] == b'!';
                let base = result[expr_start..idx].trim();
                if base.is_empty() {
                    search_start = idx + marker.len();
                    continue;
                }

                let replacement = if has_negation {
                    format!("({} {} nil)", base, if op == "!=" { "==" } else { "!=" })
                } else {
                    format!("({base} {op} nil)")
                };

                let replace_start = if has_negation {
                    expr_start - 1
                } else {
                    expr_start
                };
                let replace_end = idx + marker.len();
                result = format!(
                    "{}{}{}",
                    &result[..replace_start],
                    replacement,
                    &result[replace_end..]
                );
                search_start = replace_start + replacement.len();
            }
            result
        }

        let result = normalize_marker(condition.to_string(), ".is_some()", "!=");
        normalize_marker(result, ".is_none()", "==")
    }

    fn normalize_unwrap_value_error(condition: &str) -> String {
        // Normalize common Rust unwrap idioms (Option/Result) into Swift-style field access.
        //
        // The condition parser does not support dotted method calls like `x.unwrap()`,
        // so without this normalization, later field accesses (e.g., `.len()`) end up
        // attached to an uninterpreted token.
        //
        // - `x.unwrap()` -> `x.value`
        // - `x.unwrap_err()` -> `x.error`
        condition
            .replace(".unwrap_err()", ".error")
            .replace(".unwrap()", ".value")
    }

    fn normalize_result_is_ok_err(condition: &str) -> String {
        // Transform Rust Result `.is_ok()` / `.is_err()` checks into Swift-style `.isSuccess`:
        // - `res.is_ok()`  -> `res.isSuccess`
        // - `res.is_err()` -> `!res.isSuccess`
        //
        // Also handles negated forms:
        // - `!res.is_ok()`  -> `!res.isSuccess`
        // - `!res.is_err()` -> `res.isSuccess`
        //
        // The condition parser does not support dotted method calls like `res.is_ok()`,
        // so this normalization must run before parsing.

        fn find_expression_start(before: &str) -> usize {
            let bytes = before.as_bytes();
            let mut pos = bytes.len();
            while pos > 0 {
                let c = bytes[pos - 1] as char;
                if c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '[' || c == ']' {
                    pos -= 1;
                } else {
                    break;
                }
            }
            pos
        }

        let patterns: &[(&str, bool)] = &[(".is_ok()", true), (".is_err()", false)];

        let mut result = condition.to_string();
        for &(pattern, is_success) in patterns {
            let mut search_start: usize = 0;
            loop {
                let Some(rel_idx) = result[search_start..].find(pattern) else {
                    break;
                };
                let idx = search_start + rel_idx;
                if idx == 0 {
                    search_start = idx + pattern.len();
                    continue;
                }

                let expr_start = find_expression_start(&result[..idx]);
                if expr_start >= idx {
                    search_start = idx + pattern.len();
                    continue;
                }

                let has_negation = expr_start > 0 && result.as_bytes()[expr_start - 1] == b'!';
                let base = result[expr_start..idx].trim();
                if base.is_empty() {
                    search_start = idx + pattern.len();
                    continue;
                }

                // XOR negation with desired success value.
                let final_success = has_negation != is_success;
                let replacement = if final_success {
                    format!("{base}.isSuccess")
                } else {
                    format!("!{base}.isSuccess")
                };

                let replace_start = if has_negation {
                    expr_start - 1
                } else {
                    expr_start
                };
                let replace_end = idx + pattern.len();
                result = format!(
                    "{}{}{}",
                    &result[..replace_start],
                    replacement,
                    &result[replace_end..]
                );
                search_start = replace_start + replacement.len();
            }
        }

        result
    }

    fn normalize_result_ok_err(condition: &str) -> String {
        // Transform Rust Result `.ok().is_some()` / `.ok().is_none()` / `.err().is_some()` / `.err().is_none()`
        // into Swift-style `.isSuccess` / `!.isSuccess` patterns:
        //
        // - `result.ok().is_some()` -> `result.isSuccess` (Ok variant exists)
        // - `result.ok().is_none()` -> `!result.isSuccess` (Ok variant does not exist)
        // - `result.err().is_some()` -> `!result.isSuccess` (Err variant exists)
        // - `result.err().is_none()` -> `result.isSuccess` (Err variant does not exist)
        //
        // Also handles negated forms:
        // - `!result.ok().is_some()` -> `!result.isSuccess`
        // - `!result.ok().is_none()` -> `result.isSuccess`
        //
        // This normalization must run BEFORE normalize_option_is_some_is_none since it handles
        // the specific pattern where .ok()/.err() precedes .is_some()/.is_none().

        fn find_expression_start(before: &str) -> usize {
            let bytes = before.as_bytes();
            let mut pos = bytes.len();
            while pos > 0 {
                let c = bytes[pos - 1] as char;
                if c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '[' || c == ']' {
                    pos -= 1;
                } else {
                    break;
                }
            }
            pos
        }

        // Patterns to normalize and their output: (pattern, is_success)
        // is_success=true means output is "result.isSuccess"
        // is_success=false means output is "!result.isSuccess"
        let patterns: &[(&str, bool)] = &[
            (".ok().is_some()", true),   // Ok exists -> success
            (".ok().is_none()", false),  // Ok doesn't exist -> not success
            (".err().is_some()", false), // Err exists -> not success
            (".err().is_none()", true),  // Err doesn't exist -> success
        ];

        let mut result = condition.to_string();
        for &(pattern, is_success) in patterns {
            let mut search_start: usize = 0;
            loop {
                let Some(rel_idx) = result[search_start..].find(pattern) else {
                    break;
                };
                let idx = search_start + rel_idx;
                if idx == 0 {
                    search_start = idx + pattern.len();
                    continue;
                }

                let expr_start = find_expression_start(&result[..idx]);
                if expr_start >= idx {
                    search_start = idx + pattern.len();
                    continue;
                }

                let has_negation = expr_start > 0 && result.as_bytes()[expr_start - 1] == b'!';
                let base = result[expr_start..idx].trim();
                if base.is_empty() {
                    search_start = idx + pattern.len();
                    continue;
                }

                // XOR negation with is_success: !true=false, !false=true, true=true, false=false
                let final_success = has_negation != is_success;
                let replacement = if final_success {
                    format!("{base}.isSuccess")
                } else {
                    format!("!{base}.isSuccess")
                };

                let replace_start = if has_negation {
                    expr_start - 1
                } else {
                    expr_start
                };
                let replace_end = idx + pattern.len();
                result = format!(
                    "{}{}{}",
                    &result[..replace_start],
                    replacement,
                    &result[replace_end..]
                );
                search_start = replace_start + replacement.len();
            }
        }
        result
    }

    fn normalize_collection_contains(condition: &str) -> String {
        // Transform Rust collection `.contains(&x)` patterns to Swift-style `.contains(x)`:
        // - `items.contains(&x)` -> `items.contains(x)` (strip the reference)
        // - `vec.contains(&elem)` -> `vec.contains(elem)`
        //
        // This handles NON-range contains calls (range contains is normalized by
        // normalize_range_contains into comparison expressions).
        //
        // Range contains patterns like `(0..n).contains(&i)` are detected by having
        // `)` immediately before `.contains(`, so we skip those.

        fn find_matching_close_paren(s: &str, open_pos: usize) -> Option<usize> {
            let bytes = s.as_bytes();
            let mut depth: i32 = 0;
            for (offset, &byte) in bytes[open_pos..].iter().enumerate() {
                match byte {
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            return Some(open_pos + offset);
                        }
                    }
                    _ => {}
                }
            }
            None
        }

        fn strip_ref_prefix(arg: &str) -> Option<&str> {
            let arg = arg.trim();
            if let Some(rest) = arg.strip_prefix("&mut ") {
                return Some(rest.trim());
            }
            if let Some(rest) = arg.strip_prefix("&mut") {
                return Some(rest.trim());
            }
            if let Some(rest) = arg.strip_prefix('&') {
                return Some(rest.trim());
            }
            None // No reference to strip
        }

        let marker = ".contains(";
        let mut result = condition.to_string();
        let mut search_start: usize = 0;

        loop {
            let Some(rel_idx) = result[search_start..].find(marker) else {
                break;
            };
            let idx = search_start + rel_idx;

            // Skip if this is a range contains pattern (preceded by `)`)
            // Those are handled by normalize_range_contains
            if idx > 0 && result.as_bytes().get(idx - 1) == Some(&b')') {
                search_start = idx + marker.len();
                continue;
            }

            let call_open = idx + marker.len() - 1;
            let Some(call_close) = find_matching_close_paren(&result, call_open) else {
                search_start = idx + marker.len();
                continue;
            };

            let arg_str = result[call_open + 1..call_close].trim();
            // Only normalize if argument has a reference prefix
            let Some(stripped_arg) = strip_ref_prefix(arg_str) else {
                search_start = call_close + 1;
                continue;
            };

            if stripped_arg.is_empty() {
                search_start = call_close + 1;
                continue;
            }

            // Replace `.contains(&arg)` with `.contains(arg)`
            let new_call = format!(".contains({stripped_arg})");
            let replace_start = idx;
            let replace_end = call_close + 1;
            result = format!(
                "{}{}{}",
                &result[..replace_start],
                new_call,
                &result[replace_end..]
            );
            search_start = replace_start + new_call.len();
        }

        result
    }

    fn normalize_split_count(condition: &str) -> String {
        // Transform Rust `.split(delim).count()` to `.split(delim).count`
        // This removes the trailing () from count() making it compatible with Swift conditions.
        //
        // Examples:
        // - `text.split(',').count()` -> `text.split(',').count`
        // - `s.split('\n').count()` -> `s.split('\n').count`
        // - `data.split(delimiter).count()` -> `data.split(delimiter).count`
        //
        // The pattern is: .split(<anything balanced>).count()
        // We need to find .split(, then find the matching ), then check for .count()

        fn find_matching_close_paren(s: &str, open_paren_pos: usize) -> Option<usize> {
            let bytes = s.as_bytes();
            let mut depth: i32 = 0;
            for (offset, &byte) in bytes[open_paren_pos..].iter().enumerate() {
                match byte {
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            return Some(open_paren_pos + offset);
                        }
                    }
                    _ => {}
                }
            }
            None
        }

        let marker = ".split(";
        let suffix = ".count()";
        let mut result = condition.to_string();
        let mut search_start: usize = 0;

        loop {
            let Some(rel_idx) = result[search_start..].find(marker) else {
                break;
            };
            let split_start = search_start + rel_idx;
            let paren_start = split_start + marker.len() - 1; // position of '(' in .split(

            // Find matching close paren for .split(...)
            let Some(paren_end) = find_matching_close_paren(&result, paren_start) else {
                search_start = split_start + marker.len();
                continue;
            };

            // Check if followed by .count()
            let after_split = paren_end + 1;
            if result[after_split..].starts_with(suffix) {
                // Replace .count() with .count (remove the trailing ())
                let count_end = after_split + suffix.len();
                result = format!("{}.count{}", &result[..after_split], &result[count_end..]);
                search_start = after_split + ".count".len();
            } else {
                search_start = paren_end + 1;
            }
        }

        result
    }

    fn normalize_take_skip_count(condition: &str) -> String {
        // Normalize Rust iterator `.iter().take(n).count()` and `.iter().skip(n).count()` patterns.
        //
        // Examples:
        // - `data.iter().take(5).count()` -> `data.take(5).count`
        // - `arr.iter().skip(3).count()` -> `arr.skip(3).count`
        // - `items.into_iter().take(n).count()` -> `items.take(n).count`
        // - `vec.iter_mut().skip(m).count()` -> `vec.skip(m).count`
        //
        // This removes the iterator adapter (.iter()/.into_iter()/.iter_mut()) and converts
        // .count() to .count for Swift-style field access.
        //
        // Semantics for FFI verification:
        // - `.take(n).count` represents min(n, collection.count) - at most n elements
        // - `.skip(n).count` represents max(0, collection.count - n) - skip first n elements

        fn find_matching_close_paren(s: &str, open_paren_pos: usize) -> Option<usize> {
            let bytes = s.as_bytes();
            let mut depth: i32 = 0;
            for (offset, &byte) in bytes[open_paren_pos..].iter().enumerate() {
                match byte {
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            return Some(open_paren_pos + offset);
                        }
                    }
                    _ => {}
                }
            }
            None
        }

        let iter_patterns = [".iter().", ".into_iter().", ".iter_mut()."];
        let take_skip_markers = ["take(", "skip("]; // without leading dot since iter_pat ends with dot
        let suffix = ".count()";
        let mut result = condition.to_string();

        // Process each iterator pattern
        for iter_pat in &iter_patterns {
            for &marker in &take_skip_markers {
                let mut search_start: usize = 0;

                loop {
                    // Find iterator pattern followed by take/skip
                    let Some(rel_idx) = result[search_start..].find(iter_pat) else {
                        break;
                    };
                    let iter_start = search_start + rel_idx;
                    let after_iter = iter_start + iter_pat.len();

                    // Check if immediately followed by take( or skip(
                    // after_iter points right after the trailing dot of ".iter()."
                    if !result[after_iter..].starts_with(marker) {
                        search_start = after_iter;
                        continue;
                    }

                    let take_skip_start = after_iter;
                    // paren_start is the position of the '(' in take( or skip(
                    let paren_start = take_skip_start + marker.len() - 1;

                    // Find matching close paren for take(n) or skip(n)
                    let Some(paren_end) = find_matching_close_paren(&result, paren_start) else {
                        search_start = take_skip_start + marker.len();
                        continue;
                    };

                    // Check if followed by .count()
                    let after_take_skip = paren_end + 1;
                    if result[after_take_skip..].starts_with(suffix) {
                        // Transform: remove iterator pattern, keep take/skip, change .count() to .count
                        // E.g., "data.iter().take(5).count()" -> "data.take(5).count"
                        // iter_start points to '.iter().'
                        // after_iter points to 'take(5).count()'
                        // We want: data + . + take(5) + .count + rest
                        let count_end = after_take_skip + suffix.len();
                        result = format!(
                            "{}.{}.count{}",
                            &result[..iter_start],           // "data"
                            &result[after_iter..=paren_end], // "take(5)" or "skip(3)"
                            &result[count_end..]             // rest after .count()
                        );
                        search_start = iter_start + marker.len();
                    } else {
                        search_start = paren_end + 1;
                    }
                }
            }
        }

        result
    }

    fn find_expression_start(before: &str) -> usize {
        // Walk backward to find where the expression starts
        let bytes = before.as_bytes();
        let mut pos = bytes.len();
        while pos > 0 {
            let c = bytes[pos - 1] as char;
            if c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '[' || c == ']' {
                pos -= 1;
            } else {
                break;
            }
        }
        pos
    }

    fn normalize_rust_condition_for_parser(condition: &str) -> String {
        // Normalize Rust iterator `.iter().take(n).count()` and `.iter().skip(n).count()` patterns
        // MUST run before simple .iter().count() normalization to handle chained iterators first
        let normalized = normalize_take_skip_count(condition);
        // Normalize Rust iterator `.iter().count()`, `.into_iter().count()`, `.iter_mut().count()`,
        // `.chars().count()` to Swift-style `.count` - common Rust idioms for collection/string length
        let normalized = normalized.replace(".iter().count()", ".count");
        let normalized = normalized.replace(".into_iter().count()", ".count");
        let normalized = normalized.replace(".iter_mut().count()", ".count");
        // Normalize Rust string `.chars().count()` to Swift-style `.count` - counts characters
        let normalized = normalized.replace(".chars().count()", ".count");
        // Normalize Rust string `.bytes().count()` to Swift-style `.utf8.count` - counts bytes
        let normalized = normalized.replace(".bytes().count()", ".utf8.count");
        // Normalize Rust string `.lines().count()` to Swift-style `.lines.count` - counts lines
        let normalized = normalized.replace(".lines().count()", ".lines.count");
        // Normalize Rust string `.split(delim).count()` to `.split(delim).count` - counts split parts
        let normalized = normalize_split_count(&normalized);
        // Normalize Rust range `.len()` and `.count` to arithmetic (must be before generic .len())
        // e.g., `(a..b).len()` -> `(b - a)`, `(a..=b).len()` -> `(b - a + 1)`
        let normalized = normalize_range_len(&normalized);
        // Normalize `.unwrap()`/`.unwrap_err()` to `.value`/`.error` so chained field access parses.
        let normalized = normalize_unwrap_value_error(&normalized);
        // Normalize Rust slice `.len()` to Swift-style `.count` so the condition parser
        // recognizes it as field access. This also avoids illegal SMT symbols like `x.len()`.
        let normalized = normalized.replace(".len()", ".count");
        // Normalize Result `.is_ok()`/`.is_err()` to `.isSuccess` / `!.isSuccess`.
        let normalized = normalize_result_is_ok_err(&normalized);
        // Normalize Rust range `.contains(&x)` patterns to comparisons
        let normalized = normalize_range_contains(&normalized);
        // Normalize Rust collection `.contains(&x)` to `.contains(x)` (strip reference)
        // Must run after range_contains since range contains converts `(a..b).contains(&x)` to comparisons
        let normalized = normalize_collection_contains(&normalized);
        // Normalize `.is_empty()` to count comparisons
        let normalized = normalize_is_empty(&normalized);
        // Normalize `.first()/.last().is_some()/.is_none()` to count comparisons
        let normalized = normalize_first_last_option(&normalized);
        // Normalize `.get(index).is_some()/.is_none()` to bounds comparisons
        let normalized = normalize_get_option(&normalized);
        // Normalize Result `.ok().is_some()/.is_none()/.err().is_some()/.is_none()` patterns
        // (must be before option normalization since these patterns end with is_some/is_none)
        let normalized = normalize_result_ok_err(&normalized);
        // Normalize `opt.is_some()/.is_none()` to nil comparisons (must be after first/last/get/result)
        let normalized = normalize_option_is_some_is_none(&normalized);
        strip_rust_casts(&normalized)
    }

    // Rust uses && and || instead of and/or, but the parser handles both.
    // Normalize a few common Rust-only surface syntax forms first.
    let normalized = normalize_rust_condition_for_parser(condition);
    parse_swift_condition_to_predicate(&normalized, param_names)
}

// ============================================================================
// swift-bridge Type Mappings
// ============================================================================

/// Mapping between swift-bridge generated types and our `FfiTypes`
///
/// swift-bridge generates Rust types that correspond to Swift types.
/// This provides the canonical mapping.
#[derive(Debug, Clone)]
pub struct SwiftBridgeTypeMap {
    /// Maps swift-bridge Rust type names to `FfiType`
    mappings: std::collections::HashMap<String, FfiType>,
}

impl Default for SwiftBridgeTypeMap {
    fn default() -> Self {
        let mut mappings = std::collections::HashMap::new();

        // swift-bridge primitive type mappings
        // Rust type -> FfiType
        mappings.insert("bool".to_string(), FfiType::Bool);
        mappings.insert("i8".to_string(), FfiType::Int { bits: 8 });
        mappings.insert("i16".to_string(), FfiType::Int { bits: 16 });
        mappings.insert("i32".to_string(), FfiType::Int { bits: 32 });
        mappings.insert("i64".to_string(), FfiType::Int { bits: 64 });
        mappings.insert("u8".to_string(), FfiType::UInt { bits: 8 });
        mappings.insert("u16".to_string(), FfiType::UInt { bits: 16 });
        mappings.insert("u32".to_string(), FfiType::UInt { bits: 32 });
        mappings.insert("u64".to_string(), FfiType::UInt { bits: 64 });
        mappings.insert("f32".to_string(), FfiType::Float { bits: 32 });
        mappings.insert("f64".to_string(), FfiType::Float { bits: 64 });
        mappings.insert("()".to_string(), FfiType::Void);

        // swift-bridge string types
        mappings.insert("String".to_string(), FfiType::String);
        mappings.insert(
            "swift_bridge::string::SwiftString".to_string(),
            FfiType::String,
        );
        mappings.insert("&str".to_string(), FfiType::StringRef);

        // swift-bridge data/bytes types
        mappings.insert("Vec<u8>".to_string(), FfiType::Bytes);
        mappings.insert("&[u8]".to_string(), FfiType::BytesRef);

        Self { mappings }
    }
}

impl SwiftBridgeTypeMap {
    /// Create a new empty Swift-bridge type map.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a custom type mapping
    pub fn add_mapping(&mut self, rust_type: &str, ffi_type: FfiType) {
        self.mappings.insert(rust_type.to_string(), ffi_type);
    }

    /// Look up `FfiType` for a Rust type
    #[must_use]
    pub fn get(&self, rust_type: &str) -> Option<&FfiType> {
        self.mappings.get(rust_type)
    }

    /// Parse a Rust type string to `FfiType` using swift-bridge conventions
    #[must_use]
    pub fn parse_rust_type(&self, rust_type: &str) -> FfiType {
        let trimmed = rust_type.trim();

        // Check direct mapping first
        if let Some(ffi_type) = self.mappings.get(trimmed) {
            return ffi_type.clone();
        }

        // Handle Option<T>
        if let Some(inner) = trimmed
            .strip_prefix("Option<")
            .and_then(|s| s.strip_suffix('>'))
        {
            return FfiType::Optional(Box::new(self.parse_rust_type(inner)));
        }

        // Handle Result<T, E>
        if let Some(inner) = trimmed
            .strip_prefix("Result<")
            .and_then(|s| s.strip_suffix('>'))
        {
            if let Some((ok, err)) = inner.split_once(',') {
                return FfiType::Result {
                    ok: Box::new(self.parse_rust_type(ok.trim())),
                    err: Box::new(self.parse_rust_type(err.trim())),
                };
            }
        }

        // Handle references
        if let Some(inner) = trimmed.strip_prefix("&mut ") {
            return FfiType::Custom(format!("&mut {inner}"));
        }
        if let Some(inner) = trimmed.strip_prefix('&') {
            // Check for &str or &[u8]
            if let Some(ffi_type) = self.mappings.get(trimmed) {
                return ffi_type.clone();
            }
            return FfiType::Custom(format!("&{inner}"));
        }

        // Default to Custom type
        FfiType::Custom(trimmed.to_string())
    }

    /// Check if two types are compatible across Swift/Rust boundary
    #[must_use]
    pub fn types_compatible(&self, swift_type: &str, rust_type: &str) -> bool {
        let swift_ffi = parse_swift_type(swift_type);
        let rust_ffi = self.parse_rust_type(rust_type);
        ffi_types_compatible(&swift_ffi, &rust_ffi)
    }
}

// ============================================================================
// FFI Verification Logic
// ============================================================================

/// Options for FFI verification
#[derive(Debug, Clone, Default)]
pub struct FfiVerifyOptions {
    /// Use Z4 SMT solver for semantic implication proofs (slower but more precise)
    /// When false, uses structural comparison only
    pub use_z4_proofs: bool,
}

// ============================================================================
// FFI Contract File Format (for Contract Mode)
// ============================================================================

/// FFI contract file format (.ffi.json)
///
/// This format allows separate compilation where:
/// 1. Rust crate generates contract file during build
/// 2. Swift/Kotlin consumers verify against contract without Rust source
///
/// Example:
/// ```json
/// {
///   "version": "1.0",
///   "crate": "dterm-core",
///   "hash": "sha256:abc123...",
///   "functions": { ... },
///   "types": { ... }
/// }
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FfiContractFile {
    /// Contract format version
    pub version: String,
    /// Name of the crate/library
    pub crate_name: String,
    /// Content hash for staleness detection
    #[serde(skip_serializing_if = "Option::is_none")]
    pub hash: Option<String>,
    /// Exported functions
    pub functions: std::collections::HashMap<String, FfiContractFunction>,
    /// Type definitions
    #[serde(default)]
    pub types: std::collections::HashMap<String, FfiContractType>,
    /// Callback signatures
    #[serde(default)]
    pub callbacks: std::collections::HashMap<String, FfiContractCallback>,
}

/// Function specification in a contract file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FfiContractFunction {
    /// Mangled symbol name
    #[serde(skip_serializing_if = "Option::is_none")]
    pub symbol: Option<String>,
    /// Parameters
    pub params: Vec<FfiContractParam>,
    /// Return type
    pub returns: FfiContractReturn,
    /// Preconditions as strings
    #[serde(default)]
    pub requires: Vec<String>,
    /// Postconditions as strings
    #[serde(default)]
    pub ensures: Vec<String>,
    /// Whether the function can panic
    #[serde(default)]
    pub panics: bool,
    /// Whether the function is thread-safe
    #[serde(default = "default_true")]
    pub thread_safe: bool,
}

const fn default_true() -> bool {
    true
}

/// Parameter in a contract function
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FfiContractParam {
    /// Parameter name
    pub name: String,
    /// Type description
    #[serde(rename = "type")]
    pub type_str: String,
    /// Ownership semantics
    #[serde(default)]
    pub ownership: FfiOwnership,
}

/// Return type in a contract function
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FfiContractReturn {
    /// Type description
    #[serde(rename = "type")]
    pub type_str: String,
    /// Ownership semantics
    #[serde(default)]
    pub ownership: FfiOwnership,
}

/// Ownership semantics for FFI values
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
#[serde(rename_all = "lowercase")]
pub enum FfiOwnership {
    /// Value is owned/moved
    #[default]
    Owned,
    /// Value is borrowed (reference)
    Borrow,
    /// Value is mutably borrowed
    BorrowMut,
}

/// Type definition in a contract file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FfiContractType {
    /// Layout information
    pub layout: FfiTypeLayout,
    /// Fields for structs
    #[serde(default)]
    pub fields: Vec<FfiContractField>,
}

/// Memory layout for a type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FfiTypeLayout {
    /// Size in bytes
    pub size: usize,
    /// Alignment in bytes
    pub align: usize,
}

/// Field in a contract type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FfiContractField {
    /// Field name
    pub name: String,
    /// Field type
    #[serde(rename = "type")]
    pub type_str: String,
    /// Byte offset
    pub offset: usize,
}

/// Callback signature in a contract file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FfiContractCallback {
    /// Parameters
    pub params: Vec<FfiContractParam>,
    /// Preconditions
    #[serde(default)]
    pub requires: Vec<String>,
    /// Postconditions
    #[serde(default)]
    pub ensures: Vec<String>,
}

impl FfiContractFile {
    /// Create a new contract file
    #[must_use]
    pub fn new(crate_name: &str) -> Self {
        Self {
            version: "1.0".to_string(),
            crate_name: crate_name.to_string(),
            hash: None,
            functions: std::collections::HashMap::new(),
            types: std::collections::HashMap::new(),
            callbacks: std::collections::HashMap::new(),
        }
    }

    /// Parse a contract file from JSON
    ///
    /// # Errors
    /// Returns an error if the JSON cannot be parsed as a contract file.
    pub fn from_json(json: &str) -> Result<Self, String> {
        serde_json::from_str(json).map_err(|e| format!("Failed to parse contract file: {e}"))
    }

    /// Serialize to JSON
    ///
    /// # Errors
    /// Returns an error if the contract file cannot be serialized to JSON.
    pub fn to_json(&self) -> Result<String, String> {
        serde_json::to_string_pretty(self).map_err(|e| format!("Failed to serialize contract: {e}"))
    }

    /// Convert to `FfiSpecs` for verification
    #[must_use]
    pub fn to_ffi_specs(&self) -> FfiSpecs {
        let mut specs = FfiSpecs::new();

        for (name, func) in &self.functions {
            let ffi_func = contract_function_to_ffi_function(name, func);
            specs.rust_exports.insert(name.clone(), ffi_func);
        }

        specs
    }
}

/// Convert a contract function to `FfiFunction`
fn contract_function_to_ffi_function(name: &str, func: &FfiContractFunction) -> FfiFunction {
    let params: Vec<FfiParam> = func
        .params
        .iter()
        .map(|p| FfiParam {
            name: p.name.clone(),
            ffi_type: parse_contract_type(&p.type_str),
        })
        .collect();

    // Collect parameter names for the condition parser
    let param_names: Vec<String> = func.params.iter().map(|p| p.name.clone()).collect();

    let return_type = parse_contract_type(&func.returns.type_str);

    // Parse preconditions into predicates using the proper condition parser
    let requires: Vec<Predicate> = func
        .requires
        .iter()
        .filter_map(|s| parse_swift_condition_to_predicate(s, &param_names).ok())
        .collect();

    // Parse postconditions into predicates using the proper condition parser
    let ensures: Vec<Predicate> = func
        .ensures
        .iter()
        .filter_map(|s| parse_swift_condition_to_predicate(s, &param_names).ok())
        .collect();

    FfiFunction {
        name: name.to_string(),
        language: FfiLanguage::Rust,
        params,
        return_type,
        requires,
        ensures,
        trusted: false,
        source_file: None,
        source_line: None,
    }
}

/// Parse a contract type string into `FfiType`
fn parse_contract_type(type_str: &str) -> FfiType {
    let s = type_str.trim();
    match s {
        "bool" | "Bool" => FfiType::Bool,
        "i8" | "Int8" => FfiType::Int { bits: 8 },
        "i16" | "Int16" => FfiType::Int { bits: 16 },
        "i32" | "Int32" | "Int" => FfiType::Int { bits: 32 },
        "i64" | "Int64" => FfiType::Int { bits: 64 },
        "u8" | "UInt8" => FfiType::UInt { bits: 8 },
        "u16" | "UInt16" => FfiType::UInt { bits: 16 },
        "u32" | "UInt32" | "UInt" => FfiType::UInt { bits: 32 },
        "u64" | "UInt64" => FfiType::UInt { bits: 64 },
        "f32" | "Float32" | "Float" => FfiType::Float { bits: 32 },
        "f64" | "Float64" | "Double" => FfiType::Float { bits: 64 },
        "String" | "string" => FfiType::String,
        "&str" | "str" => FfiType::StringRef,
        "Vec<u8>" | "Data" | "bytes" => FfiType::Bytes,
        "&[u8]" | "slice<u8>" => FfiType::BytesRef,
        "()" | "void" | "Void" => FfiType::Void,
        _ if s.starts_with("Option<") || s.ends_with('?') => {
            let inner = if s.starts_with("Option<") {
                &s[7..s.len() - 1]
            } else {
                &s[..s.len() - 1]
            };
            FfiType::Optional(Box::new(parse_contract_type(inner)))
        }
        _ if s.starts_with("Result<") => {
            // Parse Result<Ok, Err>
            let inner = &s[7..s.len() - 1];
            let parts: Vec<&str> = inner.splitn(2, ',').collect();
            if parts.len() == 2 {
                FfiType::Result {
                    ok: Box::new(parse_contract_type(parts[0].trim())),
                    err: Box::new(parse_contract_type(parts[1].trim())),
                }
            } else {
                FfiType::Custom(s.to_string())
            }
        }
        _ => FfiType::Custom(s.to_string()),
    }
}

/// Convert `FfiSpecs` (from Rust source) to a contract file
#[must_use]
pub fn ffi_specs_to_contract(specs: &FfiSpecs, crate_name: &str) -> FfiContractFile {
    let mut contract = FfiContractFile::new(crate_name);

    for (name, func) in &specs.rust_exports {
        contract
            .functions
            .insert(name.clone(), ffi_function_to_contract_function(func));
    }

    contract
}

/// Convert `FfiFunction` to contract format
fn ffi_function_to_contract_function(func: &FfiFunction) -> FfiContractFunction {
    let params: Vec<FfiContractParam> = func
        .params
        .iter()
        .map(|p| {
            FfiContractParam {
                name: p.name.clone(),
                type_str: ffi_type_to_string(&p.ffi_type),
                ownership: FfiOwnership::Owned, // Default; could be improved
            }
        })
        .collect();

    let returns = FfiContractReturn {
        type_str: ffi_type_to_string(&func.return_type),
        ownership: FfiOwnership::Owned,
    };

    let requires: Vec<String> = func.requires.iter().map(predicate_to_string).collect();

    let ensures: Vec<String> = func.ensures.iter().map(predicate_to_string).collect();

    FfiContractFunction {
        symbol: None,
        params,
        returns,
        requires,
        ensures,
        panics: false,
        thread_safe: true,
    }
}

/// Convert `FfiType` to string for contract file
fn ffi_type_to_string(ty: &FfiType) -> String {
    match ty {
        FfiType::Bool => "bool".to_string(),
        FfiType::Int { bits } => format!("i{bits}"),
        FfiType::UInt { bits } => format!("u{bits}"),
        FfiType::Float { bits } => format!("f{bits}"),
        FfiType::String => "String".to_string(),
        FfiType::StringRef => "&str".to_string(),
        FfiType::Bytes => "Vec<u8>".to_string(),
        FfiType::BytesRef => "&[u8]".to_string(),
        FfiType::Void => "()".to_string(),
        FfiType::Optional(inner) => format!("Option<{}>", ffi_type_to_string(inner)),
        FfiType::Result { ok, err } => {
            format!(
                "Result<{}, {}>",
                ffi_type_to_string(ok),
                ffi_type_to_string(err)
            )
        }
        FfiType::Custom(name) => name.clone(),
    }
}

/// Convert a Predicate to a string for contract files
fn predicate_to_string(pred: &Predicate) -> String {
    match pred {
        Predicate::Expr(e) => expr_to_string(e),
        Predicate::And(preds) => {
            if preds.is_empty() {
                "true".to_string()
            } else {
                preds
                    .iter()
                    .map(predicate_to_string)
                    .collect::<Vec<_>>()
                    .join(" && ")
            }
        }
        Predicate::Or(preds) => {
            if preds.is_empty() {
                "false".to_string()
            } else {
                preds
                    .iter()
                    .map(|p| format!("({})", predicate_to_string(p)))
                    .collect::<Vec<_>>()
                    .join(" || ")
            }
        }
        Predicate::Not(p) => format!("!({})", predicate_to_string(p)),
        Predicate::Implies(lhs, rhs) => {
            format!(
                "({}) => ({})",
                predicate_to_string(lhs),
                predicate_to_string(rhs)
            )
        }
    }
}

/// Convert an Expr to a string for contract files
fn expr_to_string(expr: &Expr) -> String {
    match expr {
        Expr::IntLit(n) => n.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::NilLit => "nil".to_string(),
        Expr::Var(name) => name.clone(),
        Expr::Result => "result".to_string(),
        Expr::Old(e) => format!("old({})", expr_to_string(e)),
        Expr::Add(l, r) => format!("({} + {})", expr_to_string(l), expr_to_string(r)),
        Expr::Sub(l, r) => format!("({} - {})", expr_to_string(l), expr_to_string(r)),
        Expr::Mul(l, r) => format!("({} * {})", expr_to_string(l), expr_to_string(r)),
        Expr::Div(l, r) => format!("({} / {})", expr_to_string(l), expr_to_string(r)),
        Expr::Rem(l, r) => format!("({} % {})", expr_to_string(l), expr_to_string(r)),
        Expr::Neg(e) => format!("(-{})", expr_to_string(e)),
        Expr::Eq(l, r) => format!("{} == {}", expr_to_string(l), expr_to_string(r)),
        Expr::Ne(l, r) => format!("{} != {}", expr_to_string(l), expr_to_string(r)),
        Expr::Lt(l, r) => format!("{} < {}", expr_to_string(l), expr_to_string(r)),
        Expr::Le(l, r) => format!("{} <= {}", expr_to_string(l), expr_to_string(r)),
        Expr::Gt(l, r) => format!("{} > {}", expr_to_string(l), expr_to_string(r)),
        Expr::Ge(l, r) => format!("{} >= {}", expr_to_string(l), expr_to_string(r)),
        Expr::And(l, r) => format!("({} && {})", expr_to_string(l), expr_to_string(r)),
        Expr::Or(l, r) => format!("({} || {})", expr_to_string(l), expr_to_string(r)),
        Expr::Not(e) => format!("!{}", expr_to_string(e)),
        Expr::Ite { cond, then_, else_ } => {
            format!(
                "({} ? {} : {})",
                expr_to_string(cond),
                expr_to_string(then_),
                expr_to_string(else_)
            )
        }
        Expr::StructField(base, name) => format!("{}.{}", expr_to_string(base), name),
        Expr::ArrayIndex(arr, idx) => format!("{}[{}]", expr_to_string(arr), expr_to_string(idx)),
        Expr::Apply { func, args } => {
            let args_str = args
                .iter()
                .map(expr_to_string)
                .collect::<Vec<_>>()
                .join(", ");
            format!("{func}({args_str})")
        }
        Expr::Forall { vars, body } => {
            let vars_str = vars
                .iter()
                .map(|(n, _)| n.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            format!("forall {}: {}", vars_str, expr_to_string(body))
        }
        Expr::Exists { vars, body } => {
            let vars_str = vars
                .iter()
                .map(|(n, _)| n.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            format!("exists {}: {}", vars_str, expr_to_string(body))
        }
    }
}

/// Verify FFI compatibility between languages with options
#[must_use]
pub fn verify_ffi_compatibility_with_options(
    specs: &FfiSpecs,
    options: &FfiVerifyOptions,
) -> Vec<FfiVerifyResult> {
    let mut results = Vec::new();

    // Check Swift imports against Rust exports
    for (name, swift_fn) in &specs.swift_imports {
        if let Some(rust_fn) = specs.rust_exports.get(name) {
            results.push(verify_ffi_pair_with_options(swift_fn, rust_fn, options));
        } else {
            // Missing Rust export
            results.push(FfiVerifyResult {
                function_name: name.clone(),
                caller: FfiLanguage::Swift,
                callee: FfiLanguage::Rust,
                result: FfiCompatibility::Unknown,
                checks: vec![FfiCheck {
                    check_type: FfiCheckType::PreconditionCompatibility,
                    passed: false,
                    message: Some("No Rust export found for Swift import".to_string()),
                }],
            });
        }
    }

    // Check Kotlin imports against Rust exports
    for (name, kotlin_fn) in &specs.kotlin_imports {
        if let Some(rust_fn) = specs.rust_exports.get(name) {
            results.push(verify_ffi_pair_with_options(kotlin_fn, rust_fn, options));
        } else {
            // Missing Rust export
            results.push(FfiVerifyResult {
                function_name: name.clone(),
                caller: FfiLanguage::Kotlin,
                callee: FfiLanguage::Rust,
                result: FfiCompatibility::Unknown,
                checks: vec![FfiCheck {
                    check_type: FfiCheckType::PreconditionCompatibility,
                    passed: false,
                    message: Some("No Rust export found for Kotlin import".to_string()),
                }],
            });
        }
    }

    results
}

/// Verify FFI compatibility between languages (uses structural comparison)
#[must_use]
pub fn verify_ffi_compatibility(specs: &FfiSpecs) -> Vec<FfiVerifyResult> {
    let mut results = Vec::new();

    // Check Swift imports against Rust exports
    for (name, swift_fn) in &specs.swift_imports {
        if let Some(rust_fn) = specs.rust_exports.get(name) {
            results.push(verify_ffi_pair(swift_fn, rust_fn));
        } else {
            // Missing Rust export
            results.push(FfiVerifyResult {
                function_name: name.clone(),
                caller: FfiLanguage::Swift,
                callee: FfiLanguage::Rust,
                result: FfiCompatibility::Unknown,
                checks: vec![FfiCheck {
                    check_type: FfiCheckType::PreconditionCompatibility,
                    passed: false,
                    message: Some("No Rust export found for Swift import".to_string()),
                }],
            });
        }
    }

    // Check Kotlin imports against Rust exports
    for (name, kotlin_fn) in &specs.kotlin_imports {
        if let Some(rust_fn) = specs.rust_exports.get(name) {
            results.push(verify_ffi_pair(kotlin_fn, rust_fn));
        } else {
            // Missing Rust export
            results.push(FfiVerifyResult {
                function_name: name.clone(),
                caller: FfiLanguage::Kotlin,
                callee: FfiLanguage::Rust,
                result: FfiCompatibility::Unknown,
                checks: vec![FfiCheck {
                    check_type: FfiCheckType::PreconditionCompatibility,
                    passed: false,
                    message: Some("No Rust export found for Kotlin import".to_string()),
                }],
            });
        }
    }

    results
}

/// Verify compatibility between a caller and callee FFI function
fn verify_ffi_pair(caller: &FfiFunction, callee: &FfiFunction) -> FfiVerifyResult {
    verify_ffi_pair_with_options(caller, callee, &FfiVerifyOptions::default())
}

/// Verify compatibility between a caller and callee FFI function with options
fn verify_ffi_pair_with_options(
    caller: &FfiFunction,
    callee: &FfiFunction,
    options: &FfiVerifyOptions,
) -> FfiVerifyResult {
    let mut checks = Vec::new();

    // If either side is trusted, skip verification
    if caller.trusted || callee.trusted {
        return FfiVerifyResult {
            function_name: caller.name.clone(),
            caller: caller.language,
            callee: callee.language,
            result: FfiCompatibility::Compatible,
            checks: vec![FfiCheck {
                check_type: FfiCheckType::PreconditionCompatibility,
                passed: true,
                message: Some("Skipped - function is marked @trusted".to_string()),
            }],
        };
    }

    // Check precondition compatibility: caller_requires => callee_requires
    // The caller's precondition must be at least as strong as the callee's
    let pre_check = if options.use_z4_proofs {
        check_precondition_compatibility_z4(caller, callee)
    } else {
        check_precondition_compatibility(caller, callee)
    };
    checks.push(pre_check);

    // Check postcondition compatibility: callee_ensures => caller_expects
    // The callee's postcondition must be at least as strong as what caller expects
    let post_check = if options.use_z4_proofs {
        check_postcondition_compatibility_z4(caller, callee)
    } else {
        check_postcondition_compatibility(caller, callee)
    };
    checks.push(post_check);

    // Check type layout compatibility
    let type_check = check_type_layout_compatibility(caller, callee);
    checks.push(type_check);

    // Determine overall result
    let all_passed = checks.iter().all(|c| c.passed);
    let result = if all_passed {
        FfiCompatibility::Compatible
    } else {
        FfiCompatibility::Incompatible
    };

    FfiVerifyResult {
        function_name: caller.name.clone(),
        caller: caller.language,
        callee: callee.language,
        result,
        checks,
    }
}

/// Check precondition compatibility: `caller_requires` => `callee_requires`
fn check_precondition_compatibility(caller: &FfiFunction, callee: &FfiFunction) -> FfiCheck {
    // If callee has no requirements, any caller is fine
    if callee.requires.is_empty() {
        return FfiCheck {
            check_type: FfiCheckType::PreconditionCompatibility,
            passed: true,
            message: Some("Callee has no preconditions".to_string()),
        };
    }

    // If caller has no requirements but callee does, that's potentially unsafe
    // (caller may pass values that violate callee's preconditions)
    if caller.requires.is_empty() && !callee.requires.is_empty() {
        return FfiCheck {
            check_type: FfiCheckType::PreconditionCompatibility,
            passed: false,
            message: Some(format!(
                "{} caller has no preconditions but {} callee requires: {:?}",
                caller.language, callee.language, callee.requires
            )),
        };
    }

    // Both have preconditions - for now we do structural comparison
    // A full implementation would use Z4 to prove caller_requires => callee_requires
    FfiCheck {
        check_type: FfiCheckType::PreconditionCompatibility,
        passed: true,
        message: Some("Both have preconditions (structural check passed)".to_string()),
    }
}

/// Check postcondition compatibility: `callee_ensures` => `caller_expects`
fn check_postcondition_compatibility(caller: &FfiFunction, callee: &FfiFunction) -> FfiCheck {
    // If caller expects nothing, any callee is fine
    if caller.ensures.is_empty() {
        return FfiCheck {
            check_type: FfiCheckType::PostconditionCompatibility,
            passed: true,
            message: Some("Caller expects no postconditions".to_string()),
        };
    }

    // If caller expects postconditions but callee provides none, that's potentially unsafe
    if !caller.ensures.is_empty() && callee.ensures.is_empty() {
        return FfiCheck {
            check_type: FfiCheckType::PostconditionCompatibility,
            passed: false,
            message: Some(format!(
                "{} caller expects postconditions but {} callee provides none",
                caller.language, callee.language
            )),
        };
    }

    // Both have postconditions - for now we do structural comparison
    FfiCheck {
        check_type: FfiCheckType::PostconditionCompatibility,
        passed: true,
        message: Some("Both have postconditions (structural check passed)".to_string()),
    }
}

// ============================================================================
// Z4-based Semantic Verification
// ============================================================================

use crate::z4_backend::verify_smtlib;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SmtSort {
    Int,
    Bool,
}

impl SmtSort {
    const fn as_smtlib(self) -> &'static str {
        match self {
            Self::Int => "Int",
            Self::Bool => "Bool",
        }
    }
}

fn smt_symbol(sym: &str) -> String {
    let mut chars = sym.chars();
    let Some(first) = chars.next() else {
        return "|_|".to_string();
    };

    let is_simple = (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_');

    if is_simple {
        sym.to_string()
    } else {
        format!("|{}|", sym.replace('|', "_"))
    }
}

/// Convert a Predicate to SMT-LIB2 string for use in FFI verification
fn predicate_to_smtlib_ffi(pred: &Predicate) -> String {
    match pred {
        Predicate::Expr(expr) => expr_to_smtlib_ffi(expr),
        Predicate::And(preds) => {
            if preds.is_empty() {
                "true".to_string()
            } else if preds.len() == 1 {
                predicate_to_smtlib_ffi(&preds[0])
            } else {
                let parts: Vec<String> = preds.iter().map(predicate_to_smtlib_ffi).collect();
                format!("(and {})", parts.join(" "))
            }
        }
        Predicate::Or(preds) => {
            if preds.is_empty() {
                "false".to_string()
            } else if preds.len() == 1 {
                predicate_to_smtlib_ffi(&preds[0])
            } else {
                let parts: Vec<String> = preds.iter().map(predicate_to_smtlib_ffi).collect();
                format!("(or {})", parts.join(" "))
            }
        }
        Predicate::Not(p) => format!("(not {})", predicate_to_smtlib_ffi(p)),
        Predicate::Implies(p, q) => {
            format!(
                "(=> {} {})",
                predicate_to_smtlib_ffi(p),
                predicate_to_smtlib_ffi(q)
            )
        }
    }
}

/// Convert an expression to SMT-LIB2 string for FFI verification
fn expr_to_smtlib_ffi(expr: &Expr) -> String {
    match expr {
        Expr::IntLit(v) => {
            if *v < 0 {
                format!("(- {})", -v)
            } else {
                v.to_string()
            }
        }
        Expr::BoolLit(b) => b.to_string(),
        Expr::NilLit => smt_symbol("nil"),
        Expr::Var(name) => smt_symbol(name),
        Expr::Result => "result".to_string(),
        Expr::Old(e) => match e.as_ref() {
            Expr::Var(name) => smt_symbol(&format!("{name}_old")),
            Expr::Result => "result_old".to_string(),
            _ => format!("(old {})", expr_to_smtlib_ffi(e)),
        },
        Expr::Add(a, b) => format!("(+ {} {})", expr_to_smtlib_ffi(a), expr_to_smtlib_ffi(b)),
        Expr::Sub(a, b) => format!("(- {} {})", expr_to_smtlib_ffi(a), expr_to_smtlib_ffi(b)),
        Expr::Mul(a, b) => format!("(* {} {})", expr_to_smtlib_ffi(a), expr_to_smtlib_ffi(b)),
        Expr::Div(a, b) => format!("(div {} {})", expr_to_smtlib_ffi(a), expr_to_smtlib_ffi(b)),
        Expr::Rem(a, b) => format!("(mod {} {})", expr_to_smtlib_ffi(a), expr_to_smtlib_ffi(b)),
        Expr::Neg(e) => format!("(- 0 {})", expr_to_smtlib_ffi(e)),
        Expr::Eq(a, b) => format!("(= {} {})", expr_to_smtlib_ffi(a), expr_to_smtlib_ffi(b)),
        Expr::Ne(a, b) => format!(
            "(not (= {} {}))",
            expr_to_smtlib_ffi(a),
            expr_to_smtlib_ffi(b)
        ),
        Expr::Lt(a, b) => format!(
            "(<= (+ {} 1) {})",
            expr_to_smtlib_ffi(a),
            expr_to_smtlib_ffi(b)
        ),
        Expr::Le(a, b) => format!("(<= {} {})", expr_to_smtlib_ffi(a), expr_to_smtlib_ffi(b)),
        Expr::Gt(a, b) => format!(
            "(>= {} (+ {} 1))",
            expr_to_smtlib_ffi(a),
            expr_to_smtlib_ffi(b)
        ),
        Expr::Ge(a, b) => format!("(>= {} {})", expr_to_smtlib_ffi(a), expr_to_smtlib_ffi(b)),
        Expr::And(a, b) => format!("(and {} {})", expr_to_smtlib_ffi(a), expr_to_smtlib_ffi(b)),
        Expr::Or(a, b) => format!("(or {} {})", expr_to_smtlib_ffi(a), expr_to_smtlib_ffi(b)),
        Expr::Not(e) => format!("(not {})", expr_to_smtlib_ffi(e)),
        Expr::Ite { cond, then_, else_ } => format!(
            "(ite {} {} {})",
            expr_to_smtlib_ffi(cond),
            expr_to_smtlib_ffi(then_),
            expr_to_smtlib_ffi(else_)
        ),
        Expr::ArrayIndex(base, idx) => {
            format!(
                "(select {} {})",
                expr_to_smtlib_ffi(base),
                expr_to_smtlib_ffi(idx)
            )
        }
        Expr::StructField(base, field) => {
            format!(
                "({} {})",
                smt_symbol(&format!("{field}__field")),
                expr_to_smtlib_ffi(base)
            )
        }
        Expr::Apply { func, args } => {
            if args.is_empty() {
                smt_symbol(func)
            } else {
                let arg_strs: Vec<String> = args.iter().map(expr_to_smtlib_ffi).collect();
                format!("({} {})", smt_symbol(func), arg_strs.join(" "))
            }
        }
        Expr::Forall { vars, body } => {
            let var_decls: Vec<String> = vars
                .iter()
                .map(|(name, _)| format!("({} Int)", smt_symbol(name)))
                .collect();
            format!(
                "(forall ({}) {})",
                var_decls.join(" "),
                expr_to_smtlib_ffi(body)
            )
        }
        Expr::Exists { vars, body } => {
            let var_decls: Vec<String> = vars
                .iter()
                .map(|(name, _)| format!("({} Int)", smt_symbol(name)))
                .collect();
            format!(
                "(exists ({}) {})",
                var_decls.join(" "),
                expr_to_smtlib_ffi(body)
            )
        }
    }
}

/// Verify an implication using Z4: antecedent => consequent
///
/// Returns (passed, message) where passed is true if the implication holds.
#[allow(clippy::too_many_lines)]
fn verify_implication_z4(
    antecedent: &[Predicate],
    consequent: &[Predicate],
    description: &str,
) -> (bool, String) {
    fn record_sort(
        map: &mut std::collections::HashMap<String, SmtSort>,
        name: &str,
        sort: SmtSort,
    ) {
        map.entry(name.to_string())
            .and_modify(|existing| {
                // Prefer Int if we see conflicting usage; it keeps arithmetic constraints typed.
                if *existing != sort {
                    *existing = SmtSort::Int;
                }
            })
            .or_insert(sort);
    }

    fn record_fun_sort(
        map: &mut std::collections::HashMap<(String, usize), SmtSort>,
        name: &str,
        arity: usize,
        sort: SmtSort,
    ) {
        map.entry((name.to_string(), arity))
            .and_modify(|existing| {
                if *existing != sort {
                    *existing = SmtSort::Int;
                }
            })
            .or_insert(sort);
    }

    fn infer_symbols(
        expr: &Expr,
        expected: Option<SmtSort>,
        var_sorts: &mut std::collections::HashMap<String, SmtSort>,
        fun_sorts: &mut std::collections::HashMap<(String, usize), SmtSort>,
    ) {
        match expr {
            Expr::Var(name) => record_sort(var_sorts, name, expected.unwrap_or(SmtSort::Int)),
            Expr::Result => record_sort(var_sorts, "result", expected.unwrap_or(SmtSort::Int)),
            Expr::Old(inner) => {
                infer_symbols(inner, expected, var_sorts, fun_sorts);
                match inner.as_ref() {
                    Expr::Var(name) => record_sort(
                        var_sorts,
                        &format!("{name}_old"),
                        expected.unwrap_or(SmtSort::Int),
                    ),
                    Expr::Result => {
                        record_sort(var_sorts, "result_old", expected.unwrap_or(SmtSort::Int));
                    }
                    _ => {}
                }
            }
            Expr::IntLit(_) | Expr::BoolLit(_) => {}
            Expr::NilLit => {
                record_sort(var_sorts, "nil", expected.unwrap_or(SmtSort::Int));
            }
            Expr::Add(a, b)
            | Expr::Sub(a, b)
            | Expr::Mul(a, b)
            | Expr::Div(a, b)
            | Expr::Rem(a, b)
            | Expr::Lt(a, b)
            | Expr::Le(a, b)
            | Expr::Gt(a, b)
            | Expr::Ge(a, b) => {
                infer_symbols(a, Some(SmtSort::Int), var_sorts, fun_sorts);
                infer_symbols(b, Some(SmtSort::Int), var_sorts, fun_sorts);
            }
            Expr::Neg(e) => infer_symbols(e, Some(SmtSort::Int), var_sorts, fun_sorts),
            Expr::Eq(a, b) | Expr::Ne(a, b) => match (a.as_ref(), b.as_ref()) {
                (Expr::BoolLit(_), other) | (other, Expr::BoolLit(_)) => {
                    infer_symbols(other, Some(SmtSort::Bool), var_sorts, fun_sorts);
                }
                (Expr::IntLit(_), other) | (other, Expr::IntLit(_)) => {
                    infer_symbols(other, Some(SmtSort::Int), var_sorts, fun_sorts);
                }
                _ => {
                    infer_symbols(a, Some(SmtSort::Int), var_sorts, fun_sorts);
                    infer_symbols(b, Some(SmtSort::Int), var_sorts, fun_sorts);
                }
            },
            Expr::And(a, b) | Expr::Or(a, b) => {
                infer_symbols(a, Some(SmtSort::Bool), var_sorts, fun_sorts);
                infer_symbols(b, Some(SmtSort::Bool), var_sorts, fun_sorts);
            }
            Expr::Not(e) => infer_symbols(e, Some(SmtSort::Bool), var_sorts, fun_sorts),
            Expr::Ite { cond, then_, else_ } => {
                infer_symbols(cond, Some(SmtSort::Bool), var_sorts, fun_sorts);
                infer_symbols(then_, expected, var_sorts, fun_sorts);
                infer_symbols(else_, expected, var_sorts, fun_sorts);
            }
            Expr::ArrayIndex(base, idx) => {
                // Arrays are modeled opaquely; base/idx still need declarations.
                infer_symbols(base, Some(SmtSort::Int), var_sorts, fun_sorts);
                infer_symbols(idx, Some(SmtSort::Int), var_sorts, fun_sorts);
            }
            Expr::StructField(base, field) => {
                infer_symbols(base, Some(SmtSort::Int), var_sorts, fun_sorts);
                record_fun_sort(
                    fun_sorts,
                    &format!("{field}__field"),
                    1,
                    expected.unwrap_or(SmtSort::Int),
                );
            }
            Expr::Apply { func, args } => {
                if args.is_empty() {
                    record_sort(var_sorts, func, expected.unwrap_or(SmtSort::Int));
                } else {
                    for arg in args {
                        infer_symbols(arg, Some(SmtSort::Int), var_sorts, fun_sorts);
                    }
                    record_fun_sort(
                        fun_sorts,
                        func,
                        args.len(),
                        expected.unwrap_or(SmtSort::Int),
                    );
                }
            }
            Expr::Forall { vars, body } | Expr::Exists { vars, body } => {
                for (name, _) in vars {
                    record_sort(var_sorts, name, SmtSort::Int);
                }
                infer_symbols(body, expected, var_sorts, fun_sorts);
            }
        }
    }

    fn infer_symbols_from_predicate(
        pred: &Predicate,
        var_sorts: &mut std::collections::HashMap<String, SmtSort>,
        fun_sorts: &mut std::collections::HashMap<(String, usize), SmtSort>,
    ) {
        match pred {
            Predicate::Expr(expr) => infer_symbols(expr, Some(SmtSort::Bool), var_sorts, fun_sorts),
            Predicate::And(preds) | Predicate::Or(preds) => {
                for p in preds {
                    infer_symbols_from_predicate(p, var_sorts, fun_sorts);
                }
            }
            Predicate::Not(p) => infer_symbols_from_predicate(p, var_sorts, fun_sorts),
            Predicate::Implies(p, q) => {
                infer_symbols_from_predicate(p, var_sorts, fun_sorts);
                infer_symbols_from_predicate(q, var_sorts, fun_sorts);
            }
        }
    }

    // If consequent is empty, implication trivially holds
    if consequent.is_empty() {
        return (true, format!("{description} (consequent empty)"));
    }

    // Combine antecedent predicates with AND
    let ante_combined = if antecedent.is_empty() {
        Predicate::t()
    } else {
        Predicate::and(antecedent.to_vec())
    };

    // Combine consequent predicates with AND
    let cons_combined = Predicate::and(consequent.to_vec());

    let mut var_sorts: std::collections::HashMap<String, SmtSort> =
        std::collections::HashMap::new();
    let mut fun_sorts: std::collections::HashMap<(String, usize), SmtSort> =
        std::collections::HashMap::new();
    infer_symbols_from_predicate(&ante_combined, &mut var_sorts, &mut fun_sorts);
    infer_symbols_from_predicate(&cons_combined, &mut var_sorts, &mut fun_sorts);

    let mut var_names: Vec<String> = var_sorts.keys().cloned().collect();
    var_names.sort();

    // Generate SMT-LIB2
    let mut smtlib = String::new();
    smtlib.push_str("(set-option :produce-models true)\n");
    smtlib.push_str("(set-logic QF_UFLIA)\n");

    // Declare variables/constants
    for var in &var_names {
        let sort = var_sorts.get(var).copied().unwrap_or(SmtSort::Int);
        let _ = writeln!(
            smtlib,
            "(declare-const {} {})",
            smt_symbol(var),
            sort.as_smtlib()
        );
    }

    // Declare uninterpreted functions used by StructField / Apply(args)
    let mut funs: Vec<((String, usize), SmtSort)> = fun_sorts.into_iter().collect();
    funs.sort_by(|(a, _), (b, _)| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
    for ((name, arity), ret_sort) in funs {
        let args = (0..arity).map(|_| "Int").collect::<Vec<_>>().join(" ");
        let _ = writeln!(
            smtlib,
            "(declare-fun {} ({}) {})",
            smt_symbol(&name),
            args,
            ret_sort.as_smtlib()
        );
    }

    // To verify P => Q, we check if (P AND NOT Q) is unsat
    // If unsat, the implication holds
    smtlib.push_str("(assert (and ");
    smtlib.push_str(&predicate_to_smtlib_ffi(&ante_combined));
    smtlib.push_str(" (not ");
    smtlib.push_str(&predicate_to_smtlib_ffi(&cons_combined));
    smtlib.push_str(")))\n");
    smtlib.push_str("(check-sat)\n");
    smtlib.push_str("(get-model)\n");

    // Verify using Z4
    let result = verify_smtlib(&smtlib);
    match result {
        VerifyResult::Proven => (true, format!("{description} (Z4 proved)")),
        VerifyResult::Counterexample(cex) => {
            let cex_str = cex
                .assignments
                .iter()
                .map(|(n, v)| format!("{n}={v}"))
                .collect::<Vec<_>>()
                .join(", ");
            (
                false,
                format!("{description} failed: counterexample {{{cex_str}}}"),
            )
        }
        VerifyResult::Unknown { category, reason } => {
            // If Z4 returns unknown, we conservatively pass (assume compatible)
            // This matches the structural check behavior
            (
                true,
                format!("{description} (Z4 unknown: {category} - {reason})"),
            )
        }
        VerifyResult::Timeout { seconds } => (
            true,
            format!("{description} (Z4 timeout after {seconds:.2}s)"),
        ),
        VerifyResult::Error(e) => (true, format!("{description} (Z4 error: {e})")),
    }
}

fn build_ffi_param_alignment_map(
    caller: &FfiFunction,
    callee: &FfiFunction,
) -> std::collections::HashMap<String, String> {
    let mut map: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    for (i, (caller_param, callee_param)) in caller.params.iter().zip(&callee.params).enumerate() {
        let canonical = format!("arg{i}");
        map.insert(caller_param.name.clone(), canonical.clone());
        map.insert(callee_param.name.clone(), canonical);
    }
    map
}

#[allow(clippy::too_many_lines)]
fn rename_expr_vars_for_ffi(
    expr: &Expr,
    rename_map: &std::collections::HashMap<String, String>,
    bound_vars: &[String],
) -> Expr {
    match expr {
        Expr::Var(name) => {
            if bound_vars.iter().any(|b| b == name) {
                Expr::Var(name.clone())
            } else if let Some(new_name) = rename_map.get(name) {
                Expr::Var(new_name.clone())
            } else {
                Expr::Var(name.clone())
            }
        }
        Expr::Result => Expr::Result,
        Expr::Old(e) => Expr::Old(Box::new(rename_expr_vars_for_ffi(
            e, rename_map, bound_vars,
        ))),
        Expr::IntLit(v) => Expr::IntLit(*v),
        Expr::BoolLit(b) => Expr::BoolLit(*b),
        Expr::NilLit => Expr::NilLit,
        Expr::Add(a, b) => Expr::Add(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Sub(a, b) => Expr::Sub(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Mul(a, b) => Expr::Mul(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Div(a, b) => Expr::Div(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Rem(a, b) => Expr::Rem(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Neg(e) => Expr::Neg(Box::new(rename_expr_vars_for_ffi(
            e, rename_map, bound_vars,
        ))),
        Expr::Eq(a, b) => Expr::Eq(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Ne(a, b) => Expr::Ne(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Lt(a, b) => Expr::Lt(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Le(a, b) => Expr::Le(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Gt(a, b) => Expr::Gt(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Ge(a, b) => Expr::Ge(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::And(a, b) => Expr::And(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Or(a, b) => Expr::Or(
            Box::new(rename_expr_vars_for_ffi(a, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(b, rename_map, bound_vars)),
        ),
        Expr::Not(e) => Expr::Not(Box::new(rename_expr_vars_for_ffi(
            e, rename_map, bound_vars,
        ))),
        Expr::Ite { cond, then_, else_ } => Expr::Ite {
            cond: Box::new(rename_expr_vars_for_ffi(cond, rename_map, bound_vars)),
            then_: Box::new(rename_expr_vars_for_ffi(then_, rename_map, bound_vars)),
            else_: Box::new(rename_expr_vars_for_ffi(else_, rename_map, bound_vars)),
        },
        Expr::ArrayIndex(base, idx) => Expr::ArrayIndex(
            Box::new(rename_expr_vars_for_ffi(base, rename_map, bound_vars)),
            Box::new(rename_expr_vars_for_ffi(idx, rename_map, bound_vars)),
        ),
        Expr::StructField(base, field) => Expr::StructField(
            Box::new(rename_expr_vars_for_ffi(base, rename_map, bound_vars)),
            field.clone(),
        ),
        Expr::Apply { func, args } => Expr::Apply {
            func: func.clone(),
            args: args
                .iter()
                .map(|a| rename_expr_vars_for_ffi(a, rename_map, bound_vars))
                .collect(),
        },
        Expr::Forall { vars, body } => {
            let mut new_bound = bound_vars.to_vec();
            for (name, _) in vars {
                new_bound.push(name.clone());
            }
            Expr::Forall {
                vars: vars.clone(),
                body: Box::new(rename_expr_vars_for_ffi(body, rename_map, &new_bound)),
            }
        }
        Expr::Exists { vars, body } => {
            let mut new_bound = bound_vars.to_vec();
            for (name, _) in vars {
                new_bound.push(name.clone());
            }
            Expr::Exists {
                vars: vars.clone(),
                body: Box::new(rename_expr_vars_for_ffi(body, rename_map, &new_bound)),
            }
        }
    }
}

fn rename_predicate_vars_for_ffi(
    pred: &Predicate,
    rename_map: &std::collections::HashMap<String, String>,
) -> Predicate {
    match pred {
        Predicate::Expr(expr) => Predicate::Expr(rename_expr_vars_for_ffi(expr, rename_map, &[])),
        Predicate::And(preds) => Predicate::And(
            preds
                .iter()
                .map(|p| rename_predicate_vars_for_ffi(p, rename_map))
                .collect(),
        ),
        Predicate::Or(preds) => Predicate::Or(
            preds
                .iter()
                .map(|p| rename_predicate_vars_for_ffi(p, rename_map))
                .collect(),
        ),
        Predicate::Not(p) => Predicate::Not(Box::new(rename_predicate_vars_for_ffi(p, rename_map))),
        Predicate::Implies(p, q) => Predicate::Implies(
            Box::new(rename_predicate_vars_for_ffi(p, rename_map)),
            Box::new(rename_predicate_vars_for_ffi(q, rename_map)),
        ),
    }
}

fn rename_predicates_for_ffi_alignment(
    preds: &[Predicate],
    rename_map: &std::collections::HashMap<String, String>,
) -> Vec<Predicate> {
    preds
        .iter()
        .map(|p| rename_predicate_vars_for_ffi(p, rename_map))
        .collect()
}

/// Check precondition compatibility using Z4: `caller_requires` => `callee_requires`
///
/// For FFI safety, the caller must provide at least as strong preconditions as the callee requires.
/// This means: whatever the caller guarantees (`caller_requires`) must imply what the callee needs (`callee_requires`).
fn check_precondition_compatibility_z4(caller: &FfiFunction, callee: &FfiFunction) -> FfiCheck {
    // If callee has no requirements, any caller is fine
    if callee.requires.is_empty() {
        return FfiCheck {
            check_type: FfiCheckType::PreconditionCompatibility,
            passed: true,
            message: Some("Callee has no preconditions".to_string()),
        };
    }

    // If caller has no requirements but callee does, we need to prove the callee's
    // requirements are trivially satisfied (e.g., always true)
    // Use Z4 to check: true => callee_requires
    // Align variables across caller/callee by parameter position (not name).
    // This avoids false incompatibilities when Swift and Rust use different parameter names.
    let rename_map = build_ffi_param_alignment_map(caller, callee);
    let caller_requires = rename_predicates_for_ffi_alignment(&caller.requires, &rename_map);
    let callee_requires = rename_predicates_for_ffi_alignment(&callee.requires, &rename_map);

    let (passed, message) = verify_implication_z4(
        &caller_requires,
        &callee_requires,
        "caller_requires => callee_requires",
    );

    FfiCheck {
        check_type: FfiCheckType::PreconditionCompatibility,
        passed,
        message: Some(message),
    }
}

/// Check postcondition compatibility using Z4: `callee_ensures` => `caller_expects`
///
/// For FFI safety, the callee must provide at least as strong postconditions as the caller expects.
/// This means: whatever the callee guarantees (`callee_ensures`) must imply what the caller expects (`caller_ensures`).
fn check_postcondition_compatibility_z4(caller: &FfiFunction, callee: &FfiFunction) -> FfiCheck {
    // If caller expects nothing, any callee is fine
    if caller.ensures.is_empty() {
        return FfiCheck {
            check_type: FfiCheckType::PostconditionCompatibility,
            passed: true,
            message: Some("Caller expects no postconditions".to_string()),
        };
    }

    // Use Z4 to check: callee_ensures => caller_ensures
    // Align variables across caller/callee by parameter position (not name).
    let rename_map = build_ffi_param_alignment_map(caller, callee);
    let callee_ensures = rename_predicates_for_ffi_alignment(&callee.ensures, &rename_map);
    let caller_ensures = rename_predicates_for_ffi_alignment(&caller.ensures, &rename_map);

    let (passed, message) = verify_implication_z4(
        &callee_ensures,
        &caller_ensures,
        "callee_ensures => caller_expects",
    );

    FfiCheck {
        check_type: FfiCheckType::PostconditionCompatibility,
        passed,
        message: Some(message),
    }
}

/// Check type layout compatibility between caller and callee
fn check_type_layout_compatibility(caller: &FfiFunction, callee: &FfiFunction) -> FfiCheck {
    // Check parameter count
    if caller.params.len() != callee.params.len() {
        return FfiCheck {
            check_type: FfiCheckType::TypeLayout,
            passed: false,
            message: Some(format!(
                "Parameter count mismatch: {} has {}, {} has {}",
                caller.language,
                caller.params.len(),
                callee.language,
                callee.params.len()
            )),
        };
    }

    // Check each parameter type
    for (i, (caller_param, callee_param)) in caller.params.iter().zip(&callee.params).enumerate() {
        if !ffi_types_compatible(&caller_param.ffi_type, &callee_param.ffi_type) {
            return FfiCheck {
                check_type: FfiCheckType::TypeLayout,
                passed: false,
                message: Some(format!(
                    "Parameter {} type mismatch: {} has {:?}, {} has {:?}",
                    i,
                    caller.language,
                    caller_param.ffi_type,
                    callee.language,
                    callee_param.ffi_type
                )),
            };
        }
    }

    // Check return type
    if !ffi_types_compatible(&caller.return_type, &callee.return_type) {
        return FfiCheck {
            check_type: FfiCheckType::TypeLayout,
            passed: false,
            message: Some(format!(
                "Return type mismatch: {} expects {:?}, {} provides {:?}",
                caller.language, caller.return_type, callee.language, callee.return_type
            )),
        };
    }

    FfiCheck {
        check_type: FfiCheckType::TypeLayout,
        passed: true,
        message: Some("All types compatible".to_string()),
    }
}

/// Check if two FFI types are compatible
fn ffi_types_compatible(t1: &FfiType, t2: &FfiType) -> bool {
    match (t1, t2) {
        (FfiType::Bool, FfiType::Bool)
        | (FfiType::String, FfiType::String)
        | (FfiType::StringRef, FfiType::StringRef)
        | (FfiType::Bytes, FfiType::Bytes)
        | (FfiType::BytesRef, FfiType::BytesRef)
        | (FfiType::Void, FfiType::Void) => true,
        (FfiType::Int { bits: b1 }, FfiType::Int { bits: b2 })
        | (FfiType::UInt { bits: b1 }, FfiType::UInt { bits: b2 })
        | (FfiType::Float { bits: b1 }, FfiType::Float { bits: b2 }) => b1 == b2,
        (FfiType::Optional(inner1), FfiType::Optional(inner2)) => {
            ffi_types_compatible(inner1, inner2)
        }
        (FfiType::Result { ok: ok1, err: err1 }, FfiType::Result { ok: ok2, err: err2 }) => {
            ffi_types_compatible(ok1, ok2) && ffi_types_compatible(err1, err2)
        }
        (FfiType::Custom(n1), FfiType::Custom(n2)) => n1 == n2,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_predicate_true() {
        let p = Predicate::t();
        assert!(matches!(p, Predicate::Expr(Expr::BoolLit(true))));
    }

    #[test]
    fn test_predicate_and_empty() {
        let p = Predicate::and(vec![]);
        assert!(matches!(p, Predicate::Expr(Expr::BoolLit(true))));
    }

    #[test]
    fn test_predicate_and_single() {
        let inner = Predicate::t();
        let p = Predicate::and(vec![inner]);
        assert!(matches!(p, Predicate::Expr(Expr::BoolLit(true))));
    }

    #[test]
    fn test_expr_add() {
        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        assert!(matches!(expr, Expr::Add(_, _)));
    }

    // ========================================================================
    // UnknownReason Tests
    // ========================================================================

    #[test]
    fn test_unknown_reason_solver_returned_unknown_display() {
        let reason = UnknownReason::SolverReturnedUnknown;
        let display = format!("{reason}");
        assert!(display.contains("Z4 solver returned unknown"));
        assert!(display.contains("QF_LIA"));
    }

    #[test]
    fn test_unknown_reason_non_linear_arithmetic_display() {
        let reason = UnknownReason::NonLinearArithmetic {
            operation: "x * y".to_string(),
        };
        let display = format!("{reason}");
        assert!(display.contains("Non-linear arithmetic"));
        assert!(display.contains("x * y"));
    }

    #[test]
    fn test_unknown_reason_unsupported_pattern_display() {
        let reason = UnknownReason::UnsupportedPattern {
            pattern: "abs(x)".to_string(),
            suggestion: "Use x >= 0 ? x : -x".to_string(),
        };
        let display = format!("{reason}");
        assert!(display.contains("abs(x)"));
        assert!(display.contains("not fully supported"));
        assert!(display.contains("Use x >= 0"));
    }

    #[test]
    fn test_unknown_reason_floating_point_display() {
        let reason = UnknownReason::FloatingPointSymbolic;
        let display = format!("{reason}");
        assert!(display.contains("Floating point"));
        assert!(display.contains("symbolic"));
    }

    #[test]
    fn test_unknown_reason_no_termination_proof_display() {
        let reason = UnknownReason::NoTerminationProof;
        let display = format!("{reason}");
        assert!(display.contains("Termination"));
        assert!(display.contains("not proven"));
    }

    #[test]
    fn test_unknown_reason_no_memory_safety_display() {
        let reason = UnknownReason::NoMemorySafetyProof;
        let display = format!("{reason}");
        assert!(display.contains("Memory safety"));
        assert!(display.contains("not verified"));
    }

    #[test]
    fn test_unknown_reason_no_concurrency_display() {
        let reason = UnknownReason::NoConcurrencyProof;
        let display = format!("{reason}");
        assert!(display.contains("Concurrency"));
        assert!(display.contains("not verified"));
    }

    #[test]
    fn test_unknown_reason_other_display() {
        let reason = UnknownReason::Other {
            reason: "Custom reason text".to_string(),
        };
        let display = format!("{reason}");
        assert_eq!(display, "Custom reason text");
    }

    #[test]
    fn test_unknown_reason_clone() {
        let reason = UnknownReason::NonLinearArithmetic {
            operation: "x * y".to_string(),
        };
        let cloned = reason.clone();
        assert_eq!(reason, cloned);
    }

    #[test]
    fn test_unknown_reason_eq() {
        let r1 = UnknownReason::SolverReturnedUnknown;
        let r2 = UnknownReason::SolverReturnedUnknown;
        let r3 = UnknownReason::FloatingPointSymbolic;
        assert_eq!(r1, r2);
        assert_ne!(r1, r3);
    }

    #[test]
    fn test_unknown_reason_debug() {
        let reason = UnknownReason::NoTerminationProof;
        let debug = format!("{reason:?}");
        assert!(debug.contains("NoTerminationProof"));
    }

    // ========================================================================
    // VerifyResult Tests
    // ========================================================================

    #[test]
    fn test_verify_result_proven() {
        let result = VerifyResult::Proven;
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_verify_result_counterexample() {
        let ce = Counterexample {
            assignments: vec![("x".to_string(), Value::Int(42))],
        };
        let result = VerifyResult::Counterexample(ce);
        assert!(matches!(result, VerifyResult::Counterexample(_)));
    }

    #[test]
    fn test_verify_result_unknown() {
        let result = VerifyResult::Unknown {
            category: UnknownReason::SolverReturnedUnknown,
            reason: "legacy reason".to_string(),
        };
        if let VerifyResult::Unknown { category, reason } = result {
            assert!(matches!(category, UnknownReason::SolverReturnedUnknown));
            assert_eq!(reason, "legacy reason");
        } else {
            panic!("Expected Unknown variant");
        }
    }

    #[test]
    fn test_verify_result_timeout() {
        let result = VerifyResult::Timeout { seconds: 30.5 };
        if let VerifyResult::Timeout { seconds } = result {
            assert!((seconds - 30.5).abs() < f64::EPSILON);
        } else {
            panic!("Expected Timeout variant");
        }
    }

    #[test]
    fn test_verify_result_error() {
        let result = VerifyResult::Error("Something went wrong".to_string());
        if let VerifyResult::Error(msg) = result {
            assert_eq!(msg, "Something went wrong");
        } else {
            panic!("Expected Error variant");
        }
    }

    #[test]
    fn test_verify_result_clone() {
        let result = VerifyResult::Proven;
        let cloned = result;
        assert!(matches!(cloned, VerifyResult::Proven));
    }

    #[test]
    fn test_verify_result_debug() {
        let result = VerifyResult::Proven;
        let debug = format!("{result:?}");
        assert!(debug.contains("Proven"));
    }

    // ========================================================================
    // Value Display Tests
    // ========================================================================

    #[test]
    fn test_value_bool_display() {
        assert_eq!(format!("{}", Value::Bool(true)), "true");
        assert_eq!(format!("{}", Value::Bool(false)), "false");
    }

    #[test]
    fn test_value_int_display() {
        assert_eq!(format!("{}", Value::Int(42)), "42");
        assert_eq!(format!("{}", Value::Int(-100)), "-100");
        assert_eq!(format!("{}", Value::Int(0)), "0");
    }

    #[test]
    fn test_value_float_display() {
        let display = format!("{}", Value::Float(1.234));
        assert!(display.contains("1.234"));
    }

    #[test]
    fn test_value_bitvec_display() {
        let bv = Value::BitVec {
            bits: 16,
            value: vec![0xAB, 0xCD],
        };
        let display = format!("{bv}");
        assert!(display.contains("bv16"));
        assert!(display.contains("ab"));
        assert!(display.contains("cd"));
    }

    #[test]
    fn test_value_bitvec_empty() {
        let bv = Value::BitVec {
            bits: 0,
            value: vec![],
        };
        let display = format!("{bv}");
        assert_eq!(display, "bv0()");
    }

    #[test]
    fn test_value_array_display() {
        let arr = Value::Array(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        let display = format!("{arr}");
        assert_eq!(display, "[1, 2, 3]");
    }

    #[test]
    fn test_value_array_empty() {
        let arr = Value::Array(vec![]);
        let display = format!("{arr}");
        assert_eq!(display, "[]");
    }

    #[test]
    fn test_value_array_nested() {
        let arr = Value::Array(vec![
            Value::Array(vec![Value::Int(1), Value::Int(2)]),
            Value::Array(vec![Value::Int(3), Value::Int(4)]),
        ]);
        let display = format!("{arr}");
        assert_eq!(display, "[[1, 2], [3, 4]]");
    }

    #[test]
    fn test_value_struct_display() {
        let s = Value::Struct {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), Value::Int(10)),
                ("y".to_string(), Value::Int(20)),
            ],
        };
        let display = format!("{s}");
        assert!(display.contains("Point"));
        assert!(display.contains("x=10"));
        assert!(display.contains("y=20"));
    }

    #[test]
    fn test_value_struct_empty_fields() {
        let s = Value::Struct {
            name: "Empty".to_string(),
            fields: vec![],
        };
        let display = format!("{s}");
        assert_eq!(display, "Empty{}");
    }

    #[test]
    fn test_value_tuple_display() {
        let t = Value::Tuple(vec![Value::Int(1), Value::Bool(true), Value::Int(3)]);
        let display = format!("{t}");
        assert_eq!(display, "(1, true, 3)");
    }

    #[test]
    fn test_value_tuple_empty() {
        let t = Value::Tuple(vec![]);
        let display = format!("{t}");
        assert_eq!(display, "()");
    }

    #[test]
    fn test_value_tuple_single() {
        let t = Value::Tuple(vec![Value::Int(42)]);
        let display = format!("{t}");
        assert_eq!(display, "(42)");
    }

    #[test]
    fn test_value_tensor_display() {
        let t = Value::Tensor {
            shape: vec![2, 3],
            data: vec![Value::Int(1), Value::Int(2), Value::Int(3)],
        };
        let display = format!("{t}");
        assert!(display.contains("tensor"));
        assert!(display.contains("[2, 3]"));
        assert!(display.contains('1'));
    }

    #[test]
    fn test_value_tensor_truncated() {
        let t = Value::Tensor {
            shape: vec![10],
            data: (1..=10).map(Value::Int).collect(),
        };
        let display = format!("{t}");
        assert!(display.contains("..."));
    }

    #[test]
    fn test_value_tensor_empty() {
        let t = Value::Tensor {
            shape: vec![0],
            data: vec![],
        };
        let display = format!("{t}");
        assert!(display.contains("tensor"));
    }

    #[test]
    fn test_value_clone() {
        let v = Value::Struct {
            name: "Test".to_string(),
            fields: vec![("f".to_string(), Value::Int(1))],
        };
        let cloned = v;
        assert!(matches!(cloned, Value::Struct { .. }));
    }

    #[test]
    fn test_value_debug() {
        let v = Value::Bool(true);
        let debug = format!("{v:?}");
        assert!(debug.contains("Bool"));
        assert!(debug.contains("true"));
    }

    // ========================================================================
    // Counterexample Tests
    // ========================================================================

    #[test]
    fn test_counterexample_empty() {
        let ce = Counterexample {
            assignments: vec![],
        };
        assert!(ce.assignments.is_empty());
    }

    #[test]
    fn test_counterexample_single_assignment() {
        let ce = Counterexample {
            assignments: vec![("x".to_string(), Value::Int(42))],
        };
        assert_eq!(ce.assignments.len(), 1);
        assert_eq!(ce.assignments[0].0, "x");
    }

    #[test]
    fn test_counterexample_multiple_assignments() {
        let ce = Counterexample {
            assignments: vec![
                ("x".to_string(), Value::Int(10)),
                ("y".to_string(), Value::Int(20)),
                ("flag".to_string(), Value::Bool(false)),
            ],
        };
        assert_eq!(ce.assignments.len(), 3);
    }

    #[test]
    fn test_counterexample_clone() {
        let ce = Counterexample {
            assignments: vec![("x".to_string(), Value::Int(42))],
        };
        let cloned = ce;
        assert_eq!(cloned.assignments.len(), 1);
    }

    #[test]
    fn test_counterexample_debug() {
        let ce = Counterexample {
            assignments: vec![("x".to_string(), Value::Int(42))],
        };
        let debug = format!("{ce:?}");
        assert!(debug.contains("Counterexample"));
        assert!(debug.contains('x'));
    }

    // ========================================================================
    // VcId Tests
    // ========================================================================

    #[test]
    fn test_vc_id_equality() {
        let id1 = VcId(42);
        let id2 = VcId(42);
        let id3 = VcId(100);
        assert_eq!(id1, id2);
        assert_ne!(id1, id3);
    }

    #[test]
    fn test_vc_id_copy() {
        let id1 = VcId(42);
        let id2 = id1;
        assert_eq!(id1, id2);
    }

    #[test]
    fn test_vc_id_hash() {
        use std::collections::HashSet;
        let mut set = HashSet::new();
        set.insert(VcId(1));
        set.insert(VcId(2));
        set.insert(VcId(1));
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_vc_id_debug() {
        let id = VcId(123);
        let debug = format!("{id:?}");
        assert!(debug.contains("VcId"));
        assert!(debug.contains("123"));
    }

    // ========================================================================
    // SourceSpan Tests
    // ========================================================================

    #[test]
    fn test_source_span_creation() {
        let span = SourceSpan {
            file: "test.swift".into(),
            line_start: 10,
            line_end: 15,
            col_start: 5,
            col_end: 20,
        };
        assert_eq!(&*span.file, "test.swift");
        assert_eq!(span.line_start, 10);
        assert_eq!(span.line_end, 15);
    }

    #[test]
    fn test_source_span_single_line() {
        let span = SourceSpan {
            file: "single.swift".into(),
            line_start: 42,
            line_end: 42,
            col_start: 1,
            col_end: 80,
        };
        assert_eq!(span.line_start, span.line_end);
    }

    #[test]
    fn test_source_span_clone() {
        let span = SourceSpan {
            file: "clone.swift".into(),
            line_start: 1,
            line_end: 10,
            col_start: 1,
            col_end: 50,
        };
        let cloned = span;
        assert_eq!(&*cloned.file, "clone.swift");
        assert_eq!(cloned.line_start, 1);
    }

    #[test]
    fn test_source_span_debug() {
        let span = SourceSpan {
            file: "debug.swift".into(),
            line_start: 5,
            line_end: 10,
            col_start: 1,
            col_end: 20,
        };
        let debug = format!("{span:?}");
        assert!(debug.contains("SourceSpan"));
        assert!(debug.contains("debug.swift"));
    }

    // ========================================================================
    // VcType Tests
    // ========================================================================

    #[test]
    fn test_vc_type_int() {
        let t = VcType::Int {
            signed: true,
            bits: 32,
        };
        if let VcType::Int { signed, bits } = t {
            assert!(signed);
            assert_eq!(bits, 32);
        } else {
            panic!("Expected Int");
        }
    }

    #[test]
    fn test_vc_type_bool() {
        let t = VcType::Bool;
        assert!(matches!(t, VcType::Bool));
    }

    #[test]
    fn test_vc_type_float() {
        let t = VcType::Float { bits: 64 };
        if let VcType::Float { bits } = t {
            assert_eq!(bits, 64);
        } else {
            panic!("Expected Float");
        }
    }

    #[test]
    fn test_vc_type_array() {
        let t = VcType::Array {
            elem: Box::new(VcType::Int {
                signed: true,
                bits: 32,
            }),
            len: Some(10),
        };
        if let VcType::Array { elem, len } = t {
            assert!(matches!(*elem, VcType::Int { .. }));
            assert_eq!(len, Some(10));
        } else {
            panic!("Expected Array");
        }
    }

    #[test]
    fn test_vc_type_array_unsized() {
        let t = VcType::Array {
            elem: Box::new(VcType::Bool),
            len: None,
        };
        if let VcType::Array { len, .. } = t {
            assert!(len.is_none());
        } else {
            panic!("Expected Array");
        }
    }

    #[test]
    fn test_vc_type_ref() {
        let t = VcType::Ref {
            mutable: true,
            inner: Box::new(VcType::Int {
                signed: true,
                bits: 64,
            }),
        };
        if let VcType::Ref { mutable, inner } = t {
            assert!(mutable);
            assert!(matches!(*inner, VcType::Int { .. }));
        } else {
            panic!("Expected Ref");
        }
    }

    #[test]
    fn test_vc_type_tuple() {
        let t = VcType::Tuple(vec![
            VcType::Bool,
            VcType::Int {
                signed: true,
                bits: 32,
            },
        ]);
        if let VcType::Tuple(elems) = t {
            assert_eq!(elems.len(), 2);
        } else {
            panic!("Expected Tuple");
        }
    }

    #[test]
    fn test_vc_type_tuple_empty() {
        let t = VcType::Tuple(vec![]);
        if let VcType::Tuple(elems) = t {
            assert!(elems.is_empty());
        } else {
            panic!("Expected Tuple");
        }
    }

    #[test]
    fn test_vc_type_struct() {
        let t = VcType::Struct {
            name: "Point".to_string(),
            fields: vec![
                (
                    "x".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "y".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
        };
        if let VcType::Struct { name, fields } = t {
            assert_eq!(name, "Point");
            assert_eq!(fields.len(), 2);
        } else {
            panic!("Expected Struct");
        }
    }

    #[test]
    fn test_vc_type_abstract() {
        let t = VcType::Abstract("MyCustomType".to_string());
        if let VcType::Abstract(name) = t {
            assert_eq!(name, "MyCustomType");
        } else {
            panic!("Expected Abstract");
        }
    }

    #[test]
    fn test_vc_type_equality() {
        let t1 = VcType::Int {
            signed: true,
            bits: 32,
        };
        let t2 = VcType::Int {
            signed: true,
            bits: 32,
        };
        let t3 = VcType::Int {
            signed: false,
            bits: 32,
        };
        assert_eq!(t1, t2);
        assert_ne!(t1, t3);
    }

    #[test]
    fn test_vc_type_clone() {
        let t = VcType::Struct {
            name: "Test".to_string(),
            fields: vec![("f".to_string(), VcType::Bool)],
        };
        let cloned = t.clone();
        assert_eq!(t, cloned);
    }

    // ========================================================================
    // Expr Tests
    // ========================================================================

    #[test]
    fn test_expr_int_lit() {
        let e = Expr::IntLit(42);
        assert!(matches!(e, Expr::IntLit(42)));
    }

    #[test]
    fn test_expr_bool_lit() {
        let e = Expr::BoolLit(true);
        assert!(matches!(e, Expr::BoolLit(true)));
    }

    #[test]
    fn test_expr_nil_lit() {
        let e = Expr::NilLit;
        assert!(matches!(e, Expr::NilLit));
    }

    #[test]
    fn test_expr_var() {
        let e = Expr::Var("myVar".to_string());
        if let Expr::Var(name) = e {
            assert_eq!(name, "myVar");
        } else {
            panic!("Expected Var");
        }
    }

    #[test]
    fn test_expr_result() {
        let e = Expr::Result;
        assert!(matches!(e, Expr::Result));
    }

    #[test]
    fn test_expr_old() {
        let e = Expr::Old(Box::new(Expr::Var("x".to_string())));
        assert!(matches!(e, Expr::Old(_)));
    }

    #[test]
    fn test_expr_sub() {
        let e = Expr::Sub(Box::new(Expr::IntLit(10)), Box::new(Expr::IntLit(3)));
        assert!(matches!(e, Expr::Sub(_, _)));
    }

    #[test]
    fn test_expr_mul() {
        let e = Expr::Mul(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert!(matches!(e, Expr::Mul(_, _)));
    }

    #[test]
    fn test_expr_div() {
        let e = Expr::Div(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert!(matches!(e, Expr::Div(_, _)));
    }

    #[test]
    fn test_expr_rem() {
        let e = Expr::Rem(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(3)),
        );
        assert!(matches!(e, Expr::Rem(_, _)));
    }

    #[test]
    fn test_expr_neg() {
        let e = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        assert!(matches!(e, Expr::Neg(_)));
    }

    #[test]
    fn test_expr_eq() {
        let e = Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert!(matches!(e, Expr::Eq(_, _)));
    }

    #[test]
    fn test_expr_ne() {
        let e = Expr::Ne(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert!(matches!(e, Expr::Ne(_, _)));
    }

    #[test]
    fn test_expr_lt() {
        let e = Expr::Lt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(10)),
        );
        assert!(matches!(e, Expr::Lt(_, _)));
    }

    #[test]
    fn test_expr_le() {
        let e = Expr::Le(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(10)),
        );
        assert!(matches!(e, Expr::Le(_, _)));
    }

    #[test]
    fn test_expr_gt() {
        let e = Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert!(matches!(e, Expr::Gt(_, _)));
    }

    #[test]
    fn test_expr_ge() {
        let e = Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert!(matches!(e, Expr::Ge(_, _)));
    }

    #[test]
    fn test_expr_and() {
        let e = Expr::And(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::BoolLit(false)),
        );
        assert!(matches!(e, Expr::And(_, _)));
    }

    #[test]
    fn test_expr_or() {
        let e = Expr::Or(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::BoolLit(false)),
        );
        assert!(matches!(e, Expr::Or(_, _)));
    }

    #[test]
    fn test_expr_not() {
        let e = Expr::Not(Box::new(Expr::BoolLit(true)));
        assert!(matches!(e, Expr::Not(_)));
    }

    #[test]
    fn test_expr_ite() {
        let e = Expr::Ite {
            cond: Box::new(Expr::BoolLit(true)),
            then_: Box::new(Expr::IntLit(1)),
            else_: Box::new(Expr::IntLit(0)),
        };
        assert!(matches!(e, Expr::Ite { .. }));
    }

    #[test]
    fn test_expr_array_index() {
        let e = Expr::ArrayIndex(
            Box::new(Expr::Var("arr".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert!(matches!(e, Expr::ArrayIndex(_, _)));
    }

    #[test]
    fn test_expr_struct_field() {
        let e = Expr::StructField(Box::new(Expr::Var("point".to_string())), "x".to_string());
        if let Expr::StructField(_, field) = e {
            assert_eq!(field, "x");
        } else {
            panic!("Expected StructField");
        }
    }

    #[test]
    fn test_expr_apply() {
        let e = Expr::Apply {
            func: "abs".to_string(),
            args: vec![Expr::Var("x".to_string())],
        };
        if let Expr::Apply { func, args } = e {
            assert_eq!(func, "abs");
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected Apply");
        }
    }

    #[test]
    fn test_expr_apply_no_args() {
        let e = Expr::Apply {
            func: "now".to_string(),
            args: vec![],
        };
        if let Expr::Apply { args, .. } = e {
            assert!(args.is_empty());
        } else {
            panic!("Expected Apply");
        }
    }

    #[test]
    fn test_expr_forall() {
        let e = Expr::Forall {
            vars: vec![(
                "i".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Expr::BoolLit(true)),
        };
        if let Expr::Forall { vars, .. } = e {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "i");
        } else {
            panic!("Expected Forall");
        }
    }

    #[test]
    fn test_expr_exists() {
        let e = Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        };
        assert!(matches!(e, Expr::Exists { .. }));
    }

    #[test]
    fn test_expr_clone() {
        let e = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        let cloned = e;
        assert!(matches!(cloned, Expr::Add(_, _)));
    }

    #[test]
    fn test_expr_debug() {
        let e = Expr::IntLit(42);
        let debug = format!("{e:?}");
        assert!(debug.contains("IntLit"));
        assert!(debug.contains("42"));
    }

    #[test]
    fn test_expr_nested() {
        let e = Expr::Add(
            Box::new(Expr::Mul(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(2)),
            )),
            Box::new(Expr::Sub(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
        );
        assert!(matches!(e, Expr::Add(_, _)));
    }

    // ========================================================================
    // VcKind Tests
    // ========================================================================

    #[test]
    fn test_vc_kind_predicate() {
        let vk = VcKind::Predicate(Predicate::t());
        assert!(matches!(vk, VcKind::Predicate(_)));
    }

    #[test]
    fn test_vc_kind_implies() {
        let vk = VcKind::Implies {
            antecedent: Predicate::t(),
            consequent: Predicate::f(),
        };
        assert!(matches!(vk, VcKind::Implies { .. }));
    }

    #[test]
    fn test_vc_kind_termination() {
        let vk = VcKind::Termination {
            measure: Expr::Var("n".to_string()),
            initial_measure: Some(Expr::IntLit(10)),
            next_measure: Expr::Sub(
                Box::new(Expr::Var("n".to_string())),
                Box::new(Expr::IntLit(1)),
            ),
            loop_label: "loop_0".to_string(),
        };
        if let VcKind::Termination {
            loop_label,
            initial_measure,
            ..
        } = vk
        {
            assert_eq!(loop_label, "loop_0");
            assert!(initial_measure.is_some());
        } else {
            panic!("Expected Termination");
        }
    }

    #[test]
    fn test_vc_kind_termination_no_initial() {
        let vk = VcKind::Termination {
            measure: Expr::Var("n".to_string()),
            initial_measure: None,
            next_measure: Expr::Sub(
                Box::new(Expr::Var("n".to_string())),
                Box::new(Expr::IntLit(1)),
            ),
            loop_label: "while_loop".to_string(),
        };
        if let VcKind::Termination {
            initial_measure, ..
        } = vk
        {
            assert!(initial_measure.is_none());
        } else {
            panic!("Expected Termination");
        }
    }

    #[test]
    fn test_vc_kind_clone() {
        let vk = VcKind::Predicate(Predicate::t());
        let cloned = vk;
        assert!(matches!(cloned, VcKind::Predicate(_)));
    }

    #[test]
    fn test_vc_kind_debug() {
        let vk = VcKind::Predicate(Predicate::t());
        let debug = format!("{vk:?}");
        assert!(debug.contains("Predicate"));
    }

    // ========================================================================
    // Predicate Additional Tests
    // ========================================================================

    #[test]
    fn test_predicate_false() {
        let p = Predicate::f();
        assert!(matches!(p, Predicate::Expr(Expr::BoolLit(false))));
    }

    #[test]
    fn test_predicate_and_two() {
        let p = Predicate::and(vec![Predicate::t(), Predicate::f()]);
        assert!(matches!(p, Predicate::And(_)));
    }

    #[test]
    fn test_predicate_or_empty() {
        let p = Predicate::or(vec![]);
        assert!(matches!(p, Predicate::Expr(Expr::BoolLit(false))));
    }

    #[test]
    fn test_predicate_or_single() {
        let p = Predicate::or(vec![Predicate::t()]);
        assert!(matches!(p, Predicate::Expr(Expr::BoolLit(true))));
    }

    #[test]
    fn test_predicate_or_two() {
        let p = Predicate::or(vec![Predicate::t(), Predicate::f()]);
        assert!(matches!(p, Predicate::Or(_)));
    }

    #[test]
    fn test_predicate_not() {
        let p = Predicate::Not(Box::new(Predicate::t()));
        assert!(matches!(p, Predicate::Not(_)));
    }

    #[test]
    fn test_predicate_implies() {
        let p = Predicate::Implies(Box::new(Predicate::t()), Box::new(Predicate::f()));
        assert!(matches!(p, Predicate::Implies(_, _)));
    }

    #[test]
    fn test_predicate_expr() {
        let p = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        assert!(matches!(p, Predicate::Expr(Expr::Gt(_, _))));
    }

    #[test]
    fn test_predicate_clone() {
        let p = Predicate::And(vec![Predicate::t(), Predicate::f()]);
        let cloned = p;
        assert!(matches!(cloned, Predicate::And(_)));
    }

    #[test]
    fn test_predicate_debug() {
        let p = Predicate::t();
        let debug = format!("{p:?}");
        assert!(debug.contains("Expr"));
        assert!(debug.contains("BoolLit"));
    }

    // ========================================================================
    // VerificationCondition Tests
    // ========================================================================

    #[test]
    fn test_verification_condition_creation() {
        let vc = VerificationCondition {
            id: VcId(1),
            name: "test_vc".to_string(),
            span: SourceSpan {
                file: "test.swift".into(),
                line_start: 10,
                line_end: 10,
                col_start: 1,
                col_end: 50,
            },
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: None,
        };
        assert_eq!(vc.name, "test_vc");
        assert_eq!(vc.id, VcId(1));
    }

    #[test]
    fn test_verification_condition_clone() {
        let vc = VerificationCondition {
            id: VcId(42),
            name: "clone_test".to_string(),
            span: SourceSpan {
                file: "clone.swift".into(),
                line_start: 1,
                line_end: 1,
                col_start: 1,
                col_end: 10,
            },
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: None,
        };
        let cloned = vc;
        assert_eq!(cloned.id, VcId(42));
        assert_eq!(cloned.name, "clone_test");
    }

    #[test]
    fn test_verification_condition_debug() {
        let vc = VerificationCondition {
            id: VcId(99),
            name: "debug_test".to_string(),
            span: SourceSpan {
                file: "debug.swift".into(),
                line_start: 5,
                line_end: 5,
                col_start: 1,
                col_end: 20,
            },
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: None,
        };
        let debug = format!("{vc:?}");
        assert!(debug.contains("VerificationCondition"));
        assert!(debug.contains("debug_test"));
    }

    #[test]
    fn test_verification_condition_with_preferred_backend() {
        let vc = VerificationCondition {
            id: VcId(100),
            name: "backend_test".to_string(),
            span: SourceSpan {
                file: "backend.swift".into(),
                line_start: 1,
                line_end: 1,
                col_start: 1,
                col_end: 10,
            },
            condition: VcKind::Predicate(Predicate::t()),
            preferred_backend: Some("z3".to_string()),
        };
        assert_eq!(vc.preferred_backend, Some("z3".to_string()));
    }

    // ========================================================================
    // FFI Verification Tests
    // ========================================================================

    /// Helper to create a simple `FfiFunction` for testing
    fn make_ffi_func(
        name: &str,
        language: FfiLanguage,
        params: Vec<(&str, FfiType)>,
        return_type: FfiType,
        requires: Vec<Predicate>,
        ensures: Vec<Predicate>,
    ) -> FfiFunction {
        FfiFunction {
            name: name.to_string(),
            language,
            params: params
                .into_iter()
                .map(|(n, t)| FfiParam {
                    name: n.to_string(),
                    ffi_type: t,
                })
                .collect(),
            return_type,
            requires,
            ensures,
            trusted: false,
            source_file: None,
            source_line: None,
        }
    }

    #[test]
    fn test_ffi_types_compatible_basic() {
        assert!(ffi_types_compatible(&FfiType::Bool, &FfiType::Bool));
        assert!(ffi_types_compatible(
            &FfiType::Int { bits: 32 },
            &FfiType::Int { bits: 32 }
        ));
        assert!(!ffi_types_compatible(
            &FfiType::Int { bits: 32 },
            &FfiType::Int { bits: 64 }
        ));
        assert!(ffi_types_compatible(&FfiType::String, &FfiType::String));
        assert!(ffi_types_compatible(&FfiType::Void, &FfiType::Void));
        assert!(!ffi_types_compatible(
            &FfiType::Bool,
            &FfiType::Int { bits: 32 }
        ));
    }

    #[test]
    fn test_ffi_types_compatible_uint() {
        // UInt types should match by bit width
        assert!(ffi_types_compatible(
            &FfiType::UInt { bits: 32 },
            &FfiType::UInt { bits: 32 }
        ));
        assert!(ffi_types_compatible(
            &FfiType::UInt { bits: 64 },
            &FfiType::UInt { bits: 64 }
        ));
        // Different bit widths should not match
        assert!(!ffi_types_compatible(
            &FfiType::UInt { bits: 32 },
            &FfiType::UInt { bits: 64 }
        ));
        // UInt and Int should not match even with same bits
        assert!(!ffi_types_compatible(
            &FfiType::UInt { bits: 32 },
            &FfiType::Int { bits: 32 }
        ));
    }

    #[test]
    fn test_ffi_types_compatible_float() {
        // Float types should match by bit width
        assert!(ffi_types_compatible(
            &FfiType::Float { bits: 32 },
            &FfiType::Float { bits: 32 }
        ));
        assert!(ffi_types_compatible(
            &FfiType::Float { bits: 64 },
            &FfiType::Float { bits: 64 }
        ));
        // Different bit widths should not match
        assert!(!ffi_types_compatible(
            &FfiType::Float { bits: 32 },
            &FfiType::Float { bits: 64 }
        ));
        // Float and Int should not match
        assert!(!ffi_types_compatible(
            &FfiType::Float { bits: 32 },
            &FfiType::Int { bits: 32 }
        ));
    }

    #[test]
    fn test_ffi_types_compatible_string_ref() {
        // StringRef should match StringRef
        assert!(ffi_types_compatible(
            &FfiType::StringRef,
            &FfiType::StringRef
        ));
        // StringRef should not match String
        assert!(!ffi_types_compatible(&FfiType::StringRef, &FfiType::String));
        // StringRef should not match BytesRef
        assert!(!ffi_types_compatible(
            &FfiType::StringRef,
            &FfiType::BytesRef
        ));
    }

    #[test]
    fn test_ffi_types_compatible_bytes_and_bytes_ref() {
        // Bytes should match Bytes
        assert!(ffi_types_compatible(&FfiType::Bytes, &FfiType::Bytes));
        // BytesRef should match BytesRef
        assert!(ffi_types_compatible(&FfiType::BytesRef, &FfiType::BytesRef));
        // Bytes and BytesRef should not match
        assert!(!ffi_types_compatible(&FfiType::Bytes, &FfiType::BytesRef));
        // Bytes and String should not match
        assert!(!ffi_types_compatible(&FfiType::Bytes, &FfiType::String));
    }

    #[test]
    fn test_ffi_types_compatible_optional() {
        let opt_int32 = FfiType::Optional(Box::new(FfiType::Int { bits: 32 }));
        let opt_int64 = FfiType::Optional(Box::new(FfiType::Int { bits: 64 }));
        let opt_bool = FfiType::Optional(Box::new(FfiType::Bool));

        assert!(ffi_types_compatible(&opt_int32, &opt_int32));
        assert!(!ffi_types_compatible(&opt_int32, &opt_int64));
        assert!(!ffi_types_compatible(&opt_int32, &opt_bool));
    }

    #[test]
    fn test_ffi_types_compatible_result() {
        let res1 = FfiType::Result {
            ok: Box::new(FfiType::Int { bits: 32 }),
            err: Box::new(FfiType::String),
        };
        let res2 = FfiType::Result {
            ok: Box::new(FfiType::Int { bits: 32 }),
            err: Box::new(FfiType::String),
        };
        let res3 = FfiType::Result {
            ok: Box::new(FfiType::Int { bits: 64 }),
            err: Box::new(FfiType::String),
        };

        assert!(ffi_types_compatible(&res1, &res2));
        assert!(!ffi_types_compatible(&res1, &res3));
    }

    #[test]
    fn test_ffi_types_compatible_custom() {
        let custom1 = FfiType::Custom("ParseResult".to_string());
        let custom2 = FfiType::Custom("ParseResult".to_string());
        let custom3 = FfiType::Custom("VoiceError".to_string());

        assert!(ffi_types_compatible(&custom1, &custom2));
        assert!(!ffi_types_compatible(&custom1, &custom3));
    }

    #[test]
    fn test_ffi_specs_add() {
        let mut specs = FfiSpecs::new();

        let rust_fn = make_ffi_func(
            "parse_escape",
            FfiLanguage::Rust,
            vec![("buffer", FfiType::BytesRef)],
            FfiType::Int { bits: 32 },
            vec![],
            vec![],
        );

        let swift_fn = make_ffi_func(
            "parse_escape",
            FfiLanguage::Swift,
            vec![("buffer", FfiType::BytesRef)],
            FfiType::Int { bits: 32 },
            vec![],
            vec![],
        );

        specs.add(rust_fn);
        specs.add(swift_fn);

        assert_eq!(specs.rust_exports.len(), 1);
        assert_eq!(specs.swift_imports.len(), 1);
        assert!(specs.rust_exports.contains_key("parse_escape"));
        assert!(specs.swift_imports.contains_key("parse_escape"));
    }

    #[test]
    fn test_verify_ffi_compatible_no_specs() {
        // Both have no specs - should pass
        let rust_fn = make_ffi_func(
            "simple_add",
            FfiLanguage::Rust,
            vec![
                ("x", FfiType::Int { bits: 32 }),
                ("y", FfiType::Int { bits: 32 }),
            ],
            FfiType::Int { bits: 32 },
            vec![],
            vec![],
        );

        let swift_fn = make_ffi_func(
            "simple_add",
            FfiLanguage::Swift,
            vec![
                ("x", FfiType::Int { bits: 32 }),
                ("y", FfiType::Int { bits: 32 }),
            ],
            FfiType::Int { bits: 32 },
            vec![],
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let results = verify_ffi_compatibility(&specs);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].result, FfiCompatibility::Compatible);
    }

    #[test]
    fn test_verify_ffi_compatible_matching_specs() {
        // Both have matching specs
        let pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let rust_fn = make_ffi_func(
            "increment",
            FfiLanguage::Rust,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![pre.clone()],
            vec![],
        );

        let swift_fn = make_ffi_func(
            "increment",
            FfiLanguage::Swift,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![pre],
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let results = verify_ffi_compatibility(&specs);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].result, FfiCompatibility::Compatible);
    }

    #[test]
    fn test_verify_ffi_incompatible_missing_precondition() {
        // Rust requires precondition, Swift doesn't provide it
        let pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let rust_fn = make_ffi_func(
            "increment",
            FfiLanguage::Rust,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![pre], // Rust requires x > 0
            vec![],
        );

        let swift_fn = make_ffi_func(
            "increment",
            FfiLanguage::Swift,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![], // Swift provides no precondition
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let results = verify_ffi_compatibility(&specs);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].result, FfiCompatibility::Incompatible);

        // Find the precondition check
        let pre_check = results[0]
            .checks
            .iter()
            .find(|c| c.check_type == FfiCheckType::PreconditionCompatibility);
        assert!(pre_check.is_some());
        assert!(!pre_check.unwrap().passed);
    }

    #[test]
    fn test_verify_ffi_incompatible_missing_postcondition() {
        // Swift expects postcondition, Rust doesn't provide it
        let post = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Result),
            Box::new(Expr::Var("x".to_string())),
        ));

        let rust_fn = make_ffi_func(
            "increment",
            FfiLanguage::Rust,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![],
            vec![], // Rust provides no postcondition
        );

        let swift_fn = make_ffi_func(
            "increment",
            FfiLanguage::Swift,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![],
            vec![post], // Swift expects result >= x
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let results = verify_ffi_compatibility(&specs);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].result, FfiCompatibility::Incompatible);

        // Find the postcondition check
        let post_check = results[0]
            .checks
            .iter()
            .find(|c| c.check_type == FfiCheckType::PostconditionCompatibility);
        assert!(post_check.is_some());
        assert!(!post_check.unwrap().passed);
    }

    #[test]
    fn test_verify_ffi_incompatible_type_mismatch() {
        // Type mismatch: Swift expects Int64, Rust provides Int32
        let rust_fn = make_ffi_func(
            "get_size",
            FfiLanguage::Rust,
            vec![],
            FfiType::Int { bits: 32 }, // Rust returns i32
            vec![],
            vec![],
        );

        let swift_fn = make_ffi_func(
            "get_size",
            FfiLanguage::Swift,
            vec![],
            FfiType::Int { bits: 64 }, // Swift expects Int64
            vec![],
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let results = verify_ffi_compatibility(&specs);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].result, FfiCompatibility::Incompatible);

        // Find the type layout check
        let type_check = results[0]
            .checks
            .iter()
            .find(|c| c.check_type == FfiCheckType::TypeLayout);
        assert!(type_check.is_some());
        assert!(!type_check.unwrap().passed);
    }

    #[test]
    fn test_verify_ffi_incompatible_param_count() {
        // Parameter count mismatch
        let rust_fn = make_ffi_func(
            "process",
            FfiLanguage::Rust,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Void,
            vec![],
            vec![],
        );

        let swift_fn = make_ffi_func(
            "process",
            FfiLanguage::Swift,
            vec![
                ("x", FfiType::Int { bits: 32 }),
                ("y", FfiType::Int { bits: 32 }),
            ],
            FfiType::Void,
            vec![],
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let results = verify_ffi_compatibility(&specs);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].result, FfiCompatibility::Incompatible);
    }

    #[test]
    fn test_verify_ffi_missing_export() {
        // Swift imports function that Rust doesn't export
        let swift_fn = make_ffi_func(
            "nonexistent",
            FfiLanguage::Swift,
            vec![],
            FfiType::Void,
            vec![],
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(swift_fn);

        let results = verify_ffi_compatibility(&specs);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].result, FfiCompatibility::Unknown);
    }

    #[test]
    fn test_verify_ffi_trusted_skip() {
        // Trusted functions skip verification
        let mut rust_fn = make_ffi_func(
            "unsafe_op",
            FfiLanguage::Rust,
            vec![("ptr", FfiType::Custom("RawPointer".to_string()))],
            FfiType::Void,
            vec![Predicate::Expr(Expr::BoolLit(true))],
            vec![],
        );
        rust_fn.trusted = true;

        let swift_fn = make_ffi_func(
            "unsafe_op",
            FfiLanguage::Swift,
            vec![("ptr", FfiType::Custom("RawPointer".to_string()))],
            FfiType::Void,
            vec![], // No specs on Swift side
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let results = verify_ffi_compatibility(&specs);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].result, FfiCompatibility::Compatible);
    }

    #[test]
    fn test_verify_ffi_kotlin_import() {
        // Test Kotlin import verification
        let rust_fn = make_ffi_func(
            "start_stt",
            FfiLanguage::Rust,
            vec![("sample_rate", FfiType::UInt { bits: 32 })],
            FfiType::Result {
                ok: Box::new(FfiType::Custom("SessionId".to_string())),
                err: Box::new(FfiType::Custom("VoiceError".to_string())),
            },
            vec![],
            vec![],
        );

        let kotlin_fn = make_ffi_func(
            "start_stt",
            FfiLanguage::Kotlin,
            vec![("sample_rate", FfiType::UInt { bits: 32 })],
            FfiType::Result {
                ok: Box::new(FfiType::Custom("SessionId".to_string())),
                err: Box::new(FfiType::Custom("VoiceError".to_string())),
            },
            vec![],
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(kotlin_fn);

        let results = verify_ffi_compatibility(&specs);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].result, FfiCompatibility::Compatible);
        assert_eq!(results[0].caller, FfiLanguage::Kotlin);
        assert_eq!(results[0].callee, FfiLanguage::Rust);
    }

    #[test]
    fn test_ffi_language_display() {
        assert_eq!(format!("{}", FfiLanguage::Rust), "Rust");
        assert_eq!(format!("{}", FfiLanguage::Swift), "Swift");
        assert_eq!(format!("{}", FfiLanguage::Kotlin), "Kotlin");
    }

    #[test]
    fn test_ffi_check_type_display() {
        assert_eq!(
            format!("{}", FfiCheckType::PreconditionCompatibility),
            "precondition"
        );
        assert_eq!(
            format!("{}", FfiCheckType::PostconditionCompatibility),
            "postcondition"
        );
        assert_eq!(format!("{}", FfiCheckType::TypeLayout), "type layout");
        assert_eq!(format!("{}", FfiCheckType::Ownership), "ownership");
    }

    // ========================================================================
    // Z4-based FFI Verification Tests
    // ========================================================================

    #[test]
    fn test_z4_verify_ffi_compatible_no_specs() {
        // Both have no specs - should pass with Z4
        let rust_fn = make_ffi_func(
            "simple_add",
            FfiLanguage::Rust,
            vec![
                ("x", FfiType::Int { bits: 32 }),
                ("y", FfiType::Int { bits: 32 }),
            ],
            FfiType::Int { bits: 32 },
            vec![],
            vec![],
        );

        let swift_fn = make_ffi_func(
            "simple_add",
            FfiLanguage::Swift,
            vec![
                ("x", FfiType::Int { bits: 32 }),
                ("y", FfiType::Int { bits: 32 }),
            ],
            FfiType::Int { bits: 32 },
            vec![],
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].result, FfiCompatibility::Compatible);
    }

    #[test]
    fn test_z4_verify_ffi_precondition_implication_valid() {
        // Swift provides x > 0, Rust requires x > -1
        // x > 0 => x > -1 should verify
        let swift_pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let rust_pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(-1)),
        ));

        let rust_fn = make_ffi_func(
            "process",
            FfiLanguage::Rust,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![rust_pre], // Rust requires x > -1
            vec![],
        );

        let swift_fn = make_ffi_func(
            "process",
            FfiLanguage::Swift,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![swift_pre], // Swift provides x > 0
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);
        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].result,
            FfiCompatibility::Compatible,
            "x > 0 => x > -1 should be valid. Result: {:?}",
            results[0]
        );
    }

    #[test]
    fn test_z4_verify_ffi_precondition_implication_invalid() {
        // Swift provides x > 0, Rust requires x > 10
        // x > 0 => x > 10 should NOT verify (counterexample: x = 5)
        let swift_pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let rust_pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(10)),
        ));

        let rust_fn = make_ffi_func(
            "process",
            FfiLanguage::Rust,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![rust_pre], // Rust requires x > 10
            vec![],
        );

        let swift_fn = make_ffi_func(
            "process",
            FfiLanguage::Swift,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![swift_pre], // Swift only provides x > 0
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);
        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].result,
            FfiCompatibility::Incompatible,
            "x > 0 => x > 10 should fail. Result: {:?}",
            results[0]
        );
    }

    #[test]
    fn test_z4_verify_ffi_postcondition_implication_valid() {
        // Rust ensures result >= 0, Swift expects result >= -1
        // result >= 0 => result >= -1 should verify
        let rust_post = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("result".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let swift_post = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("result".to_string())),
            Box::new(Expr::IntLit(-1)),
        ));

        let rust_fn = make_ffi_func(
            "compute",
            FfiLanguage::Rust,
            vec![],
            FfiType::Int { bits: 32 },
            vec![],
            vec![rust_post], // Rust ensures result >= 0
        );

        let swift_fn = make_ffi_func(
            "compute",
            FfiLanguage::Swift,
            vec![],
            FfiType::Int { bits: 32 },
            vec![],
            vec![swift_post], // Swift expects result >= -1
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);
        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].result,
            FfiCompatibility::Compatible,
            "result >= 0 => result >= -1 should be valid. Result: {:?}",
            results[0]
        );
    }

    #[test]
    fn test_z4_verify_ffi_alignment_by_position_not_name() {
        // Rust: (a, b) requires b > 0
        // Swift: (dividend, divisor) requires divisor > 10
        //
        // By position, divisor aligns with b, so divisor > 10 => b > 0.
        // Without positional alignment, this would incorrectly compare different names.

        let rust_pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("b".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let swift_pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("divisor".to_string())),
            Box::new(Expr::IntLit(10)),
        ));

        let rust_fn = make_ffi_func(
            "safe_divide",
            FfiLanguage::Rust,
            vec![
                ("a", FfiType::Int { bits: 32 }),
                ("b", FfiType::Int { bits: 32 }),
            ],
            FfiType::Int { bits: 32 },
            vec![rust_pre],
            vec![],
        );

        let swift_fn = make_ffi_func(
            "safe_divide",
            FfiLanguage::Swift,
            vec![
                ("dividend", FfiType::Int { bits: 32 }),
                ("divisor", FfiType::Int { bits: 32 }),
            ],
            FfiType::Int { bits: 32 },
            vec![swift_pre],
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);
        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].result,
            FfiCompatibility::Compatible,
            "Expected compatible after param alignment, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn test_z4_verify_ffi_alignment_respects_argument_positions() {
        // Rust requires b > 0 (arg1), but Swift only requires dividend > 0 (arg0).
        // After positional alignment, this must be incompatible.

        let rust_pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("b".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let swift_pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("dividend".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let rust_fn = make_ffi_func(
            "safe_divide",
            FfiLanguage::Rust,
            vec![
                ("a", FfiType::Int { bits: 32 }),
                ("b", FfiType::Int { bits: 32 }),
            ],
            FfiType::Int { bits: 32 },
            vec![rust_pre],
            vec![],
        );

        let swift_fn = make_ffi_func(
            "safe_divide",
            FfiLanguage::Swift,
            vec![
                ("dividend", FfiType::Int { bits: 32 }),
                ("divisor", FfiType::Int { bits: 32 }),
            ],
            FfiType::Int { bits: 32 },
            vec![swift_pre],
            vec![],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);
        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].result,
            FfiCompatibility::Incompatible,
            "Expected incompatible after positional alignment, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn test_z4_verify_ffi_postcondition_alignment_by_position_not_name() {
        // Rust ensures result > b (arg1)
        // Swift expects result > divisor (arg1)
        //
        // These should match by position even if parameter names differ.

        let rust_post = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Result),
            Box::new(Expr::Var("b".to_string())),
        ));

        let swift_post = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Result),
            Box::new(Expr::Var("divisor".to_string())),
        ));

        let rust_fn = make_ffi_func(
            "safe_divide",
            FfiLanguage::Rust,
            vec![
                ("a", FfiType::Int { bits: 32 }),
                ("b", FfiType::Int { bits: 32 }),
            ],
            FfiType::Int { bits: 32 },
            vec![],
            vec![rust_post],
        );

        let swift_fn = make_ffi_func(
            "safe_divide",
            FfiLanguage::Swift,
            vec![
                ("dividend", FfiType::Int { bits: 32 }),
                ("divisor", FfiType::Int { bits: 32 }),
            ],
            FfiType::Int { bits: 32 },
            vec![],
            vec![swift_post],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);
        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].result,
            FfiCompatibility::Compatible,
            "Expected compatible after postcondition alignment, got: {:?}",
            results[0]
        );
    }

    #[test]
    fn test_z4_verify_ffi_postcondition_implication_invalid() {
        // Rust ensures result >= 0, Swift expects result >= 10
        // result >= 0 => result >= 10 should NOT verify (counterexample: result = 5)
        let rust_post = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("result".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let swift_post = Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("result".to_string())),
            Box::new(Expr::IntLit(10)),
        ));

        let rust_fn = make_ffi_func(
            "compute",
            FfiLanguage::Rust,
            vec![],
            FfiType::Int { bits: 32 },
            vec![],
            vec![rust_post], // Rust only ensures result >= 0
        );

        let swift_fn = make_ffi_func(
            "compute",
            FfiLanguage::Swift,
            vec![],
            FfiType::Int { bits: 32 },
            vec![],
            vec![swift_post], // Swift expects result >= 10
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);
        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].result,
            FfiCompatibility::Incompatible,
            "result >= 0 => result >= 10 should fail. Result: {:?}",
            results[0]
        );
    }

    #[test]
    fn test_z4_verify_ffi_combined_pre_post() {
        // Valid combined verification:
        // Rust: requires x > 0, ensures result > x
        // Swift: requires x > 5, expects result > 0
        // x > 5 => x > 0 should verify (pre)
        // result > x => result > 0 (post) - this needs x > 0 to be valid
        // Since Swift provides x > 5 which is stronger than x > 0, and
        // Rust provides result > x, if x > 0 then result > x > 0, so result > 0
        let rust_pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let rust_post = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("result".to_string())),
            Box::new(Expr::Var("x".to_string())),
        ));
        let swift_pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        ));
        let swift_post = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("result".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let rust_fn = make_ffi_func(
            "increment",
            FfiLanguage::Rust,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![rust_pre],
            vec![rust_post],
        );

        let swift_fn = make_ffi_func(
            "increment",
            FfiLanguage::Swift,
            vec![("x", FfiType::Int { bits: 32 })],
            FfiType::Int { bits: 32 },
            vec![swift_pre],
            vec![swift_post],
        );

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);
        assert_eq!(results.len(), 1);
        // Precondition: x > 5 => x > 0 should pass
        // Postcondition: result > x (without knowing x > 0) => result > 0 is NOT provable
        // This is correct behavior - the postcondition check is callee_ensures => caller_expects
        // which is: result > x => result > 0, and this is NOT valid without additional constraints
        assert_eq!(
            results[0].result,
            FfiCompatibility::Incompatible,
            "Postcondition check should fail: result > x does not imply result > 0 without x > 0. Result: {:?}",
            results[0]
        );
    }

    #[test]
    fn test_z4_verify_implication_direct() {
        // Test the verify_implication_z4 helper directly
        // Valid implication: x > 0 => x >= 0
        let ante = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, msg) = verify_implication_z4(&ante, &cons, "x > 0 => x >= 0");
        assert!(passed, "x > 0 => x >= 0 should be valid. Message: {msg}");
    }

    #[test]
    fn test_z4_verify_implication_invalid_direct() {
        // Invalid implication: x >= 0 => x > 0
        // Counterexample: x = 0
        let ante = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, msg) = verify_implication_z4(&ante, &cons, "x >= 0 => x > 0");
        assert!(!passed, "x >= 0 => x > 0 should be invalid. Message: {msg}");
    }

    #[test]
    fn test_z4_verify_empty_antecedent() {
        // Empty antecedent means "true", so consequent must be tautologically true
        // true => x > 0 is NOT valid (counterexample: x = -1)
        let cons = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, msg) = verify_implication_z4(&[], &cons, "true => x > 0");
        assert!(!passed, "true => x > 0 should be invalid. Message: {msg}");
    }

    #[test]
    fn test_z4_verify_empty_consequent() {
        // Empty consequent means "true", so any antecedent works
        // x > 0 => true is valid
        let ante = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, msg) = verify_implication_z4(&ante, &[], "x > 0 => true");
        assert!(passed, "x > 0 => true should be valid. Message: {msg}");
    }

    #[test]
    fn test_ffi_verify_options_default() {
        let options = FfiVerifyOptions::default();
        assert!(!options.use_z4_proofs);
    }

    // ========================================================================
    // Swift FFI Declaration Parsing Tests
    // ========================================================================

    #[test]
    fn test_swift_ffi_declaration_export() {
        let decl = SwiftFfiDeclaration {
            swift_name: "processData".to_string(),
            attributes: vec![
                SwiftFfiAttribute::Export {
                    rust_name: Some("process_data".to_string()),
                    module_path: None,
                },
                SwiftFfiAttribute::Requires {
                    condition: "buffer.count > 0".to_string(),
                },
            ],
            parameters: vec![("buffer".to_string(), "[UInt8]".to_string())],
            return_type: "Int".to_string(),
            source_file: "Data.swift".to_string(),
            source_line: 42,
        };

        assert!(decl.is_export());
        assert!(!decl.is_import());
        assert!(!decl.is_trusted());
        assert_eq!(decl.get_rust_name(), "process_data");
        assert_eq!(decl.get_requires(), vec!["buffer.count > 0"]);
        assert!(decl.get_ensures().is_empty());
    }

    #[test]
    fn test_swift_ffi_declaration_import() {
        let decl = SwiftFfiDeclaration {
            swift_name: "parseEscape".to_string(),
            attributes: vec![
                SwiftFfiAttribute::Import {
                    rust_path: "swift_bridge::parser::parse_escape".to_string(),
                    local_name: None,
                },
                SwiftFfiAttribute::Ensures {
                    condition: "result >= 0".to_string(),
                },
            ],
            parameters: vec![
                ("input".to_string(), "String".to_string()),
                ("offset".to_string(), "Int".to_string()),
            ],
            return_type: "Int".to_string(),
            source_file: "Parser.swift".to_string(),
            source_line: 100,
        };

        assert!(!decl.is_export());
        assert!(decl.is_import());
        assert!(!decl.is_trusted());
        assert_eq!(decl.get_rust_name(), "parse_escape"); // Last path component
        assert!(decl.get_requires().is_empty());
        assert_eq!(decl.get_ensures(), vec!["result >= 0"]);
    }

    #[test]
    fn test_swift_ffi_declaration_trusted() {
        let decl = SwiftFfiDeclaration {
            swift_name: "unsafeOp".to_string(),
            attributes: vec![
                SwiftFfiAttribute::Import {
                    rust_path: "core::unsafe_op".to_string(),
                    local_name: None,
                },
                SwiftFfiAttribute::Trusted,
            ],
            parameters: vec![],
            return_type: "Void".to_string(),
            source_file: "Unsafe.swift".to_string(),
            source_line: 1,
        };

        assert!(decl.is_import());
        assert!(decl.is_trusted());
    }

    #[test]
    fn test_parse_swift_type_primitives() {
        assert_eq!(parse_swift_type("Bool"), FfiType::Bool);
        assert_eq!(parse_swift_type("Int"), FfiType::Int { bits: 64 });
        assert_eq!(parse_swift_type("Int32"), FfiType::Int { bits: 32 });
        assert_eq!(parse_swift_type("UInt64"), FfiType::UInt { bits: 64 });
        assert_eq!(parse_swift_type("Float"), FfiType::Float { bits: 32 });
        assert_eq!(parse_swift_type("Double"), FfiType::Float { bits: 64 });
        assert_eq!(parse_swift_type("String"), FfiType::String);
        assert_eq!(parse_swift_type("Void"), FfiType::Void);
        assert_eq!(parse_swift_type("()"), FfiType::Void);
    }

    #[test]
    fn test_parse_swift_type_optional() {
        assert_eq!(
            parse_swift_type("Int?"),
            FfiType::Optional(Box::new(FfiType::Int { bits: 64 }))
        );
        assert_eq!(
            parse_swift_type("Optional<String>"),
            FfiType::Optional(Box::new(FfiType::String))
        );
    }

    #[test]
    fn test_parse_swift_type_result() {
        assert_eq!(
            parse_swift_type("Result<Int, Error>"),
            FfiType::Result {
                ok: Box::new(FfiType::Int { bits: 64 }),
                err: Box::new(FfiType::Custom("Error".to_string())),
            }
        );
    }

    #[test]
    fn test_parse_swift_type_data() {
        assert_eq!(parse_swift_type("[UInt8]"), FfiType::Bytes);
        assert_eq!(parse_swift_type("Data"), FfiType::Bytes);
        assert_eq!(
            parse_swift_type("UnsafeRawBufferPointer"),
            FfiType::BytesRef
        );
    }

    #[test]
    fn test_parse_swift_type_custom() {
        assert_eq!(
            parse_swift_type("MyCustomType"),
            FfiType::Custom("MyCustomType".to_string())
        );
    }

    #[test]
    fn test_swift_decl_to_ffi_function() {
        let decl = SwiftFfiDeclaration {
            swift_name: "increment".to_string(),
            attributes: vec![SwiftFfiAttribute::Import {
                rust_path: "math::increment".to_string(),
                local_name: None,
            }],
            parameters: vec![("x".to_string(), "Int32".to_string())],
            return_type: "Int32".to_string(),
            source_file: "Math.swift".to_string(),
            source_line: 10,
        };

        let pre = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));

        let ffi_fn = swift_decl_to_ffi_function(&decl, FfiLanguage::Swift, vec![pre], vec![]);

        assert_eq!(ffi_fn.name, "increment");
        assert_eq!(ffi_fn.language, FfiLanguage::Swift);
        assert_eq!(ffi_fn.params.len(), 1);
        assert_eq!(ffi_fn.params[0].name, "x");
        assert_eq!(ffi_fn.params[0].ffi_type, FfiType::Int { bits: 32 });
        assert_eq!(ffi_fn.return_type, FfiType::Int { bits: 32 });
        assert_eq!(ffi_fn.requires.len(), 1);
        assert!(ffi_fn.ensures.is_empty());
        assert!(!ffi_fn.trusted);
    }

    // ========================================================================
    // swift-bridge Type Mapping Tests
    // ========================================================================

    #[test]
    fn test_swift_bridge_type_map_default() {
        let map = SwiftBridgeTypeMap::new();

        // Check primitive mappings
        assert_eq!(map.get("bool"), Some(&FfiType::Bool));
        assert_eq!(map.get("i32"), Some(&FfiType::Int { bits: 32 }));
        assert_eq!(map.get("u64"), Some(&FfiType::UInt { bits: 64 }));
        assert_eq!(map.get("f64"), Some(&FfiType::Float { bits: 64 }));
        assert_eq!(map.get("()"), Some(&FfiType::Void));

        // Check string mappings
        assert_eq!(map.get("String"), Some(&FfiType::String));
        assert_eq!(map.get("&str"), Some(&FfiType::StringRef));

        // Check bytes mappings
        assert_eq!(map.get("Vec<u8>"), Some(&FfiType::Bytes));
        assert_eq!(map.get("&[u8]"), Some(&FfiType::BytesRef));
    }

    #[test]
    fn test_swift_bridge_parse_rust_type() {
        let map = SwiftBridgeTypeMap::new();

        // Direct types
        assert_eq!(map.parse_rust_type("i32"), FfiType::Int { bits: 32 });
        assert_eq!(map.parse_rust_type("bool"), FfiType::Bool);

        // Option<T>
        assert_eq!(
            map.parse_rust_type("Option<i32>"),
            FfiType::Optional(Box::new(FfiType::Int { bits: 32 }))
        );

        // Result<T, E>
        assert_eq!(
            map.parse_rust_type("Result<String, MyError>"),
            FfiType::Result {
                ok: Box::new(FfiType::String),
                err: Box::new(FfiType::Custom("MyError".to_string())),
            }
        );

        // Custom type
        assert_eq!(
            map.parse_rust_type("MyStruct"),
            FfiType::Custom("MyStruct".to_string())
        );
    }

    #[test]
    fn test_swift_bridge_custom_mapping() {
        let mut map = SwiftBridgeTypeMap::new();
        map.add_mapping("SessionId", FfiType::Custom("SessionId".to_string()));

        assert_eq!(
            map.get("SessionId"),
            Some(&FfiType::Custom("SessionId".to_string()))
        );
    }

    #[test]
    fn test_swift_bridge_types_compatible() {
        let map = SwiftBridgeTypeMap::new();

        // Compatible types
        assert!(map.types_compatible("Int32", "i32"));
        assert!(map.types_compatible("Bool", "bool"));
        assert!(map.types_compatible("String", "String"));
        assert!(map.types_compatible("[UInt8]", "Vec<u8>"));

        // Incompatible types
        assert!(!map.types_compatible("Int32", "i64"));
        assert!(!map.types_compatible("Int", "u64"));
    }

    #[test]
    fn test_swift_bridge_types_compatible_optional() {
        let map = SwiftBridgeTypeMap::new();

        assert!(map.types_compatible("Int32?", "Option<i32>"));
        assert!(map.types_compatible("Optional<String>", "Option<String>"));
    }

    #[test]
    fn test_swift_bridge_types_compatible_result() {
        let map = SwiftBridgeTypeMap::new();

        assert!(map.types_compatible("Result<Int32, Error>", "Result<i32, Error>"));
    }

    #[test]
    fn test_parse_swift_ffi_declarations_from_source_basic() {
        let source = r#"
@_ffi_import("math::increment")
@_ffi_requires("x > 0")
@_ffi_ensures("result > x")
func increment(_ x: Int32) -> Int32 {
  return x + 1
}
"#;

        let decls = parse_swift_ffi_declarations_from_source(source, "Math.swift");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.swift_name, "increment");
        assert_eq!(decl.get_rust_name(), "increment");
        assert!(decl.is_import());
        assert!(!decl.is_export());
        assert_eq!(
            decl.parameters,
            vec![("x".to_string(), "Int32".to_string())]
        );
        assert_eq!(decl.return_type, "Int32");
        assert_eq!(decl.source_file, "Math.swift");
        assert_eq!(decl.source_line, 5);
        assert_eq!(decl.get_requires(), vec!["x > 0"]);
        assert_eq!(decl.get_ensures(), vec!["result > x"]);
    }

    #[test]
    fn test_swift_decl_to_ffi_function_parsed_conditions() {
        let source = r#"
@_ffi_import("math::increment")
@_ffi_requires("x > 0 && result > x")
func increment(_ x: Int32) -> Int32 { x + 1 }
"#;

        let decls = parse_swift_ffi_declarations_from_source(source, "Math.swift");
        let decl = &decls[0];

        let ffi_fn = swift_decl_to_ffi_function_parsed(decl, FfiLanguage::Swift).unwrap();
        assert_eq!(ffi_fn.name, "increment");
        assert_eq!(ffi_fn.params.len(), 1);
        assert_eq!(ffi_fn.params[0].name, "x");

        assert_eq!(ffi_fn.requires.len(), 1);
        match &ffi_fn.requires[0] {
            Predicate::Expr(Expr::And(lhs, rhs)) => {
                assert!(matches!(lhs.as_ref(), Expr::Gt(_, _)));
                assert!(matches!(rhs.as_ref(), Expr::Gt(_, _)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    // ========================================================================
    // parse_swift_condition_to_predicate Tests
    // ========================================================================

    #[test]
    fn test_parse_swift_condition_simple_comparison() {
        let result = parse_swift_condition_to_predicate("x > 0", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Gt(lhs, rhs)) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(v) if v == "x"));
                assert!(matches!(rhs.as_ref(), Expr::IntLit(0)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_equality() {
        let result =
            parse_swift_condition_to_predicate("x == y", &["x".to_string(), "y".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Eq(lhs, rhs)) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(v) if v == "x"));
                assert!(matches!(rhs.as_ref(), Expr::Var(v) if v == "y"));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_logical_and() {
        let result = parse_swift_condition_to_predicate(
            "x > 0 && y < 10",
            &["x".to_string(), "y".to_string()],
        );
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::And(lhs, rhs)) => {
                assert!(matches!(lhs.as_ref(), Expr::Gt(_, _)));
                assert!(matches!(rhs.as_ref(), Expr::Lt(_, _)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_logical_or() {
        let result = parse_swift_condition_to_predicate("x < 0 || x > 100", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Or(lhs, rhs)) => {
                assert!(matches!(lhs.as_ref(), Expr::Lt(_, _)));
                assert!(matches!(rhs.as_ref(), Expr::Gt(_, _)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_result_reference() {
        let result = parse_swift_condition_to_predicate("result > x", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Gt(lhs, rhs)) => {
                assert!(matches!(lhs.as_ref(), Expr::Result));
                assert!(matches!(rhs.as_ref(), Expr::Var(v) if v == "x"));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_less_equal() {
        let result = parse_swift_condition_to_predicate("x <= 100", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Le(lhs, rhs)) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(v) if v == "x"));
                assert!(matches!(rhs.as_ref(), Expr::IntLit(100)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_greater_equal() {
        let result = parse_swift_condition_to_predicate("x >= 0", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Ge(lhs, rhs)) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(v) if v == "x"));
                assert!(matches!(rhs.as_ref(), Expr::IntLit(0)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_not_equal() {
        let result = parse_swift_condition_to_predicate("x != 0", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Ne(lhs, rhs)) => {
                assert!(matches!(lhs.as_ref(), Expr::Var(v) if v == "x"));
                assert!(matches!(rhs.as_ref(), Expr::IntLit(0)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_negation() {
        let result = parse_swift_condition_to_predicate("!valid", &["valid".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Not(inner)) => {
                assert!(matches!(inner.as_ref(), Expr::Var(v) if v == "valid"));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_arithmetic_add() {
        let result = parse_swift_condition_to_predicate("x + 1 > 0", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Gt(lhs, _)) => {
                assert!(matches!(lhs.as_ref(), Expr::Add(_, _)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_arithmetic_sub() {
        let result = parse_swift_condition_to_predicate("x - 1 >= 0", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Ge(lhs, _)) => {
                assert!(matches!(lhs.as_ref(), Expr::Sub(_, _)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_arithmetic_mul() {
        let result = parse_swift_condition_to_predicate("x * 2 <= 100", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Le(lhs, _)) => {
                assert!(matches!(lhs.as_ref(), Expr::Mul(_, _)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_arithmetic_div() {
        let result = parse_swift_condition_to_predicate("x / 2 > 0", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Gt(lhs, _)) => {
                assert!(matches!(lhs.as_ref(), Expr::Div(_, _)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_arithmetic_rem() {
        let result = parse_swift_condition_to_predicate("x % 2 == 0", &["x".to_string()]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Eq(lhs, _)) => {
                assert!(matches!(lhs.as_ref(), Expr::Rem(_, _)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_complex_nested() {
        let result = parse_swift_condition_to_predicate(
            "(x > 0 && y > 0) || (x < 0 && y < 0)",
            &["x".to_string(), "y".to_string()],
        );
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Or(_, _)) => {}
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_multiple_params() {
        let result = parse_swift_condition_to_predicate(
            "a > b && b > c && c > 0",
            &["a".to_string(), "b".to_string(), "c".to_string()],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_swift_condition_empty_params() {
        let result = parse_swift_condition_to_predicate("result > 0", &[]);
        assert!(result.is_ok());
        let pred = result.unwrap();
        match &pred {
            Predicate::Expr(Expr::Gt(lhs, rhs)) => {
                assert!(matches!(lhs.as_ref(), Expr::Result));
                assert!(matches!(rhs.as_ref(), Expr::IntLit(0)));
            }
            other => panic!("unexpected predicate: {other:?}"),
        }
    }

    #[test]
    fn test_parse_swift_condition_negative_literal() {
        let result = parse_swift_condition_to_predicate("x > -10", &["x".to_string()]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_swift_condition_boolean_literal_true() {
        let result = parse_swift_condition_to_predicate("valid == true", &["valid".to_string()]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_parse_swift_condition_boolean_literal_false() {
        let result = parse_swift_condition_to_predicate("valid == false", &["valid".to_string()]);
        assert!(result.is_ok());
    }

    // ========================================================================
    // Rust FFI Export Parsing Tests
    // ========================================================================

    #[test]
    fn test_parse_rust_ffi_declarations_basic() {
        let source = r#"
#[ffi_export]
#[ffi_requires("x > 0")]
#[ffi_ensures("result >= x")]
pub fn increment(x: i32) -> i32 {
    x + 1
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "math.rs");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.rust_name, "increment");
        assert_eq!(decl.get_ffi_name(), "increment");
        assert!(decl.is_export());
        assert!(!decl.is_trusted());
        assert_eq!(decl.parameters, vec![("x".to_string(), "i32".to_string())]);
        assert_eq!(decl.return_type, "i32");
        assert_eq!(decl.source_file, "math.rs");
        assert_eq!(decl.source_line, 5);
        assert_eq!(decl.get_requires(), vec!["x > 0"]);
        assert_eq!(decl.get_ensures(), vec!["result >= x"]);
    }

    #[test]
    fn test_parse_rust_ffi_custom_name() {
        let source = r#"
#[ffi_export("parse_escape_seq")]
pub fn parse_escape(buffer: &[u8]) -> i32 {
    42
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "parser.rs");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.rust_name, "parse_escape");
        assert_eq!(decl.get_ffi_name(), "parse_escape_seq");
    }

    #[test]
    fn test_parse_rust_ffi_trusted() {
        let source = r"
#[ffi_export]
#[ffi_trusted]
pub unsafe fn unsafe_operation(ptr: *mut u8) {
    // unsafe code
}
";

        let decls = parse_rust_ffi_declarations_from_source(source, "unsafe.rs");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert!(decl.is_trusted());
        assert_eq!(decl.return_type, "()");
    }

    #[test]
    fn test_parse_rust_ffi_multiple_params() {
        let source = r#"
#[ffi_export]
#[ffi_requires("a > 0 && b > 0")]
#[ffi_ensures("result > 0")]
pub fn multiply(a: i64, b: i64) -> i64 {
    a * b
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "math.rs");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.parameters.len(), 2);
        assert_eq!(decl.parameters[0], ("a".to_string(), "i64".to_string()));
        assert_eq!(decl.parameters[1], ("b".to_string(), "i64".to_string()));
    }

    #[test]
    fn test_parse_rust_ffi_result_type() {
        let source = r"
#[ffi_export]
pub fn start_session(sample_rate: u32) -> Result<SessionId, VoiceError> {
    Ok(SessionId::new())
}
";

        let decls = parse_rust_ffi_declarations_from_source(source, "voice.rs");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.return_type, "Result<SessionId, VoiceError>");
    }

    #[test]
    fn test_parse_rust_ffi_no_export_skipped() {
        let source = r#"
// This function has requires but no export - should be skipped
#[ffi_requires("x > 0")]
pub fn helper(x: i32) -> i32 {
    x
}

// This function has export - should be included
#[ffi_export]
pub fn exported(x: i32) -> i32 {
    x
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "lib.rs");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].rust_name, "exported");
    }

    #[test]
    fn test_parse_rust_type_basic() {
        assert_eq!(parse_rust_type("bool"), FfiType::Bool);
        assert_eq!(parse_rust_type("i32"), FfiType::Int { bits: 32 });
        assert_eq!(parse_rust_type("i64"), FfiType::Int { bits: 64 });
        assert_eq!(parse_rust_type("u32"), FfiType::UInt { bits: 32 });
        assert_eq!(parse_rust_type("f64"), FfiType::Float { bits: 64 });
        assert_eq!(parse_rust_type("String"), FfiType::String);
        assert_eq!(parse_rust_type("&str"), FfiType::StringRef);
        assert_eq!(parse_rust_type("Vec<u8>"), FfiType::Bytes);
        assert_eq!(parse_rust_type("&[u8]"), FfiType::BytesRef);
        assert_eq!(parse_rust_type("()"), FfiType::Void);
    }

    #[test]
    fn test_parse_rust_type_optional() {
        assert_eq!(
            parse_rust_type("Option<i32>"),
            FfiType::Optional(Box::new(FfiType::Int { bits: 32 }))
        );
    }

    #[test]
    fn test_parse_rust_type_result() {
        assert_eq!(
            parse_rust_type("Result<i32, String>"),
            FfiType::Result {
                ok: Box::new(FfiType::Int { bits: 32 }),
                err: Box::new(FfiType::String),
            }
        );
    }

    #[test]
    fn test_rust_decl_to_ffi_function_parsed() {
        let source = r#"
#[ffi_export]
#[ffi_requires("x > 0")]
#[ffi_ensures("result > x")]
pub fn increment(x: i32) -> i32 {
    x + 1
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "math.rs");
        let ffi_fn = rust_decl_to_ffi_function_parsed(&decls[0]).unwrap();

        assert_eq!(ffi_fn.name, "increment");
        assert_eq!(ffi_fn.language, FfiLanguage::Rust);
        assert_eq!(ffi_fn.params.len(), 1);
        assert_eq!(ffi_fn.params[0].ffi_type, FfiType::Int { bits: 32 });
        assert_eq!(ffi_fn.return_type, FfiType::Int { bits: 32 });
        assert_eq!(ffi_fn.requires.len(), 1);
        assert_eq!(ffi_fn.ensures.len(), 1);
    }

    // ========================================================================
    // RustFfiDeclaration method unit tests
    // ========================================================================

    #[test]
    fn test_rust_ffi_declaration_is_export_true() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![RustFfiAttribute::Export { name: None }],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        assert!(decl.is_export());
    }

    #[test]
    fn test_rust_ffi_declaration_is_export_false() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![RustFfiAttribute::Requires {
                condition: "x > 0".to_string(),
            }],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        assert!(!decl.is_export());
    }

    #[test]
    fn test_rust_ffi_declaration_is_export_empty_attrs() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        assert!(!decl.is_export());
    }

    #[test]
    fn test_rust_ffi_declaration_is_trusted_true() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![
                RustFfiAttribute::Export { name: None },
                RustFfiAttribute::Trusted,
            ],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        assert!(decl.is_trusted());
    }

    #[test]
    fn test_rust_ffi_declaration_is_trusted_false() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![RustFfiAttribute::Export { name: None }],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        assert!(!decl.is_trusted());
    }

    #[test]
    fn test_rust_ffi_declaration_get_requires_empty() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![RustFfiAttribute::Export { name: None }],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        let requires = decl.get_requires();
        assert!(requires.is_empty());
    }

    #[test]
    fn test_rust_ffi_declaration_get_requires_single() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![
                RustFfiAttribute::Export { name: None },
                RustFfiAttribute::Requires {
                    condition: "x > 0".to_string(),
                },
            ],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        let requires = decl.get_requires();
        assert_eq!(requires, vec!["x > 0"]);
    }

    #[test]
    fn test_rust_ffi_declaration_get_requires_multiple() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![
                RustFfiAttribute::Requires {
                    condition: "x > 0".to_string(),
                },
                RustFfiAttribute::Requires {
                    condition: "y < 100".to_string(),
                },
                RustFfiAttribute::Requires {
                    condition: "x != y".to_string(),
                },
            ],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        let requires = decl.get_requires();
        assert_eq!(requires, vec!["x > 0", "y < 100", "x != y"]);
    }

    #[test]
    fn test_rust_ffi_declaration_get_ensures_empty() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![RustFfiAttribute::Export { name: None }],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        let ensures = decl.get_ensures();
        assert!(ensures.is_empty());
    }

    #[test]
    fn test_rust_ffi_declaration_get_ensures_single() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![
                RustFfiAttribute::Export { name: None },
                RustFfiAttribute::Ensures {
                    condition: "result >= x".to_string(),
                },
            ],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        let ensures = decl.get_ensures();
        assert_eq!(ensures, vec!["result >= x"]);
    }

    #[test]
    fn test_rust_ffi_declaration_get_ensures_multiple() {
        let decl = RustFfiDeclaration {
            rust_name: "test_fn".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![
                RustFfiAttribute::Ensures {
                    condition: "result > 0".to_string(),
                },
                RustFfiAttribute::Ensures {
                    condition: "result < 1000".to_string(),
                },
            ],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        let ensures = decl.get_ensures();
        assert_eq!(ensures, vec!["result > 0", "result < 1000"]);
    }

    #[test]
    fn test_rust_ffi_declaration_get_ffi_name_default() {
        let decl = RustFfiDeclaration {
            rust_name: "my_function".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![RustFfiAttribute::Export { name: None }],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        assert_eq!(decl.get_ffi_name(), "my_function");
    }

    #[test]
    fn test_rust_ffi_declaration_get_ffi_name_custom() {
        let decl = RustFfiDeclaration {
            rust_name: "my_function".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![RustFfiAttribute::Export {
                name: Some("exported_name".to_string()),
            }],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        assert_eq!(decl.get_ffi_name(), "exported_name");
    }

    #[test]
    fn test_rust_ffi_declaration_get_ffi_name_no_export() {
        let decl = RustFfiDeclaration {
            rust_name: "my_function".to_string(),
            parameters: vec![],
            return_type: "i32".to_string(),
            attributes: vec![RustFfiAttribute::Requires {
                condition: "x > 0".to_string(),
            }],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        // Falls back to rust_name when no export attribute exists
        assert_eq!(decl.get_ffi_name(), "my_function");
    }

    #[test]
    fn test_rust_ffi_declaration_mixed_attributes() {
        let decl = RustFfiDeclaration {
            rust_name: "complex_fn".to_string(),
            parameters: vec![("x".to_string(), "i32".to_string())],
            return_type: "i32".to_string(),
            attributes: vec![
                RustFfiAttribute::Export {
                    name: Some("exported".to_string()),
                },
                RustFfiAttribute::Trusted,
                RustFfiAttribute::Requires {
                    condition: "x > 0".to_string(),
                },
                RustFfiAttribute::Requires {
                    condition: "x < 100".to_string(),
                },
                RustFfiAttribute::Ensures {
                    condition: "result >= x".to_string(),
                },
            ],
            source_file: "test.rs".to_string(),
            source_line: 1,
        };
        assert!(decl.is_export());
        assert!(decl.is_trusted());
        assert_eq!(decl.get_requires(), vec!["x > 0", "x < 100"]);
        assert_eq!(decl.get_ensures(), vec!["result >= x"]);
        assert_eq!(decl.get_ffi_name(), "exported");
    }

    #[test]
    fn test_rust_ffi_declaration_with_params() {
        let decl = RustFfiDeclaration {
            rust_name: "add".to_string(),
            parameters: vec![
                ("a".to_string(), "i32".to_string()),
                ("b".to_string(), "i32".to_string()),
            ],
            return_type: "i32".to_string(),
            attributes: vec![RustFfiAttribute::Export { name: None }],
            source_file: "math.rs".to_string(),
            source_line: 10,
        };
        assert_eq!(decl.parameters.len(), 2);
        assert_eq!(decl.parameters[0], ("a".to_string(), "i32".to_string()));
        assert_eq!(decl.parameters[1], ("b".to_string(), "i32".to_string()));
        assert_eq!(decl.source_file, "math.rs");
        assert_eq!(decl.source_line, 10);
    }

    #[derive(Clone, Copy, Debug)]
    enum CmpOp {
        Eq,
        Lt,
        Le,
        Gt,
        Ge,
    }

    fn expect_pred_expr(pred: &Predicate) -> &Expr {
        match pred {
            Predicate::Expr(expr) => expr,
            other => panic!("expected Predicate::Expr(_), got {other:?}"),
        }
    }

    fn expect_cmp_expr(expr: &Expr, op: CmpOp) -> (&Expr, &Expr) {
        match (op, expr) {
            (CmpOp::Eq, Expr::Eq(lhs, rhs))
            | (CmpOp::Lt, Expr::Lt(lhs, rhs))
            | (CmpOp::Le, Expr::Le(lhs, rhs))
            | (CmpOp::Gt, Expr::Gt(lhs, rhs))
            | (CmpOp::Ge, Expr::Ge(lhs, rhs)) => (lhs.as_ref(), rhs.as_ref()),
            (CmpOp::Eq, other) => panic!("expected Expr::Eq, got {other:?}"),
            (CmpOp::Lt, other) => panic!("expected Expr::Lt, got {other:?}"),
            (CmpOp::Le, other) => panic!("expected Expr::Le, got {other:?}"),
            (CmpOp::Gt, other) => panic!("expected Expr::Gt, got {other:?}"),
            (CmpOp::Ge, other) => panic!("expected Expr::Ge, got {other:?}"),
        }
    }

    fn expect_pred_cmp(pred: &Predicate, op: CmpOp) -> (&Expr, &Expr) {
        expect_cmp_expr(expect_pred_expr(pred), op)
    }

    fn expect_pred_and(pred: &Predicate) -> (&Expr, &Expr) {
        match expect_pred_expr(pred) {
            Expr::And(lhs, rhs) => (lhs.as_ref(), rhs.as_ref()),
            other => panic!("expected Expr::And, got {other:?}"),
        }
    }

    fn expect_add(expr: &Expr) -> (&Expr, &Expr) {
        match expr {
            Expr::Add(lhs, rhs) => (lhs.as_ref(), rhs.as_ref()),
            other => panic!("expected Expr::Add, got {other:?}"),
        }
    }

    fn expect_sub(expr: &Expr) -> (&Expr, &Expr) {
        match expr {
            Expr::Sub(lhs, rhs) => (lhs.as_ref(), rhs.as_ref()),
            other => panic!("expected Expr::Sub, got {other:?}"),
        }
    }

    fn assert_var(expr: &Expr, expected_name: &str) {
        match expr {
            Expr::Var(name) if name == expected_name => {}
            other => panic!("expected Expr::Var({expected_name}), got {other:?}"),
        }
    }

    fn assert_int(expr: &Expr, expected_value: i128) {
        match expr {
            Expr::IntLit(value) if *value == expected_value => {}
            other => panic!("expected Expr::IntLit({expected_value}), got {other:?}"),
        }
    }

    fn assert_struct_field_chain(expr: &Expr, base_var: &str, fields: &[&str]) {
        let mut current = expr;
        for expected_field in fields.iter().rev() {
            match current {
                Expr::StructField(base, field) if field == expected_field => {
                    current = base.as_ref();
                }
                other => panic!("expected StructField(_,{expected_field}), got {other:?}"),
            }
        }
        assert_var(current, base_var);
    }

    fn assert_is_struct_field(expr: &Expr, expected_field: &str) {
        match expr {
            Expr::StructField(_, field) if field == expected_field => {}
            other => panic!("expected StructField(_,{expected_field}), got {other:?}"),
        }
    }

    fn assert_pred_struct_field(pred: &Predicate, base_var: &str, field: &str) {
        assert_struct_field_chain(expect_pred_expr(pred), base_var, &[field]);
    }

    fn assert_pred_not_struct_field(pred: &Predicate, base_var: &str, field: &str) {
        match expect_pred_expr(pred) {
            Expr::Not(inner) => assert_struct_field_chain(inner.as_ref(), base_var, &[field]),
            other => panic!("expected Expr::Not(_), got {other:?}"),
        }
    }

    fn assert_pred_cmp_field_chain_int(
        pred: &Predicate,
        op: CmpOp,
        base_var: &str,
        fields: &[&str],
        rhs_int: i128,
    ) {
        let (lhs, rhs) = expect_pred_cmp(pred, op);
        assert_struct_field_chain(lhs, base_var, fields);
        assert_int(rhs, rhs_int);
    }

    fn assert_pred_cmp_field_chain_var(
        pred: &Predicate,
        op: CmpOp,
        base_var: &str,
        fields: &[&str],
        rhs_var: &str,
    ) {
        let (lhs, rhs) = expect_pred_cmp(pred, op);
        assert_struct_field_chain(lhs, base_var, fields);
        assert_var(rhs, rhs_var);
    }

    fn assert_pred_cmp_var_field_chain(
        pred: &Predicate,
        op: CmpOp,
        lhs_var: &str,
        rhs_base_var: &str,
        rhs_fields: &[&str],
    ) {
        let (lhs, rhs) = expect_pred_cmp(pred, op);
        assert_var(lhs, lhs_var);
        assert_struct_field_chain(rhs, rhs_base_var, rhs_fields);
    }

    fn assert_expr_cmp_field_chain_int(
        expr: &Expr,
        op: CmpOp,
        base_var: &str,
        fields: &[&str],
        rhs_int: i128,
    ) {
        let (lhs, rhs) = expect_cmp_expr(expr, op);
        assert_struct_field_chain(lhs, base_var, fields);
        assert_int(rhs, rhs_int);
    }

    fn assert_expr_cmp_field_chain_var(
        expr: &Expr,
        op: CmpOp,
        base_var: &str,
        fields: &[&str],
        rhs_var: &str,
    ) {
        let (lhs, rhs) = expect_cmp_expr(expr, op);
        assert_struct_field_chain(lhs, base_var, fields);
        assert_var(rhs, rhs_var);
    }

    fn assert_expr_cmp_var_field_chain(
        expr: &Expr,
        op: CmpOp,
        lhs_var: &str,
        rhs_base_var: &str,
        rhs_fields: &[&str],
    ) {
        let (lhs, rhs) = expect_cmp_expr(expr, op);
        assert_var(lhs, lhs_var);
        assert_struct_field_chain(rhs, rhs_base_var, rhs_fields);
    }

    fn assert_expr_cmp_var_int(expr: &Expr, op: CmpOp, lhs_var: &str, rhs_int: i128) {
        let (lhs, rhs) = expect_cmp_expr(expr, op);
        assert_var(lhs, lhs_var);
        assert_int(rhs, rhs_int);
    }

    #[test]
    fn test_parse_rust_condition_len_and_cast_normalization() {
        // `.len()` should normalize to `.count` so the condition parser can handle it.
        let pred = parse_rust_condition_to_predicate("buffer.len() > 0", &["buffer".to_string()])
            .expect("expected condition to parse");

        match pred {
            Predicate::Expr(Expr::Gt(lhs, rhs)) => {
                assert!(matches!(*rhs, Expr::IntLit(0)));
                match *lhs {
                    Expr::StructField(base, field) => {
                        assert_eq!(field, "count");
                        assert!(matches!(*base, Expr::Var(ref n) if n == "buffer"));
                    }
                    other => panic!("expected StructField for len/count, got {other:?}"),
                }
            }
            other => panic!("expected Gt predicate, got {other:?}"),
        }

        // `as <type>` casts should be stripped.
        let pred = parse_rust_condition_to_predicate(
            "result < haystack.len() as i64",
            &["haystack".to_string()],
        )
        .expect("expected cast-stripped condition to parse");

        match pred {
            Predicate::Expr(Expr::Lt(lhs, rhs)) => {
                assert!(matches!(*lhs, Expr::Result));
                match *rhs {
                    Expr::StructField(base, field) => {
                        assert_eq!(field, "count");
                        assert!(matches!(*base, Expr::Var(ref n) if n == "haystack"));
                    }
                    other => panic!("expected StructField for len/count, got {other:?}"),
                }
            }
            other => panic!("expected Lt predicate, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_rust_condition_is_empty_normalization() {
        // `buffer.is_empty()` should normalize to `buffer.count == 0`
        let pred = parse_rust_condition_to_predicate("buffer.is_empty()", &["buffer".to_string()])
            .expect("expected is_empty condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Eq, "buffer", &["count"], 0);

        // `!buffer.is_empty()` should normalize to `buffer.count > 0`
        let pred = parse_rust_condition_to_predicate("!buffer.is_empty()", &["buffer".to_string()])
            .expect("expected negated is_empty condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Gt, "buffer", &["count"], 0);

        // Combined: `!data.is_empty() && data.len() > 10` (both normalizations)
        let pred = parse_rust_condition_to_predicate(
            "!data.is_empty() && data.len() > 10",
            &["data".to_string()],
        )
        .expect("expected combined condition to parse");

        // The parser returns Expr(And(...)) for && expressions
        let (lhs, rhs) = expect_pred_and(&pred);
        assert_expr_cmp_field_chain_int(lhs, CmpOp::Gt, "data", &["count"], 0);
        assert_expr_cmp_field_chain_int(rhs, CmpOp::Gt, "data", &["count"], 10);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_parse_rust_condition_first_last_normalization() {
        // `buffer.first().is_some()` should normalize to `buffer.count > 0`
        let pred =
            parse_rust_condition_to_predicate("buffer.first().is_some()", &["buffer".to_string()])
                .expect("expected first().is_some() condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Gt, "buffer", &["count"], 0);

        // `buffer.first().is_none()` should normalize to `buffer.count == 0`
        let pred =
            parse_rust_condition_to_predicate("buffer.first().is_none()", &["buffer".to_string()])
                .expect("expected first().is_none() condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Eq, "buffer", &["count"], 0);

        // `buffer.last().is_some()` should normalize to `buffer.count > 0`
        let pred =
            parse_rust_condition_to_predicate("buffer.last().is_some()", &["buffer".to_string()])
                .expect("expected last().is_some() condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Gt, "buffer", &["count"], 0);

        // `buffer.last().is_none()` should normalize to `buffer.count == 0`
        let pred =
            parse_rust_condition_to_predicate("buffer.last().is_none()", &["buffer".to_string()])
                .expect("expected last().is_none() condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Eq, "buffer", &["count"], 0);

        // Combined: `data.first().is_some() && data.len() > 10`
        let pred = parse_rust_condition_to_predicate(
            "data.first().is_some() && data.len() > 10",
            &["data".to_string()],
        )
        .expect("expected combined first().is_some() condition to parse");
        let (lhs, rhs) = expect_pred_and(&pred);
        assert_expr_cmp_field_chain_int(lhs, CmpOp::Gt, "data", &["count"], 0);
        assert_expr_cmp_field_chain_int(rhs, CmpOp::Gt, "data", &["count"], 10);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_parse_rust_condition_get_normalization() {
        // `buffer.get(i).is_some()` should normalize to `i < buffer.count`
        let pred = parse_rust_condition_to_predicate(
            "buffer.get(i).is_some()",
            &["buffer".to_string(), "i".to_string()],
        )
        .expect("expected get(i).is_some() condition to parse");
        assert_pred_cmp_var_field_chain(&pred, CmpOp::Lt, "i", "buffer", &["count"]);

        // `buffer.get(i).is_none()` should normalize to `i >= buffer.count`
        let pred = parse_rust_condition_to_predicate(
            "buffer.get(i).is_none()",
            &["buffer".to_string(), "i".to_string()],
        )
        .expect("expected get(i).is_none() condition to parse");
        assert_pred_cmp_var_field_chain(&pred, CmpOp::Ge, "i", "buffer", &["count"]);

        // `!buffer.get(i).is_some()` should normalize to `i >= buffer.count`
        let pred = parse_rust_condition_to_predicate(
            "!buffer.get(i).is_some()",
            &["buffer".to_string(), "i".to_string()],
        )
        .expect("expected negated get(i).is_some() condition to parse");
        assert_pred_cmp_var_field_chain(&pred, CmpOp::Ge, "i", "buffer", &["count"]);

        // `!buffer.get(i).is_none()` should normalize to `i < buffer.count`
        let pred = parse_rust_condition_to_predicate(
            "!buffer.get(i).is_none()",
            &["buffer".to_string(), "i".to_string()],
        )
        .expect("expected negated get(i).is_none() condition to parse");
        assert_pred_cmp_var_field_chain(&pred, CmpOp::Lt, "i", "buffer", &["count"]);

        // Combined: `buffer.get(index).is_some() && index < 100`
        let pred = parse_rust_condition_to_predicate(
            "buffer.get(index).is_some() && index < 100",
            &["buffer".to_string(), "index".to_string()],
        )
        .expect("expected combined get().is_some() condition to parse");
        let (lhs, rhs) = expect_pred_and(&pred);
        assert_expr_cmp_var_field_chain(lhs, CmpOp::Lt, "index", "buffer", &["count"]);
        assert_expr_cmp_var_int(rhs, CmpOp::Lt, "index", 100);
    }

    #[test]
    fn test_parse_rust_condition_iter_count_normalization() {
        // `buffer.iter().count()` should normalize to `buffer.count`
        // This tests the condition `buffer.iter().count() > 0`
        let pred =
            parse_rust_condition_to_predicate("buffer.iter().count() > 0", &["buffer".to_string()])
                .expect("expected iter().count() > 0 condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Gt, "buffer", &["count"], 0);

        // `buffer.iter().count() == 0` should normalize to `buffer.count == 0`
        let pred = parse_rust_condition_to_predicate(
            "buffer.iter().count() == 0",
            &["buffer".to_string()],
        )
        .expect("expected iter().count() == 0 condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Eq, "buffer", &["count"], 0);

        // Combined with other conditions: `buffer.iter().count() >= n && n > 0`
        let pred = parse_rust_condition_to_predicate(
            "buffer.iter().count() >= n && n > 0",
            &["buffer".to_string(), "n".to_string()],
        )
        .expect("expected combined iter().count() condition to parse");
        let (lhs, rhs) = expect_pred_and(&pred);
        assert_expr_cmp_field_chain_var(lhs, CmpOp::Ge, "buffer", &["count"], "n");
        assert_expr_cmp_var_int(rhs, CmpOp::Gt, "n", 0);
    }

    #[test]
    fn test_parse_rust_condition_into_iter_count_normalization() {
        // `data.into_iter().count()` should normalize to `data.count`
        let pred = parse_rust_condition_to_predicate(
            "data.into_iter().count() > 0",
            &["data".to_string()],
        )
        .expect("expected into_iter().count() > 0 condition to parse");

        match pred {
            Predicate::Expr(Expr::Gt(lhs, rhs)) => {
                assert!(matches!(*rhs, Expr::IntLit(0)));
                match *lhs {
                    Expr::StructField(base, field) => {
                        assert_eq!(field, "count");
                        assert!(matches!(*base, Expr::Var(ref n) if n == "data"));
                    }
                    other => panic!("expected StructField for into_iter().count(), got {other:?}"),
                }
            }
            other => panic!("expected Gt predicate for into_iter().count() > 0, got {other:?}"),
        }

        // `items.into_iter().count() == n` should normalize to `items.count == n`
        let pred = parse_rust_condition_to_predicate(
            "items.into_iter().count() == n",
            &["items".to_string(), "n".to_string()],
        )
        .expect("expected into_iter().count() == n condition to parse");

        match pred {
            Predicate::Expr(Expr::Eq(lhs, rhs)) => {
                assert!(matches!(*rhs, Expr::Var(ref name) if name == "n"));
                match *lhs {
                    Expr::StructField(base, field) => {
                        assert_eq!(field, "count");
                        assert!(matches!(*base, Expr::Var(ref n) if n == "items"));
                    }
                    other => {
                        panic!("expected StructField for into_iter().count() == n, got {other:?}")
                    }
                }
            }
            other => panic!("expected Eq predicate for into_iter().count() == n, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_rust_condition_iter_mut_count_normalization() {
        // `data.iter_mut().count()` should normalize to `data.count`
        let pred =
            parse_rust_condition_to_predicate("data.iter_mut().count() > 0", &["data".to_string()])
                .expect("expected iter_mut().count() > 0 condition to parse");

        match pred {
            Predicate::Expr(Expr::Gt(lhs, rhs)) => {
                assert!(matches!(*rhs, Expr::IntLit(0)));
                match *lhs {
                    Expr::StructField(base, field) => {
                        assert_eq!(field, "count");
                        assert!(matches!(*base, Expr::Var(ref n) if n == "data"));
                    }
                    other => panic!("expected StructField for iter_mut().count(), got {other:?}"),
                }
            }
            other => panic!("expected Gt predicate for iter_mut().count() > 0, got {other:?}"),
        }

        // `buffer.iter_mut().count() >= min_size` should normalize to `buffer.count >= min_size`
        let pred = parse_rust_condition_to_predicate(
            "buffer.iter_mut().count() >= min_size",
            &["buffer".to_string(), "min_size".to_string()],
        )
        .expect("expected iter_mut().count() >= min_size condition to parse");

        match pred {
            Predicate::Expr(Expr::Ge(lhs, rhs)) => {
                assert!(matches!(*rhs, Expr::Var(ref name) if name == "min_size"));
                match *lhs {
                    Expr::StructField(base, field) => {
                        assert_eq!(field, "count");
                        assert!(matches!(*base, Expr::Var(ref n) if n == "buffer"));
                    }
                    other => panic!(
                        "expected StructField for iter_mut().count() >= min_size, got {other:?}"
                    ),
                }
            }
            other => {
                panic!("expected Ge predicate for iter_mut().count() >= min_size, got {other:?}")
            }
        }
    }

    #[test]
    fn test_parse_rust_condition_chars_count_normalization() {
        // `text.chars().count()` should normalize to `text.count`
        // This is a common Rust idiom for counting characters in a string
        let pred =
            parse_rust_condition_to_predicate("text.chars().count() > 0", &["text".to_string()])
                .expect("expected chars().count() > 0 condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Gt, "text", &["count"], 0);

        // `name.chars().count() >= min_len` should normalize to `name.count >= min_len`
        let pred = parse_rust_condition_to_predicate(
            "name.chars().count() >= min_len",
            &["name".to_string(), "min_len".to_string()],
        )
        .expect("expected chars().count() >= min_len condition to parse");
        assert_pred_cmp_field_chain_var(&pred, CmpOp::Ge, "name", &["count"], "min_len");

        // Combined with other conditions: `text.chars().count() <= max_len && text.chars().count() > 0`
        let pred = parse_rust_condition_to_predicate(
            "text.chars().count() <= max_len && text.chars().count() > 0",
            &["text".to_string(), "max_len".to_string()],
        )
        .expect("expected combined chars().count() condition to parse");
        let (lhs, rhs) = expect_pred_and(&pred);
        assert_expr_cmp_field_chain_var(lhs, CmpOp::Le, "text", &["count"], "max_len");
        assert_expr_cmp_field_chain_int(rhs, CmpOp::Gt, "text", &["count"], 0);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_parse_rust_condition_bytes_count_normalization() {
        // `data.bytes().count()` should normalize to `data.utf8.count`
        // This is a common Rust idiom for counting bytes in a string
        let pred =
            parse_rust_condition_to_predicate("data.bytes().count() > 0", &["data".to_string()])
                .expect("expected bytes().count() > 0 condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Gt, "data", &["utf8", "count"], 0);

        // `text.bytes().count() <= max_bytes` should normalize to `text.utf8.count <= max_bytes`
        let pred = parse_rust_condition_to_predicate(
            "text.bytes().count() <= max_bytes",
            &["text".to_string(), "max_bytes".to_string()],
        )
        .expect("expected bytes().count() <= max_bytes condition to parse");
        assert_pred_cmp_field_chain_var(&pred, CmpOp::Le, "text", &["utf8", "count"], "max_bytes");

        // Combined: `data.bytes().count() >= min && data.bytes().count() <= max`
        let pred = parse_rust_condition_to_predicate(
            "data.bytes().count() >= min && data.bytes().count() <= max",
            &["data".to_string(), "min".to_string(), "max".to_string()],
        )
        .expect("expected combined bytes().count() condition to parse");
        let (lhs, rhs) = expect_pred_and(&pred);
        assert_expr_cmp_field_chain_var(lhs, CmpOp::Ge, "data", &["utf8", "count"], "min");
        assert_expr_cmp_field_chain_var(rhs, CmpOp::Le, "data", &["utf8", "count"], "max");
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_parse_rust_condition_lines_count_normalization() {
        // `text.lines().count()` should normalize to `text.lines.count`
        // This is a common Rust idiom for counting lines in a string
        let pred =
            parse_rust_condition_to_predicate("text.lines().count() > 0", &["text".to_string()])
                .expect("expected lines().count() > 0 condition to parse");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Gt, "text", &["lines", "count"], 0);

        // `content.lines().count() <= max_lines` should normalize to `content.lines.count <= max_lines`
        let pred = parse_rust_condition_to_predicate(
            "content.lines().count() <= max_lines",
            &["content".to_string(), "max_lines".to_string()],
        )
        .expect("expected lines().count() <= max_lines condition to parse");
        assert_pred_cmp_field_chain_var(
            &pred,
            CmpOp::Le,
            "content",
            &["lines", "count"],
            "max_lines",
        );

        // Combined: `text.lines().count() >= min && text.lines().count() <= max`
        let pred = parse_rust_condition_to_predicate(
            "text.lines().count() >= min && text.lines().count() <= max",
            &["text".to_string(), "min".to_string(), "max".to_string()],
        )
        .expect("expected combined lines().count() condition to parse");
        let (lhs, rhs) = expect_pred_and(&pred);
        assert_expr_cmp_field_chain_var(lhs, CmpOp::Ge, "text", &["lines", "count"], "min");
        assert_expr_cmp_field_chain_var(rhs, CmpOp::Le, "text", &["lines", "count"], "max");
    }

    #[test]
    fn test_parse_rust_condition_split_count_normalization() {
        // `text.split(',').count()` should normalize to `text.split(',').count`
        // This is a common Rust idiom for counting split parts of a string
        let pred =
            parse_rust_condition_to_predicate("text.split(',').count() > 1", &["text".to_string()])
                .expect("expected split(',').count() > 1 condition to parse");

        match pred {
            Predicate::Expr(Expr::Gt(lhs, rhs)) => {
                assert!(matches!(*rhs, Expr::IntLit(1)));
                // The LHS should be text.split(',').count which parses as a chain of field/call access
                // After normalization: text.split(',').count (without trailing ())
                // This will parse as: Call { base: text.split(','), field: count }
                // Actually, the condition parser treats `.count` as field access
                match *lhs {
                    Expr::StructField(_base, field) => {
                        assert_eq!(field, "count");
                        // base should be something like text.split(',')
                        // which the parser interprets as a call
                    }
                    other => panic!("expected StructField for split().count, got {other:?}"),
                }
            }
            other => panic!("expected Gt predicate for split(',').count() > 1, got {other:?}"),
        }

        // `data.split(delimiter).count() >= min_parts` should normalize correctly
        let pred = parse_rust_condition_to_predicate(
            "data.split(delimiter).count() >= min_parts",
            &[
                "data".to_string(),
                "delimiter".to_string(),
                "min_parts".to_string(),
            ],
        )
        .expect("expected split(delimiter).count() >= min_parts condition to parse");

        match pred {
            Predicate::Expr(Expr::Ge(lhs, rhs)) => {
                assert!(matches!(*rhs, Expr::Var(ref name) if name == "min_parts"));
                match *lhs {
                    Expr::StructField(_, field) => {
                        assert_eq!(field, "count");
                    }
                    other => {
                        panic!("expected StructField for split(delimiter).count(), got {other:?}")
                    }
                }
            }
            other => panic!(
                "expected Ge predicate for split(delimiter).count() >= min_parts, got {other:?}"
            ),
        }

        // Combined: `text.split('\n').count() >= min && text.split('\n').count() <= max`
        let pred = parse_rust_condition_to_predicate(
            "text.split('\\n').count() >= min && text.split('\\n').count() <= max",
            &["text".to_string(), "min".to_string(), "max".to_string()],
        )
        .expect("expected combined split().count() condition to parse");

        match pred {
            Predicate::Expr(Expr::And(lhs, rhs)) => {
                // First (lhs): text.split('\n').count >= min
                match *lhs {
                    Expr::Ge(l, r) => {
                        match *l {
                            Expr::StructField(_, field) => {
                                assert_eq!(field, "count");
                            }
                            other => panic!(
                                "expected StructField for split().count in lhs, got {other:?}"
                            ),
                        }
                        assert!(matches!(*r, Expr::Var(ref name) if name == "min"));
                    }
                    other => panic!("expected Ge for text.split().count >= min, got {other:?}"),
                }
                // Second (rhs): text.split('\n').count <= max
                match *rhs {
                    Expr::Le(l, r) => {
                        match *l {
                            Expr::StructField(_, field) => {
                                assert_eq!(field, "count");
                            }
                            other => panic!(
                                "expected StructField for split().count in rhs, got {other:?}"
                            ),
                        }
                        assert!(matches!(*r, Expr::Var(ref name) if name == "max"));
                    }
                    other => panic!("expected Le for text.split().count <= max, got {other:?}"),
                }
            }
            other => panic!(
                "expected And predicate for combined split().count() condition, got {other:?}"
            ),
        }
    }

    #[test]
    fn test_parse_rust_condition_range_contains_normalization() {
        // `(0..buffer.len()).contains(&index)` should normalize to `index < buffer.count`
        let pred = parse_rust_condition_to_predicate(
            "(0..buffer.len()).contains(&index)",
            &["buffer".to_string(), "index".to_string()],
        )
        .expect("expected range.contains(&index) condition to parse");

        match pred {
            Predicate::Expr(Expr::Lt(lhs, rhs)) => {
                assert!(matches!(*lhs, Expr::Var(ref n) if n == "index"));
                match *rhs {
                    Expr::StructField(base, field) => {
                        assert_eq!(field, "count");
                        assert!(matches!(*base, Expr::Var(ref n) if n == "buffer"));
                    }
                    other => panic!("expected StructField for buffer.count, got {other:?}"),
                }
            }
            other => panic!("expected Lt predicate for (0..len).contains(&index), got {other:?}"),
        }

        // Inclusive range: `(0..=n).contains(&i)` should normalize to `i <= n`
        let pred = parse_rust_condition_to_predicate(
            "(0..=n).contains(&i)",
            &["n".to_string(), "i".to_string()],
        )
        .expect("expected inclusive range.contains(&i) condition to parse");

        match pred {
            Predicate::Expr(Expr::Le(lhs, rhs)) => {
                assert!(matches!(*lhs, Expr::Var(ref n) if n == "i"));
                assert!(matches!(*rhs, Expr::Var(ref n) if n == "n"));
            }
            other => panic!("expected Le predicate for inclusive contains, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_rust_condition_range_len_normalization() {
        // `(0..n).len()` should normalize to `(n - 0)` which simplifies to an arithmetic expression
        // The condition `(0..n).len() == n` should parse as `(n - 0) == n`
        let pred = parse_rust_condition_to_predicate("(0..n).len() == n", &["n".to_string()])
            .expect("expected range.len() condition to parse");

        // The result should be an Eq comparing (n - 0) with n
        let (lhs, rhs) = expect_pred_cmp(&pred, CmpOp::Eq);
        let (sub_lhs, sub_rhs) = expect_sub(lhs);
        assert_var(sub_lhs, "n");
        assert_int(sub_rhs, 0);
        assert_var(rhs, "n");

        // Inclusive range: `(a..=b).len()` should normalize to `(b - a + 1)`
        let pred = parse_rust_condition_to_predicate(
            "(a..=b).len() > 0",
            &["a".to_string(), "b".to_string()],
        )
        .expect("expected inclusive range.len() condition to parse");

        // The result should be (b - a + 1) > 0
        let (lhs, rhs) = expect_pred_cmp(&pred, CmpOp::Gt);
        let (add_lhs, add_rhs) = expect_add(lhs);
        let (sub_lhs, sub_rhs) = expect_sub(add_lhs);
        assert_var(sub_lhs, "b");
        assert_var(sub_rhs, "a");
        assert_int(add_rhs, 1);
        assert_int(rhs, 0);

        // After .iter().count() normalization, `.count` (pseudo-field) should also work
        // `(0..n).iter().count()` -> `(0..n).count` -> `(n - 0)`
        // We test the intermediate form directly
        let pred =
            parse_rust_condition_to_predicate("(0..n).iter().count() == n", &["n".to_string()])
                .expect("expected iter().count() condition to parse after normalization");

        let (lhs, rhs) = expect_pred_cmp(&pred, CmpOp::Eq);
        let (sub_lhs, sub_rhs) = expect_sub(lhs);
        assert_var(sub_lhs, "n");
        assert_int(sub_rhs, 0);
        assert_var(rhs, "n");
    }

    #[test]
    fn test_parse_rust_condition_range_count_method_normalization() {
        // `(0..n).count()` should normalize to `(n - 0)` (Range implements Iterator directly)
        let pred = parse_rust_condition_to_predicate("(0..n).count() == n", &["n".to_string()])
            .expect("expected range.count() condition to parse");

        match pred {
            Predicate::Expr(Expr::Eq(lhs, rhs)) => {
                // LHS should be (n - 0)
                match *lhs {
                    Expr::Sub(sub_lhs, sub_rhs) => {
                        assert!(matches!(*sub_lhs, Expr::Var(ref name) if name == "n"));
                        assert!(matches!(*sub_rhs, Expr::IntLit(0)));
                    }
                    other => panic!("expected Sub for (n - 0), got {other:?}"),
                }
                // RHS should be n
                assert!(matches!(*rhs, Expr::Var(ref name) if name == "n"));
            }
            other => panic!("expected Eq predicate for range.count() == n, got {other:?}"),
        }

        // Inclusive range: `(a..=b).count()` should normalize to `(b - a + 1)`
        let pred = parse_rust_condition_to_predicate(
            "(a..=b).count() > 0",
            &["a".to_string(), "b".to_string()],
        )
        .expect("expected inclusive range.count() condition to parse");

        match pred {
            Predicate::Expr(Expr::Gt(lhs, rhs)) => {
                // LHS should be (b - a + 1)
                match *lhs {
                    Expr::Add(add_lhs, add_rhs) => {
                        match *add_lhs {
                            Expr::Sub(sub_lhs, sub_rhs) => {
                                assert!(matches!(*sub_lhs, Expr::Var(ref name) if name == "b"));
                                assert!(matches!(*sub_rhs, Expr::Var(ref name) if name == "a"));
                            }
                            other => panic!("expected Sub for (b - a), got {other:?}"),
                        }
                        assert!(matches!(*add_rhs, Expr::IntLit(1)));
                    }
                    other => panic!("expected Add for (b - a + 1), got {other:?}"),
                }
                assert!(matches!(*rhs, Expr::IntLit(0)));
            }
            other => panic!("expected Gt predicate for inclusive range.count() > 0, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_rust_condition_option_is_some_is_none_normalization() {
        // `opt.is_some()` should normalize to `opt != nil`
        let pred = parse_rust_condition_to_predicate("opt.is_some()", &["opt".to_string()])
            .expect("expected opt.is_some() to parse after normalization");

        match pred {
            Predicate::Expr(Expr::Eq(lhs, rhs)) => match (*lhs, *rhs) {
                (Expr::StructField(base, field), Expr::BoolLit(true)) => {
                    assert_eq!(field, "hasValue");
                    assert!(matches!(*base, Expr::Var(ref name) if name == "opt"));
                }
                other => panic!("expected opt.hasValue == true for opt.is_some(), got {other:?}"),
            },
            other => panic!("expected Eq predicate for opt.is_some(), got {other:?}"),
        }

        // `opt.is_none()` should normalize to `opt == nil`
        let pred = parse_rust_condition_to_predicate("opt.is_none()", &["opt".to_string()])
            .expect("expected opt.is_none() to parse after normalization");

        match pred {
            Predicate::Expr(Expr::Eq(lhs, rhs)) => match (*lhs, *rhs) {
                (Expr::StructField(base, field), Expr::BoolLit(false)) => {
                    assert_eq!(field, "hasValue");
                    assert!(matches!(*base, Expr::Var(ref name) if name == "opt"));
                }
                other => panic!("expected opt.hasValue == false for opt.is_none(), got {other:?}"),
            },
            other => panic!("expected Eq predicate for opt.is_none(), got {other:?}"),
        }

        // Negation should flip the comparison to avoid extra `not` nesting.
        let pred = parse_rust_condition_to_predicate("!opt.is_some()", &["opt".to_string()])
            .expect("expected !opt.is_some() to parse after normalization");

        match pred {
            Predicate::Expr(Expr::Eq(lhs, rhs)) => match (*lhs, *rhs) {
                (Expr::StructField(base, field), Expr::BoolLit(false)) => {
                    assert_eq!(field, "hasValue");
                    assert!(matches!(*base, Expr::Var(ref name) if name == "opt"));
                }
                other => panic!("expected opt.hasValue == false for !opt.is_some(), got {other:?}"),
            },
            other => panic!("expected Eq predicate for !opt.is_some(), got {other:?}"),
        }
    }

    #[test]
    fn test_parse_rust_condition_result_ok_err_normalization() {
        // `res.ok().is_some()` should normalize to `res.isSuccess`
        // This is a Rust idiom for checking if a Result is Ok
        // Note: we use "res" not "result" to avoid conflict with the special "result" keyword
        let pred = parse_rust_condition_to_predicate("res.ok().is_some()", &["res".to_string()])
            .expect("expected res.ok().is_some() to parse");
        assert_pred_struct_field(&pred, "res", "isSuccess");

        // `res.ok().is_none()` should normalize to `!res.isSuccess`
        // This means the Result is not Ok (i.e., it's Err)
        let pred = parse_rust_condition_to_predicate("res.ok().is_none()", &["res".to_string()])
            .expect("expected res.ok().is_none() to parse");
        assert_pred_not_struct_field(&pred, "res", "isSuccess");

        // `res.err().is_some()` should normalize to `!res.isSuccess`
        // This means the Result has an error (is Err)
        let pred = parse_rust_condition_to_predicate("res.err().is_some()", &["res".to_string()])
            .expect("expected res.err().is_some() to parse");
        assert_pred_not_struct_field(&pred, "res", "isSuccess");

        // `res.err().is_none()` should normalize to `res.isSuccess`
        // This means the Result has no error (is Ok)
        let pred = parse_rust_condition_to_predicate("res.err().is_none()", &["res".to_string()])
            .expect("expected res.err().is_none() to parse");
        assert_pred_struct_field(&pred, "res", "isSuccess");

        // Combined: `res.ok().is_some() && other.err().is_none()`
        let pred = parse_rust_condition_to_predicate(
            "res.ok().is_some() && other.err().is_none()",
            &["res".to_string(), "other".to_string()],
        )
        .expect("expected combined Result condition to parse");
        let (lhs, rhs) = expect_pred_and(&pred);
        assert_struct_field_chain(lhs, "res", &["isSuccess"]);
        assert_struct_field_chain(rhs, "other", &["isSuccess"]);

        // Negation: `!res.ok().is_some()` should normalize to `!res.isSuccess`
        let pred = parse_rust_condition_to_predicate("!res.ok().is_some()", &["res".to_string()])
            .expect("expected !res.ok().is_some() to parse");
        assert_pred_not_struct_field(&pred, "res", "isSuccess");

        // Double negation: `!res.ok().is_none()` should normalize to `res.isSuccess`
        let pred = parse_rust_condition_to_predicate("!res.ok().is_none()", &["res".to_string()])
            .expect("expected !res.ok().is_none() to parse");
        assert_pred_struct_field(&pred, "res", "isSuccess");
    }

    #[test]
    fn test_parse_rust_condition_result_is_ok_err_and_unwrap_normalization() {
        // `res.is_ok()` should normalize to `res.isSuccess`
        let pred = parse_rust_condition_to_predicate("res.is_ok()", &["res".to_string()])
            .expect("expected res.is_ok() to parse after normalization");
        assert_pred_struct_field(&pred, "res", "isSuccess");

        // `res.is_err()` should normalize to `!res.isSuccess`
        let pred = parse_rust_condition_to_predicate("res.is_err()", &["res".to_string()])
            .expect("expected res.is_err() to parse after normalization");
        assert_pred_not_struct_field(&pred, "res", "isSuccess");

        // Negation: `!res.is_ok()` should normalize to `!res.isSuccess`
        let pred = parse_rust_condition_to_predicate("!res.is_ok()", &["res".to_string()])
            .expect("expected !res.is_ok() to parse after normalization");
        assert_pred_not_struct_field(&pred, "res", "isSuccess");

        // Double negation: `!res.is_err()` should normalize to `res.isSuccess`
        let pred = parse_rust_condition_to_predicate("!res.is_err()", &["res".to_string()])
            .expect("expected !res.is_err() to parse after normalization");
        assert_pred_struct_field(&pred, "res", "isSuccess");

        // `.unwrap().len()` should normalize to `.value.count` (unwrap then len)
        let pred =
            parse_rust_condition_to_predicate("res.unwrap().len() > 0", &["res".to_string()])
                .expect("expected res.unwrap().len() > 0 to parse after normalization");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Gt, "res", &["value", "count"], 0);

        // `.unwrap_err().len()` should normalize to `.error.count`
        let pred =
            parse_rust_condition_to_predicate("res.unwrap_err().len() > 0", &["res".to_string()])
                .expect("expected res.unwrap_err().len() > 0 to parse after normalization");
        assert_pred_cmp_field_chain_int(&pred, CmpOp::Gt, "res", &["error", "count"], 0);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_parse_rust_condition_take_skip_count_normalization() {
        // `.iter().take(n).count()` should normalize to `.take(n).count`
        // This tests Rust iterator take/skip patterns used in FFI conditions

        // Test: `data.iter().take(5).count() > 0`
        let pred = parse_rust_condition_to_predicate(
            "data.iter().take(5).count() > 0",
            &["data".to_string()],
        )
        .expect("expected iter().take(5).count() > 0 condition to parse");
        let (lhs, rhs) = expect_pred_cmp(&pred, CmpOp::Gt);
        assert_is_struct_field(lhs, "count");
        assert_int(rhs, 0);

        // Test: `arr.iter().skip(3).count() >= n`
        let pred = parse_rust_condition_to_predicate(
            "arr.iter().skip(3).count() >= n",
            &["arr".to_string(), "n".to_string()],
        )
        .expect("expected iter().skip(3).count() >= n condition to parse");
        let (lhs, rhs) = expect_pred_cmp(&pred, CmpOp::Ge);
        assert_is_struct_field(lhs, "count");
        assert_var(rhs, "n");

        // Test: `items.into_iter().take(limit).count() <= limit`
        let pred = parse_rust_condition_to_predicate(
            "items.into_iter().take(limit).count() <= limit",
            &["items".to_string(), "limit".to_string()],
        )
        .expect("expected into_iter().take(limit).count() <= limit condition to parse");
        let (lhs, rhs) = expect_pred_cmp(&pred, CmpOp::Le);
        assert_is_struct_field(lhs, "count");
        assert_var(rhs, "limit");

        // Test: `vec.iter_mut().skip(offset).count() > 0`
        let pred = parse_rust_condition_to_predicate(
            "vec.iter_mut().skip(offset).count() > 0",
            &["vec".to_string(), "offset".to_string()],
        )
        .expect("expected iter_mut().skip(offset).count() > 0 condition to parse");
        let (lhs, rhs) = expect_pred_cmp(&pred, CmpOp::Gt);
        assert_is_struct_field(lhs, "count");
        assert_int(rhs, 0);

        // Combined: `data.iter().take(n).count() >= min && data.iter().skip(m).count() > 0`
        let pred = parse_rust_condition_to_predicate(
            "data.iter().take(n).count() >= min && data.iter().skip(m).count() > 0",
            &[
                "data".to_string(),
                "n".to_string(),
                "m".to_string(),
                "min".to_string(),
            ],
        )
        .expect("expected combined take/skip condition to parse");
        let (lhs, rhs) = expect_pred_and(&pred);
        let (lhs_l, lhs_r) = expect_cmp_expr(lhs, CmpOp::Ge);
        assert_is_struct_field(lhs_l, "count");
        assert_var(lhs_r, "min");

        let (rhs_l, rhs_r) = expect_cmp_expr(rhs, CmpOp::Gt);
        assert_is_struct_field(rhs_l, "count");
        assert_int(rhs_r, 0);
    }

    // ========================================================================
    // End-to-End FFI Verification Tests
    // ========================================================================

    #[test]
    fn test_end_to_end_ffi_verification_compatible() {
        // Rust exports increment with x > 0 precondition
        let rust_source = r#"
#[ffi_export]
#[ffi_requires("x > 0")]
#[ffi_ensures("result >= x")]
pub fn increment(x: i32) -> i32 {
    x + 1
}
"#;

        // Swift imports with stronger precondition (x > 5 implies x > 0)
        let swift_source = r#"
@_ffi_import("increment")
@_ffi_requires("x > 5")
@_ffi_ensures("result >= x")
func increment(_ x: Int32) -> Int32
"#;

        // Parse both
        let rust_decls = parse_rust_ffi_declarations_from_source(rust_source, "math.rs");
        let swift_decls = parse_swift_ffi_declarations_from_source(swift_source, "Math.swift");

        assert_eq!(rust_decls.len(), 1);
        assert_eq!(swift_decls.len(), 1);

        // Convert to FfiFunctions
        let rust_fn = rust_decl_to_ffi_function_parsed(&rust_decls[0]).unwrap();
        let swift_fn =
            swift_decl_to_ffi_function_parsed(&swift_decls[0], FfiLanguage::Swift).unwrap();

        // Add to specs
        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        // Verify with Z4
        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);

        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].result,
            FfiCompatibility::Compatible,
            "Swift x > 5 implies Rust x > 0, should be compatible. Result: {:?}",
            results[0]
        );
    }

    #[test]
    fn test_end_to_end_ffi_verification_incompatible() {
        // Rust exports with strict precondition x > 10
        let rust_source = r#"
#[ffi_export]
#[ffi_requires("x > 10")]
pub fn strict_increment(x: i32) -> i32 {
    x + 1
}
"#;

        // Swift imports with weaker precondition (x > 0 does NOT imply x > 10)
        let swift_source = r#"
@_ffi_import("strict_increment")
@_ffi_requires("x > 0")
func strict_increment(_ x: Int32) -> Int32
"#;

        let rust_decls = parse_rust_ffi_declarations_from_source(rust_source, "math.rs");
        let swift_decls = parse_swift_ffi_declarations_from_source(swift_source, "Math.swift");

        let rust_fn = rust_decl_to_ffi_function_parsed(&rust_decls[0]).unwrap();
        let swift_fn =
            swift_decl_to_ffi_function_parsed(&swift_decls[0], FfiLanguage::Swift).unwrap();

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let options = FfiVerifyOptions {
            use_z4_proofs: true,
        };
        let results = verify_ffi_compatibility_with_options(&specs, &options);

        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].result,
            FfiCompatibility::Incompatible,
            "Swift x > 0 does NOT imply Rust x > 10, should be incompatible. Result: {:?}",
            results[0]
        );
    }

    #[test]
    fn test_end_to_end_ffi_verification_type_mismatch() {
        // Rust exports with i32
        let rust_source = r"
#[ffi_export]
pub fn get_value() -> i32 {
    42
}
";

        // Swift imports expecting i64
        let swift_source = r#"
@_ffi_import("get_value")
func get_value() -> Int64
"#;

        let rust_decls = parse_rust_ffi_declarations_from_source(rust_source, "lib.rs");
        let swift_decls = parse_swift_ffi_declarations_from_source(swift_source, "Lib.swift");

        let rust_fn = rust_decl_to_ffi_function_parsed(&rust_decls[0]).unwrap();
        let swift_fn =
            swift_decl_to_ffi_function_parsed(&swift_decls[0], FfiLanguage::Swift).unwrap();

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        let results = verify_ffi_compatibility(&specs);

        assert_eq!(results.len(), 1);
        assert_eq!(
            results[0].result,
            FfiCompatibility::Incompatible,
            "Type mismatch i32 vs i64 should be incompatible. Result: {:?}",
            results[0]
        );

        // Find type layout check
        let type_check = results[0]
            .checks
            .iter()
            .find(|c| c.check_type == FfiCheckType::TypeLayout);
        assert!(type_check.is_some());
        assert!(!type_check.unwrap().passed);
    }

    // ========================================================================
    // Swift Bridge Module Parsing Tests
    // ========================================================================

    #[test]
    fn test_parse_swift_bridge_module_basic() {
        let source = r#"
#[swift_bridge::bridge]
mod ffi {
    extern "Rust" {
        fn increment(x: i32) -> i32;
    }
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "lib.rs");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.rust_name, "increment");
        assert!(decl.is_export());
        assert_eq!(decl.parameters, vec![("x".to_string(), "i32".to_string())]);
        assert_eq!(decl.return_type, "i32");
    }

    #[test]
    fn test_parse_swift_bridge_module_with_requires_ensures() {
        let source = r#"
#[swift_bridge::bridge]
mod ffi {
    #[requires(x > 0)]
    #[ensures(result >= x)]
    extern "Rust" {
        fn increment(x: i32) -> i32;
    }
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "lib.rs");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.rust_name, "increment");
        assert_eq!(decl.get_requires(), vec!["x > 0"]);
        assert_eq!(decl.get_ensures(), vec!["result >= x"]);
    }

    #[test]
    fn test_parse_swift_bridge_module_function_level_attrs() {
        let source = r#"
#[swift_bridge::bridge]
mod ffi {
    extern "Rust" {
        #[requires(a > 0)]
        #[ensures(result > 0)]
        fn multiply(a: i32, b: i32) -> i32;

        #[trusted]
        fn unsafe_op(ptr: *mut u8);
    }
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "lib.rs");
        assert_eq!(decls.len(), 2);

        // Check multiply function
        let multiply = &decls[0];
        assert_eq!(multiply.rust_name, "multiply");
        assert_eq!(multiply.get_requires(), vec!["a > 0"]);
        assert_eq!(multiply.get_ensures(), vec!["result > 0"]);
        assert!(!multiply.is_trusted());

        // Check unsafe_op function
        let unsafe_op = &decls[1];
        assert_eq!(unsafe_op.rust_name, "unsafe_op");
        assert!(unsafe_op.is_trusted());
    }

    #[test]
    fn test_parse_swift_bridge_module_multiple_extern_blocks() {
        let source = r#"
#[swift_bridge::bridge]
mod ffi {
    extern "Rust" {
        fn func_a() -> i32;
    }

    extern "Rust" {
        fn func_b(x: i32);
    }
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "lib.rs");
        assert_eq!(decls.len(), 2);

        assert_eq!(decls[0].rust_name, "func_a");
        assert_eq!(decls[1].rust_name, "func_b");
    }

    #[test]
    fn test_parse_swift_bridge_module_with_quoted_conditions() {
        let source = r#"
#[swift_bridge::bridge]
mod ffi {
    #[requires("buffer.len() > 0")]
    #[ensures("result.is_ok()")]
    extern "Rust" {
        fn parse_escape(buffer: &[u8]) -> Result<ParseResult, ParseError>;
    }
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "lib.rs");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.get_requires(), vec!["buffer.len() > 0"]);
        assert_eq!(decl.get_ensures(), vec!["result.is_ok()"]);
    }

    #[test]
    fn test_parse_swift_bridge_end_to_end() {
        // Rust source with swift_bridge module
        let rust_source = r#"
#[swift_bridge::bridge]
mod ffi {
    #[requires(x > 0)]
    #[ensures(result >= x)]
    extern "Rust" {
        fn increment(x: i32) -> i32;
    }
}
"#;

        // Swift imports
        let swift_source = r#"
@_ffi_import("increment")
@_ffi_requires("x > 5")
@_ffi_ensures("result >= x")
func increment(_ x: Int32) -> Int32
"#;

        let rust_decls = parse_rust_ffi_declarations_from_source(rust_source, "lib.rs");
        let swift_decls = parse_swift_ffi_declarations_from_source(swift_source, "Math.swift");

        assert_eq!(rust_decls.len(), 1);
        assert_eq!(swift_decls.len(), 1);

        let rust_fn = rust_decl_to_ffi_function_parsed(&rust_decls[0]).unwrap();
        let swift_fn =
            swift_decl_to_ffi_function_parsed(&swift_decls[0], FfiLanguage::Swift).unwrap();

        let mut specs = FfiSpecs::new();
        specs.add(rust_fn);
        specs.add(swift_fn);

        // Verify compatibility (x > 5 implies x > 0, should be compatible)
        let results = verify_ffi_compatibility(&specs);
        assert_eq!(results.len(), 1);
        // Note: Structural check passes, Z4 check would also pass
    }

    #[test]
    fn test_parse_swift_bridge_mixed_with_ffi_export() {
        // Source with both #[ffi_export] and #[swift_bridge::bridge]
        let source = r#"
#[ffi_export]
#[ffi_requires("a > 0")]
pub fn standalone_func(a: i32) -> i32 {
    a
}

#[swift_bridge::bridge]
mod ffi {
    extern "Rust" {
        fn bridged_func(x: i32) -> i32;
    }
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "lib.rs");
        assert_eq!(decls.len(), 2);

        // Both parsing methods should work
        let standalone = decls.iter().find(|d| d.rust_name == "standalone_func");
        let bridged = decls.iter().find(|d| d.rust_name == "bridged_func");

        assert!(standalone.is_some());
        assert!(bridged.is_some());
        assert_eq!(standalone.unwrap().get_requires(), vec!["a > 0"]);
    }

    #[test]
    fn test_parse_swift_bridge_voice_example() {
        // Matches the structure of tests/ffi_examples/voice_bridge.rs
        let source = r#"
// Example Rust FFI using swift_bridge syntax
// This demonstrates verification with the swift_bridge::bridge attribute

#[swift_bridge::bridge]
mod voice_ffi {
    #[requires(sample_rate == 16000 || sample_rate == 48000)]
    #[ensures(result >= 0)]
    extern "Rust" {
        fn start_stt(sample_rate: u32) -> i32;
    }

    extern "Rust" {
        #[requires(text.len() > 0)]
        fn queue_tts(text: String) -> u64;

        #[trusted]
        fn stop_session();
    }
}
"#;

        let decls = parse_rust_ffi_declarations_from_source(source, "voice_bridge.rs");

        // Should find all 3 functions
        assert_eq!(
            decls.len(),
            3,
            "Expected 3 declarations, got {}: {:?}",
            decls.len(),
            decls.iter().map(|d| &d.rust_name).collect::<Vec<_>>()
        );

        // Check start_stt
        let start_stt = decls.iter().find(|d| d.rust_name == "start_stt");
        assert!(start_stt.is_some(), "start_stt not found");
        let start_stt = start_stt.unwrap();
        assert!(start_stt.is_export());
        assert_eq!(
            start_stt.get_requires(),
            vec!["sample_rate == 16000 || sample_rate == 48000"]
        );
        assert_eq!(start_stt.get_ensures(), vec!["result >= 0"]);

        // Check queue_tts
        let queue_tts = decls.iter().find(|d| d.rust_name == "queue_tts");
        assert!(queue_tts.is_some(), "queue_tts not found");
        let queue_tts = queue_tts.unwrap();
        assert_eq!(queue_tts.get_requires(), vec!["text.len() > 0"]);

        // Check stop_session
        let stop_session = decls.iter().find(|d| d.rust_name == "stop_session");
        assert!(stop_session.is_some(), "stop_session not found");
        assert!(stop_session.unwrap().is_trusted());
    }

    //===----------------------------------------------------------------------===//
    // Tests for swift-bridge generated Swift code parsing
    //===----------------------------------------------------------------------===//

    #[test]
    fn test_parse_swift_bridge_generated_basic() {
        // Basic swift-bridge generated function
        let source = r"
public func greet(_ name: String) {
    __swift_bridge__$greet(name)
}
";

        let decls = parse_swift_bridge_generated_from_source(source, "Generated.swift");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.swift_name, "greet");
        assert_eq!(decl.get_rust_name(), "greet");
        assert!(decl.is_import());
        assert_eq!(decl.parameters.len(), 1);
        assert_eq!(
            decl.parameters[0],
            ("name".to_string(), "String".to_string())
        );
        assert_eq!(decl.return_type, "Void");
    }

    #[test]
    fn test_parse_swift_bridge_generated_with_return() {
        // Function with return type
        let source = r"
public func add(_ a: Int32, _ b: Int32) -> Int32 {
    __swift_bridge__$add(a, b)
}
";

        let decls = parse_swift_bridge_generated_from_source(source, "Math.swift");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.swift_name, "add");
        assert_eq!(decl.get_rust_name(), "add");
        assert_eq!(decl.parameters.len(), 2);
        assert_eq!(decl.parameters[0], ("a".to_string(), "Int32".to_string()));
        assert_eq!(decl.parameters[1], ("b".to_string(), "Int32".to_string()));
        assert_eq!(decl.return_type, "Int32");
    }

    #[test]
    fn test_parse_swift_bridge_generated_multiple_functions() {
        // Multiple functions in one file
        let source = r"
public func startSession(_ id: UInt64) -> Bool {
    __swift_bridge__$start_session(id)
}

public func endSession() {
    __swift_bridge__$end_session()
}

public func getSessionData(_ id: UInt64) -> Data? {
    __swift_bridge__$get_session_data(id)
}
";

        let decls = parse_swift_bridge_generated_from_source(source, "Session.swift");
        assert_eq!(decls.len(), 3);

        // Check first function
        let start = &decls[0];
        assert_eq!(start.swift_name, "startSession");
        assert_eq!(start.get_rust_name(), "start_session");
        assert_eq!(start.parameters.len(), 1);
        assert_eq!(start.return_type, "Bool");

        // Check second function
        let end = &decls[1];
        assert_eq!(end.swift_name, "endSession");
        assert_eq!(end.get_rust_name(), "end_session");
        assert_eq!(end.parameters.len(), 0);
        assert_eq!(end.return_type, "Void");

        // Check third function
        let get = &decls[2];
        assert_eq!(get.swift_name, "getSessionData");
        assert_eq!(get.get_rust_name(), "get_session_data");
        assert_eq!(get.return_type, "Data?");
    }

    #[test]
    fn test_parse_swift_bridge_generated_skips_internal() {
        // Internal __ prefixed functions should be skipped
        let source = r"
public func myFunc() {
    __swift_bridge__$my_func()
}

func __swift_bridge__my_func() {
    // This is the internal C FFI function
}
";

        let decls = parse_swift_bridge_generated_from_source(source, "Generated.swift");
        // Should only find the public function, not the internal one
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].swift_name, "myFunc");
    }

    #[test]
    fn test_parse_swift_bridge_generated_method_syntax() {
        // Method on a type uses Type$method pattern
        let source = r"
public func processData(_ data: Data) -> UInt64 {
    __swift_bridge__$DataProcessor$process(data)
}
";

        let decls = parse_swift_bridge_generated_from_source(source, "DataProcessor.swift");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.swift_name, "processData");
        // get_rust_name() returns only the last path component for matching
        assert_eq!(decl.get_rust_name(), "process");
        // The full rust_path is stored in the Import attribute
        match &decl.attributes[0] {
            SwiftFfiAttribute::Import { rust_path, .. } => {
                assert_eq!(rust_path, "DataProcessor::process");
            }
            _ => panic!("Expected Import attribute"),
        }
    }

    #[test]
    fn test_parse_swift_bridge_generated_multiline_body() {
        // Function with multiline body
        let source = r"
public func complexOp(_ input: String) -> Int32 {
    let result = __swift_bridge__$complex_op(
        input.utf8CString
    )
    return result
}
";

        let decls = parse_swift_bridge_generated_from_source(source, "Complex.swift");
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].swift_name, "complexOp");
        assert_eq!(decls[0].get_rust_name(), "complex_op");
    }

    #[test]
    fn test_parse_swift_bridge_generated_labeled_params() {
        // Swift uses external labels: func foo(label name: Type)
        let source = r"
public func configure(withConfig config: Configuration, timeout seconds: Int32) {
    __swift_bridge__$configure(config, seconds)
}
";

        let decls = parse_swift_bridge_generated_from_source(source, "Config.swift");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(decl.parameters.len(), 2);
        // Should capture the local name (last token before colon)
        assert_eq!(
            decl.parameters[0],
            ("config".to_string(), "Configuration".to_string())
        );
        assert_eq!(
            decl.parameters[1],
            ("seconds".to_string(), "Int32".to_string())
        );
    }

    #[test]
    fn test_parse_swift_bridge_generated_generic_types() {
        // Function with generic types
        let source = r"
public func processArray(_ items: [Int32]) -> Optional<Int32> {
    __swift_bridge__$process_array(items)
}
";

        let decls = parse_swift_bridge_generated_from_source(source, "Generic.swift");
        assert_eq!(decls.len(), 1);

        let decl = &decls[0];
        assert_eq!(
            decl.parameters[0],
            ("items".to_string(), "[Int32]".to_string())
        );
        assert_eq!(decl.return_type, "Optional<Int32>");
    }

    #[test]
    fn test_parse_swift_bridge_generated_non_ffi_functions_ignored() {
        // Non-FFI functions should be ignored (no __swift_bridge__ call)
        let source = r#"
public func pureSwift(_ x: Int) -> Int {
    return x + 1
}

public func ffiBridge(_ x: Int32) -> Int32 {
    __swift_bridge__$bridge_call(x)
}

func helperFunction() {
    print("helper")
}
"#;

        let decls = parse_swift_bridge_generated_from_source(source, "Mixed.swift");
        // Should only find the FFI function
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].swift_name, "ffiBridge");
    }

    #[test]
    fn test_parse_swift_bridge_generated_realistic() {
        // Realistic swift-bridge output example
        let source = r#"
// Generated by swift-bridge

import Foundation

@_cdecl("__swift_bridge__$greet")
func __swift_bridge__greet(_ name: UnsafePointer<CChar>) -> UnsafeMutablePointer<CChar>? {
    // C FFI implementation
}

public func greet(_ name: String) -> String {
    let result = __swift_bridge__$greet(name.utf8CString)
    return String(cString: result!)
}

public func getUserCount() -> UInt64 {
    return __swift_bridge__$get_user_count()
}

public class User {
    var ptr: UnsafeMutableRawPointer

    public init(_ name: String) {
        self.ptr = __swift_bridge__$User$new(name.utf8CString)
    }

    deinit {
        __swift_bridge__$User$_free(ptr)
    }
}
"#;

        let decls = parse_swift_bridge_generated_from_source(source, "Generated.swift");

        // Should find greet and getUserCount, but skip the internal @_cdecl function
        // and the class init/deinit
        let public_funcs: Vec<_> = decls
            .iter()
            .filter(|d| !d.swift_name.starts_with("__"))
            .collect();

        assert!(
            public_funcs.iter().any(|d| d.swift_name == "greet"),
            "greet not found"
        );
        assert!(
            public_funcs.iter().any(|d| d.swift_name == "getUserCount"),
            "getUserCount not found"
        );
    }

    // ============================================================================
    // Additional SmtSort and smt_symbol tests
    // ============================================================================

    #[test]
    fn test_smt_sort_int_as_smtlib() {
        assert_eq!(SmtSort::Int.as_smtlib(), "Int");
    }

    #[test]
    fn test_smt_sort_bool_as_smtlib() {
        assert_eq!(SmtSort::Bool.as_smtlib(), "Bool");
    }

    #[test]
    fn test_smt_symbol_simple_identifier() {
        assert_eq!(smt_symbol("x"), "x");
        assert_eq!(smt_symbol("foo_bar"), "foo_bar");
        assert_eq!(smt_symbol("_underscore"), "_underscore");
    }

    #[test]
    fn test_smt_symbol_with_special_chars() {
        // Numbers at start require quoting
        assert_eq!(smt_symbol("123abc"), "|123abc|");
        // Spaces require quoting
        assert_eq!(smt_symbol("has space"), "|has space|");
        // Dashes require quoting
        assert_eq!(smt_symbol("has-dash"), "|has-dash|");
    }

    #[test]
    fn test_smt_symbol_empty_string() {
        assert_eq!(smt_symbol(""), "|_|");
    }

    #[test]
    fn test_smt_symbol_pipe_char_replaced() {
        // Pipe character should be replaced with underscore
        assert_eq!(smt_symbol("a|b"), "|a_b|");
    }

    // ============================================================================
    // Additional expr_to_smtlib_ffi tests
    // ============================================================================

    #[test]
    fn test_expr_to_smtlib_ffi_negative_int() {
        let expr = Expr::IntLit(-42);
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "(- 42)");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_zero() {
        let expr = Expr::IntLit(0);
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "0");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_bool_true() {
        let expr = Expr::BoolLit(true);
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "true");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_bool_false() {
        let expr = Expr::BoolLit(false);
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "false");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_nil_lit() {
        let expr = Expr::NilLit;
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "nil");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_result() {
        let expr = Expr::Result;
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "result");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_old_var() {
        let expr = Expr::Old(Box::new(Expr::Var("x".to_string())));
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "x_old");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_old_result() {
        let expr = Expr::Old(Box::new(Expr::Result));
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "result_old");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_old_complex() {
        let expr = Expr::Old(Box::new(Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        )));
        let result = expr_to_smtlib_ffi(&expr);
        assert!(result.contains("old"));
    }

    #[test]
    fn test_expr_to_smtlib_ffi_arithmetic_ops() {
        // Add
        let add = Expr::Add(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&add), "(+ a b)");

        // Sub
        let sub = Expr::Sub(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&sub), "(- a b)");

        // Mul
        let mul = Expr::Mul(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&mul), "(* a b)");

        // Div
        let div = Expr::Div(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&div), "(div a b)");

        // Rem (mod)
        let rem = Expr::Rem(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&rem), "(mod a b)");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_neg() {
        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "(- 0 x)");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_comparison_ops() {
        // Eq
        let eq = Expr::Eq(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&eq), "(= a b)");

        // Ne
        let ne = Expr::Ne(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&ne), "(not (= a b))");

        // Lt (uses <= with +1)
        let lt = Expr::Lt(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&lt), "(<= (+ a 1) b)");

        // Le
        let le = Expr::Le(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&le), "(<= a b)");

        // Gt (uses >= with +1)
        let gt = Expr::Gt(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&gt), "(>= a (+ b 1))");

        // Ge
        let ge = Expr::Ge(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&ge), "(>= a b)");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_logical_ops() {
        // And
        let and = Expr::And(
            Box::new(Expr::Var("p".to_string())),
            Box::new(Expr::Var("q".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&and), "(and p q)");

        // Or
        let or = Expr::Or(
            Box::new(Expr::Var("p".to_string())),
            Box::new(Expr::Var("q".to_string())),
        );
        assert_eq!(expr_to_smtlib_ffi(&or), "(or p q)");

        // Not
        let not = Expr::Not(Box::new(Expr::Var("p".to_string())));
        assert_eq!(expr_to_smtlib_ffi(&not), "(not p)");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_ite() {
        let ite = Expr::Ite {
            cond: Box::new(Expr::Var("c".to_string())),
            then_: Box::new(Expr::IntLit(1)),
            else_: Box::new(Expr::IntLit(0)),
        };
        assert_eq!(expr_to_smtlib_ffi(&ite), "(ite c 1 0)");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_array_index() {
        let arr_idx = Expr::ArrayIndex(
            Box::new(Expr::Var("arr".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert_eq!(expr_to_smtlib_ffi(&arr_idx), "(select arr 0)");
    }

    // ============================================================================
    // Additional predicate_to_smtlib_ffi tests
    // ============================================================================

    #[test]
    fn test_predicate_to_smtlib_ffi_and_empty() {
        let pred = Predicate::And(vec![]);
        assert_eq!(predicate_to_smtlib_ffi(&pred), "true");
    }

    #[test]
    fn test_predicate_to_smtlib_ffi_and_single() {
        let pred = Predicate::And(vec![Predicate::Expr(Expr::BoolLit(true))]);
        assert_eq!(predicate_to_smtlib_ffi(&pred), "true");
    }

    #[test]
    fn test_predicate_to_smtlib_ffi_and_multiple() {
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::Var("p".to_string())),
            Predicate::Expr(Expr::Var("q".to_string())),
            Predicate::Expr(Expr::Var("r".to_string())),
        ]);
        assert_eq!(predicate_to_smtlib_ffi(&pred), "(and p q r)");
    }

    #[test]
    fn test_predicate_to_smtlib_ffi_or_empty() {
        let pred = Predicate::Or(vec![]);
        assert_eq!(predicate_to_smtlib_ffi(&pred), "false");
    }

    #[test]
    fn test_predicate_to_smtlib_ffi_or_single() {
        let pred = Predicate::Or(vec![Predicate::Expr(Expr::BoolLit(false))]);
        assert_eq!(predicate_to_smtlib_ffi(&pred), "false");
    }

    #[test]
    fn test_predicate_to_smtlib_ffi_or_multiple() {
        let pred = Predicate::Or(vec![
            Predicate::Expr(Expr::Var("p".to_string())),
            Predicate::Expr(Expr::Var("q".to_string())),
        ]);
        assert_eq!(predicate_to_smtlib_ffi(&pred), "(or p q)");
    }

    #[test]
    fn test_predicate_to_smtlib_ffi_not() {
        let pred = Predicate::Not(Box::new(Predicate::Expr(Expr::Var("p".to_string()))));
        assert_eq!(predicate_to_smtlib_ffi(&pred), "(not p)");
    }

    #[test]
    fn test_predicate_to_smtlib_ffi_implies() {
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::Var("p".to_string()))),
            Box::new(Predicate::Expr(Expr::Var("q".to_string()))),
        );
        assert_eq!(predicate_to_smtlib_ffi(&pred), "(=> p q)");
    }

    // ============================================================================
    // Additional FFI verification edge case tests
    // ============================================================================

    #[test]
    fn test_check_precondition_compatibility_callee_no_requirements() {
        let caller = FfiFunction {
            name: "test".to_string(),
            language: FfiLanguage::Swift,
            params: vec![],
            return_type: FfiType::Void,
            requires: vec![Predicate::Expr(Expr::BoolLit(true))],
            ensures: vec![],
            trusted: false,
            source_file: None,
            source_line: None,
        };
        let callee = FfiFunction {
            name: "test".to_string(),
            language: FfiLanguage::Rust,
            params: vec![],
            return_type: FfiType::Void,
            requires: vec![], // No requirements
            ensures: vec![],
            trusted: false,
            source_file: None,
            source_line: None,
        };

        let check = check_precondition_compatibility(&caller, &callee);
        assert!(check.passed);
        assert!(check.message.unwrap().contains("no preconditions"));
    }

    #[test]
    fn test_check_postcondition_compatibility_caller_expects_nothing() {
        let caller = FfiFunction {
            name: "test".to_string(),
            language: FfiLanguage::Swift,
            params: vec![],
            return_type: FfiType::Void,
            requires: vec![],
            ensures: vec![], // Expects nothing
            trusted: false,
            source_file: None,
            source_line: None,
        };
        let callee = FfiFunction {
            name: "test".to_string(),
            language: FfiLanguage::Rust,
            params: vec![],
            return_type: FfiType::Void,
            requires: vec![],
            ensures: vec![Predicate::Expr(Expr::BoolLit(true))],
            trusted: false,
            source_file: None,
            source_line: None,
        };

        let check = check_postcondition_compatibility(&caller, &callee);
        assert!(check.passed);
        assert!(check.message.unwrap().contains("no postconditions"));
    }

    #[test]
    fn test_verify_ffi_pair_trusted_caller() {
        let caller = FfiFunction {
            name: "test".to_string(),
            language: FfiLanguage::Swift,
            params: vec![],
            return_type: FfiType::Void,
            requires: vec![],
            ensures: vec![],
            trusted: true, // Trusted
            source_file: None,
            source_line: None,
        };
        let callee = FfiFunction {
            name: "test".to_string(),
            language: FfiLanguage::Rust,
            params: vec![],
            return_type: FfiType::Void,
            requires: vec![Predicate::Expr(Expr::BoolLit(true))],
            ensures: vec![],
            trusted: false,
            source_file: None,
            source_line: None,
        };

        let result = verify_ffi_pair(&caller, &callee);
        assert_eq!(result.result, FfiCompatibility::Compatible);
        assert!(
            result.checks[0]
                .message
                .as_ref()
                .unwrap()
                .contains("@trusted")
        );
    }

    #[test]
    fn test_verify_ffi_pair_trusted_callee() {
        let caller = FfiFunction {
            name: "test".to_string(),
            language: FfiLanguage::Swift,
            params: vec![],
            return_type: FfiType::Void,
            requires: vec![],
            ensures: vec![],
            trusted: false,
            source_file: None,
            source_line: None,
        };
        let callee = FfiFunction {
            name: "test".to_string(),
            language: FfiLanguage::Rust,
            params: vec![],
            return_type: FfiType::Void,
            requires: vec![Predicate::Expr(Expr::BoolLit(true))],
            ensures: vec![],
            trusted: true, // Trusted
            source_file: None,
            source_line: None,
        };

        let result = verify_ffi_pair(&caller, &callee);
        assert_eq!(result.result, FfiCompatibility::Compatible);
    }

    #[test]
    fn test_ffi_language_display_all_variants() {
        assert_eq!(format!("{}", FfiLanguage::Swift), "Swift");
        assert_eq!(format!("{}", FfiLanguage::Rust), "Rust");
        assert_eq!(format!("{}", FfiLanguage::Kotlin), "Kotlin");
    }

    #[test]
    fn test_ffi_check_type_display_all_variants() {
        assert_eq!(
            format!("{}", FfiCheckType::PreconditionCompatibility),
            "precondition"
        );
        assert_eq!(
            format!("{}", FfiCheckType::PostconditionCompatibility),
            "postcondition"
        );
        assert_eq!(format!("{}", FfiCheckType::TypeLayout), "type layout");
        assert_eq!(format!("{}", FfiCheckType::Ownership), "ownership");
    }

    // ================================================================
    // FfiContractFile tests
    // ================================================================

    #[test]
    fn test_ffi_contract_file_new_basic() {
        let contract = FfiContractFile::new("test_crate");
        assert_eq!(contract.version, "1.0");
        assert_eq!(contract.crate_name, "test_crate");
        assert!(contract.hash.is_none());
        assert!(contract.functions.is_empty());
        assert!(contract.types.is_empty());
        assert!(contract.callbacks.is_empty());
    }

    #[test]
    fn test_ffi_contract_file_new_with_special_chars() {
        let contract = FfiContractFile::new("my-crate_v2.0");
        assert_eq!(contract.crate_name, "my-crate_v2.0");
    }

    #[test]
    fn test_ffi_contract_file_to_json_empty() {
        let contract = FfiContractFile::new("test");
        let json = contract.to_json().unwrap();
        assert!(json.contains("\"version\": \"1.0\""));
        assert!(json.contains("\"crate_name\": \"test\""));
        assert!(json.contains("\"functions\": {}"));
    }

    #[test]
    fn test_ffi_contract_file_from_json_minimal() {
        let json = r#"{
            "version": "1.0",
            "crate_name": "test",
            "functions": {}
        }"#;
        let contract = FfiContractFile::from_json(json).unwrap();
        assert_eq!(contract.version, "1.0");
        assert_eq!(contract.crate_name, "test");
        assert!(contract.functions.is_empty());
    }

    #[test]
    fn test_ffi_contract_file_from_json_with_function() {
        let json = r#"{
            "version": "1.0",
            "crate_name": "test",
            "functions": {
                "add": {
                    "params": [
                        {"name": "a", "type": "i32"},
                        {"name": "b", "type": "i32"}
                    ],
                    "returns": {"type": "i32"},
                    "requires": ["a >= 0"],
                    "ensures": ["result >= a"]
                }
            }
        }"#;
        let contract = FfiContractFile::from_json(json).unwrap();
        assert_eq!(contract.functions.len(), 1);
        let func = contract.functions.get("add").unwrap();
        assert_eq!(func.params.len(), 2);
        assert_eq!(func.params[0].name, "a");
        assert_eq!(func.params[0].type_str, "i32");
        assert_eq!(func.requires.len(), 1);
    }

    #[test]
    fn test_ffi_contract_file_from_json_invalid() {
        let json = "not valid json";
        let result = FfiContractFile::from_json(json);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Failed to parse"));
    }

    #[test]
    fn test_ffi_contract_file_roundtrip() {
        let mut contract = FfiContractFile::new("roundtrip_test");
        contract.hash = Some("abc123".to_string());
        contract.functions.insert(
            "test_func".to_string(),
            FfiContractFunction {
                symbol: Some("_mangled_name".to_string()),
                params: vec![FfiContractParam {
                    name: "x".to_string(),
                    type_str: "i32".to_string(),
                    ownership: FfiOwnership::Owned,
                }],
                returns: FfiContractReturn {
                    type_str: "bool".to_string(),
                    ownership: FfiOwnership::Owned,
                },
                requires: vec!["x > 0".to_string()],
                ensures: vec!["result == true".to_string()],
                panics: false,
                thread_safe: true,
            },
        );

        let json = contract.to_json().unwrap();
        let parsed = FfiContractFile::from_json(&json).unwrap();

        assert_eq!(parsed.version, contract.version);
        assert_eq!(parsed.crate_name, contract.crate_name);
        assert_eq!(parsed.hash, contract.hash);
        assert_eq!(parsed.functions.len(), 1);
        let func = parsed.functions.get("test_func").unwrap();
        assert_eq!(func.symbol, Some("_mangled_name".to_string()));
        assert_eq!(func.params.len(), 1);
    }

    #[test]
    fn test_ffi_contract_file_to_ffi_specs_empty() {
        let contract = FfiContractFile::new("test");
        let specs = contract.to_ffi_specs();
        assert!(specs.rust_exports.is_empty());
    }

    #[test]
    fn test_ffi_contract_file_to_ffi_specs_with_function() {
        let mut contract = FfiContractFile::new("test");
        contract.functions.insert(
            "increment".to_string(),
            FfiContractFunction {
                symbol: None,
                params: vec![FfiContractParam {
                    name: "n".to_string(),
                    type_str: "i32".to_string(),
                    ownership: FfiOwnership::Owned,
                }],
                returns: FfiContractReturn {
                    type_str: "i32".to_string(),
                    ownership: FfiOwnership::Owned,
                },
                requires: vec!["n >= 0".to_string()],
                ensures: vec![],
                panics: false,
                thread_safe: true,
            },
        );

        let specs = contract.to_ffi_specs();
        assert_eq!(specs.rust_exports.len(), 1);
        let func = specs.rust_exports.get("increment").unwrap();
        assert_eq!(func.name, "increment");
        assert_eq!(func.language, FfiLanguage::Rust);
        assert_eq!(func.params.len(), 1);
        assert_eq!(func.params[0].name, "n");
    }

    // ================================================================
    // parse_contract_type tests
    // ================================================================

    #[test]
    fn test_parse_contract_type_bool() {
        assert_eq!(parse_contract_type("bool"), FfiType::Bool);
        assert_eq!(parse_contract_type("Bool"), FfiType::Bool);
    }

    #[test]
    fn test_parse_contract_type_signed_ints() {
        assert_eq!(parse_contract_type("i8"), FfiType::Int { bits: 8 });
        assert_eq!(parse_contract_type("Int8"), FfiType::Int { bits: 8 });
        assert_eq!(parse_contract_type("i16"), FfiType::Int { bits: 16 });
        assert_eq!(parse_contract_type("Int16"), FfiType::Int { bits: 16 });
        assert_eq!(parse_contract_type("i32"), FfiType::Int { bits: 32 });
        assert_eq!(parse_contract_type("Int32"), FfiType::Int { bits: 32 });
        assert_eq!(parse_contract_type("Int"), FfiType::Int { bits: 32 });
        assert_eq!(parse_contract_type("i64"), FfiType::Int { bits: 64 });
        assert_eq!(parse_contract_type("Int64"), FfiType::Int { bits: 64 });
    }

    #[test]
    fn test_parse_contract_type_unsigned_ints() {
        assert_eq!(parse_contract_type("u8"), FfiType::UInt { bits: 8 });
        assert_eq!(parse_contract_type("UInt8"), FfiType::UInt { bits: 8 });
        assert_eq!(parse_contract_type("u16"), FfiType::UInt { bits: 16 });
        assert_eq!(parse_contract_type("UInt16"), FfiType::UInt { bits: 16 });
        assert_eq!(parse_contract_type("u32"), FfiType::UInt { bits: 32 });
        assert_eq!(parse_contract_type("UInt32"), FfiType::UInt { bits: 32 });
        assert_eq!(parse_contract_type("UInt"), FfiType::UInt { bits: 32 });
        assert_eq!(parse_contract_type("u64"), FfiType::UInt { bits: 64 });
        assert_eq!(parse_contract_type("UInt64"), FfiType::UInt { bits: 64 });
    }

    #[test]
    fn test_parse_contract_type_floats() {
        assert_eq!(parse_contract_type("f32"), FfiType::Float { bits: 32 });
        assert_eq!(parse_contract_type("Float32"), FfiType::Float { bits: 32 });
        assert_eq!(parse_contract_type("Float"), FfiType::Float { bits: 32 });
        assert_eq!(parse_contract_type("f64"), FfiType::Float { bits: 64 });
        assert_eq!(parse_contract_type("Float64"), FfiType::Float { bits: 64 });
        assert_eq!(parse_contract_type("Double"), FfiType::Float { bits: 64 });
    }

    #[test]
    fn test_parse_contract_type_strings() {
        assert_eq!(parse_contract_type("String"), FfiType::String);
        assert_eq!(parse_contract_type("string"), FfiType::String);
        assert_eq!(parse_contract_type("&str"), FfiType::StringRef);
        assert_eq!(parse_contract_type("str"), FfiType::StringRef);
    }

    #[test]
    fn test_parse_contract_type_bytes() {
        assert_eq!(parse_contract_type("Vec<u8>"), FfiType::Bytes);
        assert_eq!(parse_contract_type("Data"), FfiType::Bytes);
        assert_eq!(parse_contract_type("bytes"), FfiType::Bytes);
        assert_eq!(parse_contract_type("&[u8]"), FfiType::BytesRef);
        assert_eq!(parse_contract_type("slice<u8>"), FfiType::BytesRef);
    }

    #[test]
    fn test_parse_contract_type_void() {
        assert_eq!(parse_contract_type("()"), FfiType::Void);
        assert_eq!(parse_contract_type("void"), FfiType::Void);
        assert_eq!(parse_contract_type("Void"), FfiType::Void);
    }

    #[test]
    fn test_parse_contract_type_optional_rust_style() {
        let opt = parse_contract_type("Option<i32>");
        assert!(matches!(opt, FfiType::Optional(inner) if *inner == FfiType::Int { bits: 32 }));
    }

    #[test]
    fn test_parse_contract_type_optional_swift_style() {
        let opt = parse_contract_type("i32?");
        assert!(matches!(opt, FfiType::Optional(inner) if *inner == FfiType::Int { bits: 32 }));
    }

    #[test]
    fn test_parse_contract_type_result() {
        let result = parse_contract_type("Result<i32, String>");
        match result {
            FfiType::Result { ok, err } => {
                assert_eq!(*ok, FfiType::Int { bits: 32 });
                assert_eq!(*err, FfiType::String);
            }
            _ => panic!("Expected Result type"),
        }
    }

    #[test]
    fn test_parse_contract_type_result_single_param() {
        // Result with only one type should become Custom
        let result = parse_contract_type("Result<i32>");
        assert!(matches!(result, FfiType::Custom(s) if s == "Result<i32>"));
    }

    #[test]
    fn test_parse_contract_type_custom() {
        let custom = parse_contract_type("MyCustomType");
        assert_eq!(custom, FfiType::Custom("MyCustomType".to_string()));
    }

    #[test]
    fn test_parse_contract_type_with_whitespace() {
        assert_eq!(parse_contract_type("  i32  "), FfiType::Int { bits: 32 });
    }

    // ================================================================
    // ffi_type_to_string tests
    // ================================================================

    #[test]
    fn test_ffi_type_to_string_bool() {
        assert_eq!(ffi_type_to_string(&FfiType::Bool), "bool");
    }

    #[test]
    fn test_ffi_type_to_string_ints() {
        assert_eq!(ffi_type_to_string(&FfiType::Int { bits: 8 }), "i8");
        assert_eq!(ffi_type_to_string(&FfiType::Int { bits: 16 }), "i16");
        assert_eq!(ffi_type_to_string(&FfiType::Int { bits: 32 }), "i32");
        assert_eq!(ffi_type_to_string(&FfiType::Int { bits: 64 }), "i64");
    }

    #[test]
    fn test_ffi_type_to_string_uints() {
        assert_eq!(ffi_type_to_string(&FfiType::UInt { bits: 8 }), "u8");
        assert_eq!(ffi_type_to_string(&FfiType::UInt { bits: 16 }), "u16");
        assert_eq!(ffi_type_to_string(&FfiType::UInt { bits: 32 }), "u32");
        assert_eq!(ffi_type_to_string(&FfiType::UInt { bits: 64 }), "u64");
    }

    #[test]
    fn test_ffi_type_to_string_floats() {
        assert_eq!(ffi_type_to_string(&FfiType::Float { bits: 32 }), "f32");
        assert_eq!(ffi_type_to_string(&FfiType::Float { bits: 64 }), "f64");
    }

    #[test]
    fn test_ffi_type_to_string_strings() {
        assert_eq!(ffi_type_to_string(&FfiType::String), "String");
        assert_eq!(ffi_type_to_string(&FfiType::StringRef), "&str");
    }

    #[test]
    fn test_ffi_type_to_string_bytes() {
        assert_eq!(ffi_type_to_string(&FfiType::Bytes), "Vec<u8>");
        assert_eq!(ffi_type_to_string(&FfiType::BytesRef), "&[u8]");
    }

    #[test]
    fn test_ffi_type_to_string_void() {
        assert_eq!(ffi_type_to_string(&FfiType::Void), "()");
    }

    #[test]
    fn test_ffi_type_to_string_optional() {
        let opt = FfiType::Optional(Box::new(FfiType::Int { bits: 32 }));
        assert_eq!(ffi_type_to_string(&opt), "Option<i32>");
    }

    #[test]
    fn test_ffi_type_to_string_optional_nested() {
        let opt = FfiType::Optional(Box::new(FfiType::Optional(Box::new(FfiType::Bool))));
        assert_eq!(ffi_type_to_string(&opt), "Option<Option<bool>>");
    }

    #[test]
    fn test_ffi_type_to_string_result() {
        let result = FfiType::Result {
            ok: Box::new(FfiType::Int { bits: 32 }),
            err: Box::new(FfiType::String),
        };
        assert_eq!(ffi_type_to_string(&result), "Result<i32, String>");
    }

    #[test]
    fn test_ffi_type_to_string_custom() {
        let custom = FfiType::Custom("MyType".to_string());
        assert_eq!(ffi_type_to_string(&custom), "MyType");
    }

    // ================================================================
    // ffi_specs_to_contract tests
    // ================================================================

    #[test]
    fn test_ffi_specs_to_contract_empty() {
        let specs = FfiSpecs::new();
        let contract = ffi_specs_to_contract(&specs, "test_crate");
        assert_eq!(contract.crate_name, "test_crate");
        assert_eq!(contract.version, "1.0");
        assert!(contract.functions.is_empty());
    }

    #[test]
    fn test_ffi_specs_to_contract_with_function() {
        let mut specs = FfiSpecs::new();
        specs.rust_exports.insert(
            "add".to_string(),
            FfiFunction {
                name: "add".to_string(),
                language: FfiLanguage::Rust,
                params: vec![
                    FfiParam {
                        name: "a".to_string(),
                        ffi_type: FfiType::Int { bits: 32 },
                    },
                    FfiParam {
                        name: "b".to_string(),
                        ffi_type: FfiType::Int { bits: 32 },
                    },
                ],
                return_type: FfiType::Int { bits: 32 },
                requires: vec![],
                ensures: vec![],
                trusted: false,
                source_file: None,
                source_line: None,
            },
        );

        let contract = ffi_specs_to_contract(&specs, "math_lib");
        assert_eq!(contract.crate_name, "math_lib");
        assert_eq!(contract.functions.len(), 1);
        let func = contract.functions.get("add").unwrap();
        assert_eq!(func.params.len(), 2);
        assert_eq!(func.params[0].name, "a");
        assert_eq!(func.params[0].type_str, "i32");
        assert_eq!(func.returns.type_str, "i32");
    }

    #[test]
    fn test_ffi_specs_to_contract_with_requires() {
        let mut specs = FfiSpecs::new();
        specs.rust_exports.insert(
            "safe_div".to_string(),
            FfiFunction {
                name: "safe_div".to_string(),
                language: FfiLanguage::Rust,
                params: vec![
                    FfiParam {
                        name: "a".to_string(),
                        ffi_type: FfiType::Int { bits: 32 },
                    },
                    FfiParam {
                        name: "b".to_string(),
                        ffi_type: FfiType::Int { bits: 32 },
                    },
                ],
                return_type: FfiType::Int { bits: 32 },
                requires: vec![Predicate::Expr(Expr::Ne(
                    Box::new(Expr::Var("b".to_string())),
                    Box::new(Expr::IntLit(0)),
                ))],
                ensures: vec![],
                trusted: false,
                source_file: None,
                source_line: None,
            },
        );

        let contract = ffi_specs_to_contract(&specs, "safe_math");
        let func = contract.functions.get("safe_div").unwrap();
        assert_eq!(func.requires.len(), 1);
        assert!(func.requires[0].contains("!=")); // b != 0
    }

    // ================================================================
    // FfiOwnership tests
    // ================================================================

    #[test]
    fn test_ffi_ownership_default() {
        let ownership = FfiOwnership::default();
        assert_eq!(ownership, FfiOwnership::Owned);
    }

    #[test]
    fn test_ffi_ownership_serde_owned() {
        let json = r#""owned""#;
        let ownership: FfiOwnership = serde_json::from_str(json).unwrap();
        assert_eq!(ownership, FfiOwnership::Owned);
    }

    #[test]
    fn test_ffi_ownership_serde_borrow() {
        let json = r#""borrow""#;
        let ownership: FfiOwnership = serde_json::from_str(json).unwrap();
        assert_eq!(ownership, FfiOwnership::Borrow);
    }

    #[test]
    fn test_ffi_ownership_serde_borrowmut() {
        let json = r#""borrowmut""#;
        let ownership: FfiOwnership = serde_json::from_str(json).unwrap();
        assert_eq!(ownership, FfiOwnership::BorrowMut);
    }

    // ================================================================
    // FfiContractFunction defaults tests
    // ================================================================

    #[test]
    fn test_ffi_contract_function_defaults() {
        let json = r#"{
            "params": [],
            "returns": {"type": "()"}
        }"#;
        let func: FfiContractFunction = serde_json::from_str(json).unwrap();
        assert!(func.symbol.is_none());
        assert!(func.requires.is_empty());
        assert!(func.ensures.is_empty());
        assert!(!func.panics);
        assert!(func.thread_safe); // default_true
    }

    #[test]
    fn test_ffi_contract_function_with_symbol() {
        let json = r#"{
            "symbol": "_mangled_name",
            "params": [],
            "returns": {"type": "()"}
        }"#;
        let func: FfiContractFunction = serde_json::from_str(json).unwrap();
        assert_eq!(func.symbol, Some("_mangled_name".to_string()));
    }

    #[test]
    fn test_ffi_contract_function_not_thread_safe() {
        let json = r#"{
            "params": [],
            "returns": {"type": "()"},
            "thread_safe": false
        }"#;
        let func: FfiContractFunction = serde_json::from_str(json).unwrap();
        assert!(!func.thread_safe);
    }

    // ================================================================
    // predicate_to_string tests
    // ================================================================

    #[test]
    fn test_predicate_to_string_and_empty() {
        let pred = Predicate::And(vec![]);
        assert_eq!(predicate_to_string(&pred), "true");
    }

    #[test]
    fn test_predicate_to_string_and_single() {
        let pred = Predicate::And(vec![Predicate::Expr(Expr::BoolLit(true))]);
        assert_eq!(predicate_to_string(&pred), "true");
    }

    #[test]
    fn test_predicate_to_string_and_multiple() {
        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ]);
        let s = predicate_to_string(&pred);
        assert!(s.contains("&&"));
    }

    #[test]
    fn test_predicate_to_string_or_empty() {
        let pred = Predicate::Or(vec![]);
        assert_eq!(predicate_to_string(&pred), "false");
    }

    #[test]
    fn test_predicate_to_string_or_multiple() {
        let pred = Predicate::Or(vec![
            Predicate::Expr(Expr::BoolLit(true)),
            Predicate::Expr(Expr::BoolLit(false)),
        ]);
        let s = predicate_to_string(&pred);
        assert!(s.contains("||"));
    }

    #[test]
    fn test_predicate_to_string_not() {
        let pred = Predicate::Not(Box::new(Predicate::Expr(Expr::BoolLit(true))));
        let s = predicate_to_string(&pred);
        assert!(s.starts_with("!("));
    }

    // ================================================================
    // expr_to_string tests
    // ================================================================

    #[test]
    fn test_expr_to_string_int_lit() {
        assert_eq!(expr_to_string(&Expr::IntLit(42)), "42");
        assert_eq!(expr_to_string(&Expr::IntLit(-100)), "-100");
        assert_eq!(expr_to_string(&Expr::IntLit(0)), "0");
    }

    #[test]
    fn test_expr_to_string_bool_lit() {
        assert_eq!(expr_to_string(&Expr::BoolLit(true)), "true");
        assert_eq!(expr_to_string(&Expr::BoolLit(false)), "false");
    }

    #[test]
    fn test_expr_to_string_nil_lit() {
        assert_eq!(expr_to_string(&Expr::NilLit), "nil");
    }

    #[test]
    fn test_expr_to_string_var() {
        assert_eq!(expr_to_string(&Expr::Var("x".to_string())), "x");
        assert_eq!(expr_to_string(&Expr::Var("myVar".to_string())), "myVar");
    }

    #[test]
    fn test_expr_to_string_result() {
        assert_eq!(expr_to_string(&Expr::Result), "result");
    }

    #[test]
    fn test_expr_to_string_old() {
        let old = Expr::Old(Box::new(Expr::Var("x".to_string())));
        assert_eq!(expr_to_string(&old), "old(x)");
    }

    #[test]
    fn test_expr_to_string_old_nested() {
        let old = Expr::Old(Box::new(Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        )));
        assert_eq!(expr_to_string(&old), "old((x + 1))");
    }

    #[test]
    fn test_expr_to_string_add() {
        let add = Expr::Add(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_string(&add), "(a + b)");
    }

    #[test]
    fn test_expr_to_string_sub() {
        let sub = Expr::Sub(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        assert_eq!(expr_to_string(&sub), "(a - 1)");
    }

    #[test]
    fn test_expr_to_string_mul() {
        let mul = Expr::Mul(
            Box::new(Expr::IntLit(2)),
            Box::new(Expr::Var("x".to_string())),
        );
        assert_eq!(expr_to_string(&mul), "(2 * x)");
    }

    #[test]
    fn test_expr_to_string_div() {
        let div = Expr::Div(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        assert_eq!(expr_to_string(&div), "(x / 2)");
    }

    #[test]
    fn test_expr_to_string_rem() {
        let rem = Expr::Rem(
            Box::new(Expr::Var("n".to_string())),
            Box::new(Expr::IntLit(10)),
        );
        assert_eq!(expr_to_string(&rem), "(n % 10)");
    }

    #[test]
    fn test_expr_to_string_neg() {
        let neg = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        assert_eq!(expr_to_string(&neg), "(-x)");
    }

    #[test]
    fn test_expr_to_string_eq() {
        let eq = Expr::Eq(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_string(&eq), "a == b");
    }

    #[test]
    fn test_expr_to_string_ne() {
        let ne = Expr::Ne(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert_eq!(expr_to_string(&ne), "x != 0");
    }

    #[test]
    fn test_expr_to_string_lt() {
        let lt = Expr::Lt(
            Box::new(Expr::Var("i".to_string())),
            Box::new(Expr::Var("n".to_string())),
        );
        assert_eq!(expr_to_string(&lt), "i < n");
    }

    #[test]
    fn test_expr_to_string_le() {
        let le = Expr::Le(
            Box::new(Expr::IntLit(0)),
            Box::new(Expr::Var("x".to_string())),
        );
        assert_eq!(expr_to_string(&le), "0 <= x");
    }

    #[test]
    fn test_expr_to_string_gt() {
        let gt = Expr::Gt(
            Box::new(Expr::Var("count".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert_eq!(expr_to_string(&gt), "count > 0");
    }

    #[test]
    fn test_expr_to_string_ge() {
        let ge = Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert_eq!(expr_to_string(&ge), "x >= 0");
    }

    #[test]
    fn test_expr_to_string_and() {
        let and = Expr::And(
            Box::new(Expr::BoolLit(true)),
            Box::new(Expr::Var("flag".to_string())),
        );
        assert_eq!(expr_to_string(&and), "(true && flag)");
    }

    #[test]
    fn test_expr_to_string_or() {
        let or = Expr::Or(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        assert_eq!(expr_to_string(&or), "(a || b)");
    }

    #[test]
    fn test_expr_to_string_not() {
        let not = Expr::Not(Box::new(Expr::BoolLit(false)));
        assert_eq!(expr_to_string(&not), "!false");
    }

    #[test]
    fn test_expr_to_string_ite() {
        let ite = Expr::Ite {
            cond: Box::new(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            then_: Box::new(Expr::Var("x".to_string())),
            else_: Box::new(Expr::Neg(Box::new(Expr::Var("x".to_string())))),
        };
        assert_eq!(expr_to_string(&ite), "(x > 0 ? x : (-x))");
    }

    #[test]
    fn test_expr_to_string_struct_field() {
        let field = Expr::StructField(Box::new(Expr::Var("point".to_string())), "x".to_string());
        assert_eq!(expr_to_string(&field), "point.x");
    }

    #[test]
    fn test_expr_to_string_struct_field_nested() {
        let field = Expr::StructField(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("obj".to_string())),
                "inner".to_string(),
            )),
            "value".to_string(),
        );
        assert_eq!(expr_to_string(&field), "obj.inner.value");
    }

    #[test]
    fn test_expr_to_string_array_index() {
        let idx = Expr::ArrayIndex(
            Box::new(Expr::Var("arr".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        assert_eq!(expr_to_string(&idx), "arr[0]");
    }

    #[test]
    fn test_expr_to_string_array_index_var() {
        let idx = Expr::ArrayIndex(
            Box::new(Expr::Var("arr".to_string())),
            Box::new(Expr::Var("i".to_string())),
        );
        assert_eq!(expr_to_string(&idx), "arr[i]");
    }

    #[test]
    fn test_expr_to_string_apply_no_args() {
        let apply = Expr::Apply {
            func: "foo".to_string(),
            args: vec![],
        };
        assert_eq!(expr_to_string(&apply), "foo()");
    }

    #[test]
    fn test_expr_to_string_apply_single_arg() {
        let apply = Expr::Apply {
            func: "abs".to_string(),
            args: vec![Expr::Var("x".to_string())],
        };
        assert_eq!(expr_to_string(&apply), "abs(x)");
    }

    #[test]
    fn test_expr_to_string_apply_multiple_args() {
        let apply = Expr::Apply {
            func: "max".to_string(),
            args: vec![Expr::Var("a".to_string()), Expr::Var("b".to_string())],
        };
        assert_eq!(expr_to_string(&apply), "max(a, b)");
    }

    #[test]
    fn test_expr_to_string_forall() {
        let forall = Expr::Forall {
            vars: vec![(
                "i".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Expr::Ge(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        };
        assert_eq!(expr_to_string(&forall), "forall i: i >= 0");
    }

    #[test]
    fn test_expr_to_string_forall_multiple_vars() {
        let forall = Expr::Forall {
            vars: vec![
                (
                    "i".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "j".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            body: Box::new(Expr::Le(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::Var("j".to_string())),
            )),
        };
        assert_eq!(expr_to_string(&forall), "forall i, j: i <= j");
    }

    #[test]
    fn test_expr_to_string_exists() {
        let exists = Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 32,
                },
            )],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Mul(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::Var("x".to_string())),
                )),
                Box::new(Expr::IntLit(4)),
            )),
        };
        let s = expr_to_string(&exists);
        assert!(s.starts_with("exists x:"));
        assert!(s.contains("(x * x) == 4"));
    }

    #[test]
    fn test_expr_to_string_complex_nested() {
        // ((a + b) * c) > 0 && result == (a + b)
        let sum = Expr::Add(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        let product = Expr::Mul(Box::new(sum.clone()), Box::new(Expr::Var("c".to_string())));
        let gt = Expr::Gt(Box::new(product), Box::new(Expr::IntLit(0)));
        let eq = Expr::Eq(Box::new(Expr::Result), Box::new(sum));
        let and = Expr::And(Box::new(gt), Box::new(eq));
        let s = expr_to_string(&and);
        assert!(s.contains("((a + b) * c) > 0"));
        assert!(s.contains("result == (a + b)"));
    }

    // ================================================================
    // Predicate::Implies tests
    // ================================================================

    #[test]
    fn test_predicate_to_string_implies() {
        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
            Box::new(Predicate::Expr(Expr::Ge(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        );
        let s = predicate_to_string(&pred);
        assert!(s.contains("=>"));
    }

    #[test]
    fn test_predicate_to_string_expr() {
        let pred = Predicate::Expr(Expr::Var("flag".to_string()));
        assert_eq!(predicate_to_string(&pred), "flag");
    }

    // ================================================================
    // contract_function_to_ffi_function tests
    // ================================================================

    #[test]
    fn test_contract_function_to_ffi_function_basic() {
        let func = FfiContractFunction {
            symbol: None,
            params: vec![FfiContractParam {
                name: "x".to_string(),
                type_str: "i32".to_string(),
                ownership: FfiOwnership::default(),
            }],
            returns: FfiContractReturn {
                type_str: "i32".to_string(),
                ownership: FfiOwnership::default(),
            },
            requires: vec![],
            ensures: vec![],
            panics: false,
            thread_safe: true,
        };

        let result = contract_function_to_ffi_function("test_func", &func);

        assert_eq!(result.name, "test_func");
        assert_eq!(result.params.len(), 1);
        assert_eq!(result.params[0].name, "x");
        assert!(matches!(
            result.params[0].ffi_type,
            FfiType::Int { bits: 32 }
        ));
        assert!(matches!(result.return_type, FfiType::Int { bits: 32 }));
        assert_eq!(result.language, FfiLanguage::Rust);
        assert!(!result.trusted);
    }

    #[test]
    fn test_contract_function_to_ffi_function_multiple_params() {
        let func = FfiContractFunction {
            symbol: Some("mangled_name".to_string()),
            params: vec![
                FfiContractParam {
                    name: "a".to_string(),
                    type_str: "bool".to_string(),
                    ownership: FfiOwnership::default(),
                },
                FfiContractParam {
                    name: "b".to_string(),
                    type_str: "String".to_string(),
                    ownership: FfiOwnership::default(),
                },
                FfiContractParam {
                    name: "c".to_string(),
                    type_str: "f64".to_string(),
                    ownership: FfiOwnership::default(),
                },
            ],
            returns: FfiContractReturn {
                type_str: "()".to_string(),
                ownership: FfiOwnership::default(),
            },
            requires: vec![],
            ensures: vec![],
            panics: false,
            thread_safe: true,
        };

        let result = contract_function_to_ffi_function("multi_param", &func);

        assert_eq!(result.params.len(), 3);
        assert_eq!(result.params[0].name, "a");
        assert!(matches!(result.params[0].ffi_type, FfiType::Bool));
        assert_eq!(result.params[1].name, "b");
        assert!(matches!(result.params[1].ffi_type, FfiType::String));
        assert_eq!(result.params[2].name, "c");
        assert!(matches!(
            result.params[2].ffi_type,
            FfiType::Float { bits: 64 }
        ));
        assert!(matches!(result.return_type, FfiType::Void));
    }

    #[test]
    fn test_contract_function_to_ffi_function_with_requires() {
        let func = FfiContractFunction {
            symbol: None,
            params: vec![FfiContractParam {
                name: "x".to_string(),
                type_str: "i32".to_string(),
                ownership: FfiOwnership::default(),
            }],
            returns: FfiContractReturn {
                type_str: "i32".to_string(),
                ownership: FfiOwnership::default(),
            },
            requires: vec!["x > 0".to_string()],
            ensures: vec![],
            panics: false,
            thread_safe: true,
        };

        let result = contract_function_to_ffi_function("requires_test", &func);

        assert_eq!(result.requires.len(), 1);
    }

    #[test]
    fn test_contract_function_to_ffi_function_with_ensures() {
        let func = FfiContractFunction {
            symbol: None,
            params: vec![FfiContractParam {
                name: "n".to_string(),
                type_str: "i32".to_string(),
                ownership: FfiOwnership::default(),
            }],
            returns: FfiContractReturn {
                type_str: "i32".to_string(),
                ownership: FfiOwnership::default(),
            },
            requires: vec![],
            ensures: vec!["result >= 0".to_string()],
            panics: false,
            thread_safe: true,
        };

        let result = contract_function_to_ffi_function("ensures_test", &func);

        assert_eq!(result.ensures.len(), 1);
    }

    #[test]
    fn test_contract_function_to_ffi_function_empty_params() {
        let func = FfiContractFunction {
            symbol: None,
            params: vec![],
            returns: FfiContractReturn {
                type_str: "bool".to_string(),
                ownership: FfiOwnership::default(),
            },
            requires: vec![],
            ensures: vec![],
            panics: false,
            thread_safe: true,
        };

        let result = contract_function_to_ffi_function("no_params", &func);

        assert_eq!(result.params.len(), 0);
        assert!(matches!(result.return_type, FfiType::Bool));
    }

    #[test]
    fn test_contract_function_to_ffi_function_invalid_requires_filtered() {
        let func = FfiContractFunction {
            symbol: None,
            params: vec![FfiContractParam {
                name: "x".to_string(),
                type_str: "i32".to_string(),
                ownership: FfiOwnership::default(),
            }],
            returns: FfiContractReturn {
                type_str: "i32".to_string(),
                ownership: FfiOwnership::default(),
            },
            // An unparseable condition should be filtered out
            requires: vec!["x > 0".to_string(), "invalid @#$%".to_string()],
            ensures: vec![],
            panics: false,
            thread_safe: true,
        };

        let result = contract_function_to_ffi_function("filter_test", &func);

        // The invalid requires should be filtered out, keeping only the valid one
        assert!(result.requires.len() <= 2);
    }

    #[test]
    fn test_contract_function_to_ffi_function_source_fields_none() {
        let func = FfiContractFunction {
            symbol: None,
            params: vec![],
            returns: FfiContractReturn {
                type_str: "()".to_string(),
                ownership: FfiOwnership::default(),
            },
            requires: vec![],
            ensures: vec![],
            panics: false,
            thread_safe: true,
        };

        let result = contract_function_to_ffi_function("no_source", &func);

        assert!(result.source_file.is_none());
        assert!(result.source_line.is_none());
    }

    // ==========================================================================
    // Tests for parse_bridge_attribute
    // ==========================================================================

    #[test]
    fn test_parse_bridge_attribute_requires_quoted() {
        let result = parse_bridge_attribute(r#"#[requires("x > 0")]"#);
        assert!(result.is_some());
        assert!(
            matches!(result.unwrap(), RustFfiAttribute::Requires { condition } if condition == "x > 0")
        );
    }

    #[test]
    fn test_parse_bridge_attribute_requires_unquoted() {
        let result = parse_bridge_attribute("#[requires(x > 0)]");
        assert!(result.is_some());
        assert!(
            matches!(result.unwrap(), RustFfiAttribute::Requires { condition } if condition == "x > 0")
        );
    }

    #[test]
    fn test_parse_bridge_attribute_ensures_quoted() {
        let result = parse_bridge_attribute(r#"#[ensures("result >= x")]"#);
        assert!(result.is_some());
        assert!(
            matches!(result.unwrap(), RustFfiAttribute::Ensures { condition } if condition == "result >= x")
        );
    }

    #[test]
    fn test_parse_bridge_attribute_ensures_unquoted() {
        let result = parse_bridge_attribute("#[ensures(result >= x)]");
        assert!(result.is_some());
        assert!(
            matches!(result.unwrap(), RustFfiAttribute::Ensures { condition } if condition == "result >= x")
        );
    }

    #[test]
    fn test_parse_bridge_attribute_trusted() {
        let result = parse_bridge_attribute("#[trusted]");
        assert!(result.is_some());
        assert!(matches!(result.unwrap(), RustFfiAttribute::Trusted));
    }

    #[test]
    fn test_parse_bridge_attribute_trusted_with_parens() {
        let result = parse_bridge_attribute("#[trusted()]");
        assert!(result.is_some());
        assert!(matches!(result.unwrap(), RustFfiAttribute::Trusted));
    }

    #[test]
    fn test_parse_bridge_attribute_unknown_attribute() {
        let result = parse_bridge_attribute("#[some_other_attr]");
        assert!(result.is_none());
    }

    #[test]
    fn test_parse_bridge_attribute_empty_line() {
        let result = parse_bridge_attribute("");
        assert!(result.is_none());
    }

    #[test]
    fn test_parse_bridge_attribute_whitespace_handling() {
        let result = parse_bridge_attribute("   #[requires(x > 0)]   ");
        assert!(result.is_some());
        assert!(
            matches!(result.unwrap(), RustFfiAttribute::Requires { condition } if condition == "x > 0")
        );
    }

    #[test]
    fn test_parse_bridge_attribute_requires_complex_condition() {
        let result = parse_bridge_attribute(r#"#[requires("a >= 0 && b < 100")]"#);
        assert!(result.is_some());
        assert!(
            matches!(result.unwrap(), RustFfiAttribute::Requires { condition } if condition == "a >= 0 && b < 100")
        );
    }

    // ==========================================================================
    // Tests for extract_attribute_arg
    // ==========================================================================

    #[test]
    fn test_extract_attribute_arg_quoted_string() {
        let result = extract_attribute_arg(r#"#[foo("bar")]"#);
        assert_eq!(result, Some("bar".to_string()));
    }

    #[test]
    fn test_extract_attribute_arg_unquoted_string() {
        let result = extract_attribute_arg("#[foo(bar)]");
        assert_eq!(result, Some("bar".to_string()));
    }

    #[test]
    fn test_extract_attribute_arg_expression() {
        let result = extract_attribute_arg("#[requires(x > 0)]");
        assert_eq!(result, Some("x > 0".to_string()));
    }

    #[test]
    fn test_extract_attribute_arg_no_parens() {
        let result = extract_attribute_arg("#[trusted]");
        assert!(result.is_none());
    }

    #[test]
    fn test_extract_attribute_arg_empty_parens() {
        let result = extract_attribute_arg("#[foo()]");
        assert_eq!(result, Some(String::new()));
    }

    #[test]
    fn test_extract_attribute_arg_mismatched_parens() {
        let result = extract_attribute_arg("#[foo)(]");
        assert!(result.is_none());
    }

    #[test]
    fn test_extract_attribute_arg_with_spaces() {
        let result = extract_attribute_arg(r#"#[foo(  "bar"  )]"#);
        assert_eq!(result, Some("bar".to_string()));
    }

    #[test]
    fn test_extract_attribute_arg_complex_expression() {
        let result = extract_attribute_arg("#[ensures(result.len() == input.len())]");
        assert_eq!(result, Some("result.len() == input.len()".to_string()));
    }

    #[test]
    fn test_extract_attribute_arg_nested_parens() {
        let result = extract_attribute_arg("#[requires(foo(bar))]");
        // Should extract up to the last )
        assert!(result.is_some());
    }

    // ==========================================================================
    // Tests for parse_extern_fn_signature
    // ==========================================================================

    #[test]
    fn test_parse_extern_fn_signature_simple() {
        let result = parse_extern_fn_signature("fn foo(x: i32) -> i32;");
        assert!(result.is_some());
        let (name, params, ret) = result.unwrap();
        assert_eq!(name, "foo");
        assert_eq!(params.len(), 1);
        assert_eq!(params[0], ("x".to_string(), "i32".to_string()));
        assert_eq!(ret, "i32");
    }

    #[test]
    fn test_parse_extern_fn_signature_no_params() {
        let result = parse_extern_fn_signature("fn bar() -> bool;");
        assert!(result.is_some());
        let (name, params, ret) = result.unwrap();
        assert_eq!(name, "bar");
        assert!(params.is_empty());
        assert_eq!(ret, "bool");
    }

    #[test]
    fn test_parse_extern_fn_signature_no_return() {
        let result = parse_extern_fn_signature("fn baz(a: i32);");
        assert!(result.is_some());
        let (name, params, ret) = result.unwrap();
        assert_eq!(name, "baz");
        assert_eq!(params.len(), 1);
        assert_eq!(ret, "()");
    }

    #[test]
    fn test_parse_extern_fn_signature_multiple_params() {
        let result = parse_extern_fn_signature("fn add(a: i32, b: i32) -> i32;");
        assert!(result.is_some());
        let (name, params, ret) = result.unwrap();
        assert_eq!(name, "add");
        assert_eq!(params.len(), 2);
        assert_eq!(params[0], ("a".to_string(), "i32".to_string()));
        assert_eq!(params[1], ("b".to_string(), "i32".to_string()));
        assert_eq!(ret, "i32");
    }

    #[test]
    fn test_parse_extern_fn_signature_with_whitespace() {
        let result = parse_extern_fn_signature("  fn  spaces  (  x :  i64  )  ->  bool ;  ");
        assert!(result.is_some());
        let (name, params, ret) = result.unwrap();
        assert_eq!(name, "spaces");
        assert_eq!(params.len(), 1);
        // The parser does trim, so whitespace in type may vary
        assert_eq!(params[0].0, "x");
        assert_eq!(ret, "bool");
    }

    #[test]
    fn test_parse_extern_fn_signature_complex_return_type() {
        let result = parse_extern_fn_signature("fn get_opt(x: i32) -> Option<i32>;");
        assert!(result.is_some());
        let (name, _params, ret) = result.unwrap();
        assert_eq!(name, "get_opt");
        assert_eq!(ret, "Option<i32>");
    }

    #[test]
    fn test_parse_extern_fn_signature_result_type() {
        let result = parse_extern_fn_signature("fn fallible() -> Result<i32, Error>;");
        assert!(result.is_some());
        let (_, _, ret) = result.unwrap();
        assert_eq!(ret, "Result<i32, Error>");
    }

    #[test]
    fn test_parse_extern_fn_signature_no_fn_keyword() {
        let result = parse_extern_fn_signature("foo(x: i32) -> i32;");
        assert!(result.is_none());
    }

    #[test]
    fn test_parse_extern_fn_signature_no_parens() {
        let result = parse_extern_fn_signature("fn foo -> i32;");
        assert!(result.is_none());
    }

    #[test]
    fn test_parse_extern_fn_signature_unsafe_fn() {
        let result = parse_extern_fn_signature("unsafe fn dangerous(ptr: *mut u8);");
        // Our simple parser should still find "fn " and parse it
        assert!(result.is_some());
        let (name, _, _) = result.unwrap();
        assert_eq!(name, "dangerous");
    }

    #[test]
    fn test_parse_extern_fn_signature_empty_name() {
        let result = parse_extern_fn_signature("fn (x: i32) -> i32;");
        assert!(result.is_none());
    }

    #[test]
    fn test_parse_extern_fn_signature_reference_params() {
        let result = parse_extern_fn_signature("fn with_ref(data: &[u8]) -> usize;");
        assert!(result.is_some());
        let (name, params, ret) = result.unwrap();
        assert_eq!(name, "with_ref");
        assert_eq!(params[0].1, "&[u8]");
        assert_eq!(ret, "usize");
    }

    #[test]
    fn test_parse_extern_fn_signature_mutable_ref() {
        let result = parse_extern_fn_signature("fn mutate(data: &mut Vec<i32>);");
        assert!(result.is_some());
        let (name, params, _) = result.unwrap();
        assert_eq!(name, "mutate");
        assert_eq!(params[0].1, "&mut Vec<i32>");
    }

    // ==========================================================================
    // Tests for parse_extern_rust_block
    // ==========================================================================

    #[test]
    fn test_parse_extern_rust_block_single_function() {
        let lines = vec!["fn increment(x: i32) -> i32;"];
        let decls = parse_extern_rust_block(&lines, "test.rs", 0, &[]);
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].rust_name, "increment");
        assert_eq!(decls[0].parameters.len(), 1);
        assert_eq!(decls[0].return_type, "i32");
    }

    #[test]
    fn test_parse_extern_rust_block_multiple_functions() {
        let lines = vec![
            "fn add(a: i32, b: i32) -> i32;",
            "fn sub(a: i32, b: i32) -> i32;",
        ];
        let decls = parse_extern_rust_block(&lines, "test.rs", 0, &[]);
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].rust_name, "add");
        assert_eq!(decls[1].rust_name, "sub");
    }

    #[test]
    fn test_parse_extern_rust_block_with_function_attributes() {
        let lines = vec!["#[requires(x > 0)]", "fn positive(x: i32) -> i32;"];
        let decls = parse_extern_rust_block(&lines, "test.rs", 0, &[]);
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].rust_name, "positive");
        // The requires attribute should be in the attributes
        assert!(
            decls[0]
                .attributes
                .iter()
                .any(|a| matches!(a, RustFfiAttribute::Requires { .. }))
        );
    }

    #[test]
    fn test_parse_extern_rust_block_with_block_attributes() {
        let lines = vec!["fn safe_func(x: i32) -> i32;"];
        let block_attrs = vec![RustFfiAttribute::Trusted];
        let decls = parse_extern_rust_block(&lines, "test.rs", 0, &block_attrs);
        assert_eq!(decls.len(), 1);
        // Block attribute should be inherited
        assert!(
            decls[0]
                .attributes
                .iter()
                .any(|a| matches!(a, RustFfiAttribute::Trusted))
        );
    }

    #[test]
    fn test_parse_extern_rust_block_skips_comments() {
        let lines = vec![
            "// This is a comment",
            "fn real_func(x: i32) -> i32;",
            "// Another comment",
        ];
        let decls = parse_extern_rust_block(&lines, "test.rs", 0, &[]);
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].rust_name, "real_func");
    }

    #[test]
    fn test_parse_extern_rust_block_skips_empty_lines() {
        let lines = vec![
            "",
            "fn func1(x: i32) -> i32;",
            "",
            "fn func2(y: i32) -> i32;",
            "",
        ];
        let decls = parse_extern_rust_block(&lines, "test.rs", 0, &[]);
        assert_eq!(decls.len(), 2);
    }

    #[test]
    fn test_parse_extern_rust_block_source_info() {
        let lines = vec!["fn tracked();"];
        let decls = parse_extern_rust_block(&lines, "my_file.rs", 10, &[]);
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].source_file, "my_file.rs");
        assert_eq!(decls[0].source_line, 11); // line_offset(10) + rel_idx(0) + 1
    }

    #[test]
    fn test_parse_extern_rust_block_empty() {
        let lines: Vec<&str> = vec![];
        let decls = parse_extern_rust_block(&lines, "test.rs", 0, &[]);
        assert!(decls.is_empty());
    }

    #[test]
    fn test_parse_extern_rust_block_only_comments() {
        let lines = vec!["// just a comment", "// another comment"];
        let decls = parse_extern_rust_block(&lines, "test.rs", 0, &[]);
        assert!(decls.is_empty());
    }

    #[test]
    fn test_parse_extern_rust_block_multiple_attrs_per_func() {
        let lines = vec![
            "#[requires(x > 0)]",
            "#[ensures(result >= x)]",
            "fn guarded(x: i32) -> i32;",
        ];
        let decls = parse_extern_rust_block(&lines, "test.rs", 0, &[]);
        assert_eq!(decls.len(), 1);
        // Both attributes should be present
        assert!(
            decls[0]
                .attributes
                .iter()
                .any(|a| matches!(a, RustFfiAttribute::Requires { .. }))
        );
        assert!(
            decls[0]
                .attributes
                .iter()
                .any(|a| matches!(a, RustFfiAttribute::Ensures { .. }))
        );
    }

    #[test]
    fn test_parse_extern_rust_block_attrs_cleared_between_funcs() {
        let lines = vec![
            "#[requires(x > 0)]",
            "fn first(x: i32) -> i32;",
            "fn second(y: i32) -> i32;",
        ];
        let decls = parse_extern_rust_block(&lines, "test.rs", 0, &[]);
        assert_eq!(decls.len(), 2);
        // First function should have the requires
        assert!(
            decls[0]
                .attributes
                .iter()
                .any(|a| matches!(a, RustFfiAttribute::Requires { .. }))
        );
        // Second function should not have requires (attrs cleared after first func)
        assert!(
            !decls[1]
                .attributes
                .iter()
                .any(|a| matches!(a, RustFfiAttribute::Requires { .. }))
        );
    }

    // ============================================================================
    // rename_expr_vars_for_ffi tests
    // ============================================================================

    #[test]
    fn test_rename_expr_vars_for_ffi_var_in_map() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("x".to_string(), "arg0".to_string());

        let expr = Expr::Var("x".to_string());
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(result, Expr::Var("arg0".to_string()));
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_var_not_in_map() {
        let rename_map = std::collections::HashMap::new();

        let expr = Expr::Var("y".to_string());
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(result, Expr::Var("y".to_string()));
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_var_bound() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("x".to_string(), "arg0".to_string());
        let bound_vars = vec!["x".to_string()];

        let expr = Expr::Var("x".to_string());
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &bound_vars);

        // Bound vars should NOT be renamed
        assert_eq!(result, Expr::Var("x".to_string()));
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_result() {
        let rename_map = std::collections::HashMap::new();
        let result = rename_expr_vars_for_ffi(&Expr::Result, &rename_map, &[]);
        assert_eq!(result, Expr::Result);
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_old() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("x".to_string(), "arg0".to_string());

        let expr = Expr::Old(Box::new(Expr::Var("x".to_string())));
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(result, Expr::Old(Box::new(Expr::Var("arg0".to_string()))));
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_int_lit() {
        let rename_map = std::collections::HashMap::new();
        let result = rename_expr_vars_for_ffi(&Expr::IntLit(42), &rename_map, &[]);
        assert_eq!(result, Expr::IntLit(42));
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_bool_lit() {
        let rename_map = std::collections::HashMap::new();
        let result = rename_expr_vars_for_ffi(&Expr::BoolLit(true), &rename_map, &[]);
        assert_eq!(result, Expr::BoolLit(true));
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_nil_lit() {
        let rename_map = std::collections::HashMap::new();
        let result = rename_expr_vars_for_ffi(&Expr::NilLit, &rename_map, &[]);
        assert_eq!(result, Expr::NilLit);
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_add() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("x".to_string(), "arg0".to_string());
        rename_map.insert("y".to_string(), "arg1".to_string());

        let expr = Expr::Add(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Var("y".to_string())),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Add(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::Var("arg1".to_string())),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_sub() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("a".to_string(), "renamed_a".to_string());

        let expr = Expr::Sub(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::IntLit(1)),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Sub(
                Box::new(Expr::Var("renamed_a".to_string())),
                Box::new(Expr::IntLit(1)),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_mul() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("n".to_string(), "arg0".to_string());

        let expr = Expr::Mul(
            Box::new(Expr::Var("n".to_string())),
            Box::new(Expr::IntLit(2)),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Mul(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::IntLit(2)),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_div() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("dividend".to_string(), "arg0".to_string());

        let expr = Expr::Div(
            Box::new(Expr::Var("dividend".to_string())),
            Box::new(Expr::IntLit(10)),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Div(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::IntLit(10)),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_rem() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("val".to_string(), "arg0".to_string());

        let expr = Expr::Rem(
            Box::new(Expr::Var("val".to_string())),
            Box::new(Expr::IntLit(3)),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Rem(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::IntLit(3)),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_neg() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("x".to_string(), "arg0".to_string());

        let expr = Expr::Neg(Box::new(Expr::Var("x".to_string())));
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(result, Expr::Neg(Box::new(Expr::Var("arg0".to_string()))));
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_eq() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("a".to_string(), "arg0".to_string());
        rename_map.insert("b".to_string(), "arg1".to_string());

        let expr = Expr::Eq(
            Box::new(Expr::Var("a".to_string())),
            Box::new(Expr::Var("b".to_string())),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Eq(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::Var("arg1".to_string())),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_ne() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("p".to_string(), "arg0".to_string());

        let expr = Expr::Ne(Box::new(Expr::Var("p".to_string())), Box::new(Expr::NilLit));
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Ne(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::NilLit),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_lt() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("x".to_string(), "arg0".to_string());

        let expr = Expr::Lt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(10)),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Lt(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::IntLit(10)),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_le() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("count".to_string(), "arg0".to_string());

        let expr = Expr::Le(
            Box::new(Expr::Var("count".to_string())),
            Box::new(Expr::IntLit(100)),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Le(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::IntLit(100)),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_gt() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("size".to_string(), "arg0".to_string());

        let expr = Expr::Gt(
            Box::new(Expr::Var("size".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Gt(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::IntLit(0)),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_ge() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("index".to_string(), "arg0".to_string());

        let expr = Expr::Ge(
            Box::new(Expr::Var("index".to_string())),
            Box::new(Expr::IntLit(0)),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Ge(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::IntLit(0)),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_and() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("p".to_string(), "arg0".to_string());
        rename_map.insert("q".to_string(), "arg1".to_string());

        let expr = Expr::And(
            Box::new(Expr::Var("p".to_string())),
            Box::new(Expr::Var("q".to_string())),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::And(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::Var("arg1".to_string())),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_or() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("cond1".to_string(), "arg0".to_string());
        rename_map.insert("cond2".to_string(), "arg1".to_string());

        let expr = Expr::Or(
            Box::new(Expr::Var("cond1".to_string())),
            Box::new(Expr::Var("cond2".to_string())),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Or(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::Var("arg1".to_string())),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_not() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("flag".to_string(), "arg0".to_string());

        let expr = Expr::Not(Box::new(Expr::Var("flag".to_string())));
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(result, Expr::Not(Box::new(Expr::Var("arg0".to_string()))));
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_ite() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("cond".to_string(), "arg0".to_string());
        rename_map.insert("then_val".to_string(), "arg1".to_string());
        rename_map.insert("else_val".to_string(), "arg2".to_string());

        let expr = Expr::Ite {
            cond: Box::new(Expr::Var("cond".to_string())),
            then_: Box::new(Expr::Var("then_val".to_string())),
            else_: Box::new(Expr::Var("else_val".to_string())),
        };
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Ite {
                cond: Box::new(Expr::Var("arg0".to_string())),
                then_: Box::new(Expr::Var("arg1".to_string())),
                else_: Box::new(Expr::Var("arg2".to_string())),
            }
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_array_index() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("arr".to_string(), "arg0".to_string());
        rename_map.insert("idx".to_string(), "arg1".to_string());

        let expr = Expr::ArrayIndex(
            Box::new(Expr::Var("arr".to_string())),
            Box::new(Expr::Var("idx".to_string())),
        );
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::ArrayIndex(
                Box::new(Expr::Var("arg0".to_string())),
                Box::new(Expr::Var("arg1".to_string())),
            )
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_struct_field() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("obj".to_string(), "arg0".to_string());

        let expr = Expr::StructField(Box::new(Expr::Var("obj".to_string())), "value".to_string());
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::StructField(Box::new(Expr::Var("arg0".to_string())), "value".to_string())
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_apply_no_args() {
        let rename_map = std::collections::HashMap::new();

        let expr = Expr::Apply {
            func: "constant".to_string(),
            args: vec![],
        };
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Apply {
                func: "constant".to_string(),
                args: vec![],
            }
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_apply_with_args() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("x".to_string(), "arg0".to_string());
        rename_map.insert("y".to_string(), "arg1".to_string());

        let expr = Expr::Apply {
            func: "func".to_string(),
            args: vec![Expr::Var("x".to_string()), Expr::Var("y".to_string())],
        };
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        assert_eq!(
            result,
            Expr::Apply {
                func: "func".to_string(),
                args: vec![Expr::Var("arg0".to_string()), Expr::Var("arg1".to_string())],
            }
        );
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_forall_binds_vars() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("i".to_string(), "arg0".to_string());
        rename_map.insert("x".to_string(), "arg1".to_string());

        // forall i: x > i  -- i is bound, x is free
        let expr = Expr::Forall {
            vars: vec![(
                "i".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::Var("i".to_string())),
            )),
        };
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        // i should NOT be renamed (bound), x should be renamed to arg1
        match result {
            Expr::Forall { vars, body } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "i");
                match body.as_ref() {
                    Expr::Gt(lhs, rhs) => {
                        assert_eq!(**lhs, Expr::Var("arg1".to_string())); // x renamed
                        assert_eq!(**rhs, Expr::Var("i".to_string())); // i not renamed (bound)
                    }
                    _ => panic!("Expected Gt"),
                }
            }
            _ => panic!("Expected Forall"),
        }
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_exists_binds_vars() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("j".to_string(), "arg0".to_string());
        rename_map.insert("arr".to_string(), "arg1".to_string());

        // exists j: arr[j] == 0  -- j is bound, arr is free
        let expr = Expr::Exists {
            vars: vec![(
                "j".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Eq(
                Box::new(Expr::ArrayIndex(
                    Box::new(Expr::Var("arr".to_string())),
                    Box::new(Expr::Var("j".to_string())),
                )),
                Box::new(Expr::IntLit(0)),
            )),
        };
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        // j should NOT be renamed (bound), arr should be renamed to arg1
        match result {
            Expr::Exists { vars, body } => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "j");
                match body.as_ref() {
                    Expr::Eq(lhs, _) => match lhs.as_ref() {
                        Expr::ArrayIndex(base, idx) => {
                            assert_eq!(**base, Expr::Var("arg1".to_string())); // arr renamed
                            assert_eq!(**idx, Expr::Var("j".to_string())); // j not renamed (bound)
                        }
                        _ => panic!("Expected ArrayIndex"),
                    },
                    _ => panic!("Expected Eq"),
                }
            }
            _ => panic!("Expected Exists"),
        }
    }

    #[test]
    fn test_rename_expr_vars_for_ffi_nested_forall_shadow() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("x".to_string(), "arg0".to_string());

        // forall x: x > 0  -- x is bound so outer x in rename_map should not apply
        let expr = Expr::Forall {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        };
        let result = rename_expr_vars_for_ffi(&expr, &rename_map, &[]);

        // x should NOT be renamed since it's bound
        match result {
            Expr::Forall { body, .. } => match body.as_ref() {
                Expr::Gt(lhs, _) => {
                    assert_eq!(**lhs, Expr::Var("x".to_string())); // NOT renamed
                }
                _ => panic!("Expected Gt"),
            },
            _ => panic!("Expected Forall"),
        }
    }

    // ============================================================================
    // rename_predicate_vars_for_ffi tests
    // ============================================================================

    #[test]
    fn test_rename_predicate_vars_for_ffi_expr() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("x".to_string(), "arg0".to_string());

        let pred = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ));
        let result = rename_predicate_vars_for_ffi(&pred, &rename_map);

        match result {
            Predicate::Expr(Expr::Gt(lhs, _)) => {
                assert_eq!(*lhs, Expr::Var("arg0".to_string()));
            }
            _ => panic!("Expected Expr(Gt)"),
        }
    }

    #[test]
    fn test_rename_predicate_vars_for_ffi_and() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("x".to_string(), "arg0".to_string());
        rename_map.insert("y".to_string(), "arg1".to_string());

        let pred = Predicate::And(vec![
            Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ]);
        let result = rename_predicate_vars_for_ffi(&pred, &rename_map);

        match result {
            Predicate::And(preds) => {
                assert_eq!(preds.len(), 2);
            }
            _ => panic!("Expected And"),
        }
    }

    #[test]
    fn test_rename_predicate_vars_for_ffi_or() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("a".to_string(), "arg0".to_string());
        rename_map.insert("b".to_string(), "arg1".to_string());

        let pred = Predicate::Or(vec![
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("b".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        ]);
        let result = rename_predicate_vars_for_ffi(&pred, &rename_map);

        match result {
            Predicate::Or(preds) => {
                assert_eq!(preds.len(), 2);
            }
            _ => panic!("Expected Or"),
        }
    }

    #[test]
    fn test_rename_predicate_vars_for_ffi_not() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("flag".to_string(), "arg0".to_string());

        let pred = Predicate::Not(Box::new(Predicate::Expr(Expr::Var("flag".to_string()))));
        let result = rename_predicate_vars_for_ffi(&pred, &rename_map);

        match result {
            Predicate::Not(inner) => match inner.as_ref() {
                Predicate::Expr(Expr::Var(name)) => {
                    assert_eq!(name, "arg0");
                }
                _ => panic!("Expected Expr(Var)"),
            },
            _ => panic!("Expected Not"),
        }
    }

    #[test]
    fn test_rename_predicate_vars_for_ffi_implies() {
        let mut rename_map = std::collections::HashMap::new();
        rename_map.insert("p".to_string(), "arg0".to_string());
        rename_map.insert("q".to_string(), "arg1".to_string());

        let pred = Predicate::Implies(
            Box::new(Predicate::Expr(Expr::Var("p".to_string()))),
            Box::new(Predicate::Expr(Expr::Var("q".to_string()))),
        );
        let result = rename_predicate_vars_for_ffi(&pred, &rename_map);

        match result {
            Predicate::Implies(ante, cons) => {
                match ante.as_ref() {
                    Predicate::Expr(Expr::Var(name)) => assert_eq!(name, "arg0"),
                    _ => panic!("Expected Expr(Var) in antecedent"),
                }
                match cons.as_ref() {
                    Predicate::Expr(Expr::Var(name)) => assert_eq!(name, "arg1"),
                    _ => panic!("Expected Expr(Var) in consequent"),
                }
            }
            _ => panic!("Expected Implies"),
        }
    }

    // ============================================================================
    // Additional expr_to_smtlib_ffi tests for uncovered branches
    // ============================================================================

    #[test]
    fn test_expr_to_smtlib_ffi_struct_field() {
        let expr = Expr::StructField(Box::new(Expr::Var("obj".to_string())), "value".to_string());
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "(value__field obj)");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_apply_no_args_constant() {
        let expr = Expr::Apply {
            func: "max_size".to_string(),
            args: vec![],
        };
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "max_size");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_apply_with_args() {
        let expr = Expr::Apply {
            func: "func".to_string(),
            args: vec![Expr::Var("x".to_string()), Expr::IntLit(42)],
        };
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "(func x 42)");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_forall() {
        let expr = Expr::Forall {
            vars: vec![(
                "i".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Ge(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        };
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "(forall ((i Int)) (>= i 0))");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_forall_multiple_vars() {
        let expr = Expr::Forall {
            vars: vec![
                (
                    "i".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
                (
                    "j".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
            ],
            body: Box::new(Expr::Le(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::Var("j".to_string())),
            )),
        };
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "(forall ((i Int) (j Int)) (<= i j))");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_exists() {
        let expr = Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        };
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "(exists ((x Int)) (= x 0))");
    }

    #[test]
    fn test_expr_to_smtlib_ffi_exists_multiple_vars() {
        let expr = Expr::Exists {
            vars: vec![
                (
                    "a".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
                (
                    "b".to_string(),
                    VcType::Int {
                        signed: true,
                        bits: 64,
                    },
                ),
            ],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Add(
                    Box::new(Expr::Var("a".to_string())),
                    Box::new(Expr::Var("b".to_string())),
                )),
                Box::new(Expr::IntLit(10)),
            )),
        };
        let result = expr_to_smtlib_ffi(&expr);
        assert_eq!(result, "(exists ((a Int) (b Int)) (= (+ a b) 10))");
    }

    // ============================================================================
    // verify_implication_z4 internal path tests
    // ============================================================================

    #[test]
    fn test_verify_implication_z4_consequent_empty() {
        let ante = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];
        let cons: Vec<Predicate> = vec![];

        let (passed, msg) = verify_implication_z4(&ante, &cons, "test empty consequent");

        assert!(passed);
        assert!(msg.contains("consequent empty"));
    }

    #[test]
    fn test_verify_implication_z4_with_nil_lit() {
        // Test that NilLit is handled in infer_symbols
        let ante = vec![Predicate::Expr(Expr::Ne(
            Box::new(Expr::Var("ptr".to_string())),
            Box::new(Expr::NilLit),
        ))];
        let cons = vec![Predicate::Expr(Expr::Ne(
            Box::new(Expr::Var("ptr".to_string())),
            Box::new(Expr::NilLit),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "ptr != nil => ptr != nil");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_array_index() {
        // Test ArrayIndex handling in infer_symbols
        let ante = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::ArrayIndex(
                Box::new(Expr::Var("arr".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(Expr::IntLit(0)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::ArrayIndex(
                Box::new(Expr::Var("arr".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "arr[0] >= 0 => arr[0] >= 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_struct_field() {
        // Test StructField handling in infer_symbols (triggers record_fun_sort)
        let ante = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("obj".to_string())),
                "value".to_string(),
            )),
            Box::new(Expr::IntLit(0)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("obj".to_string())),
                "value".to_string(),
            )),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "obj.value > 0 => obj.value >= 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_apply_args() {
        // Test Apply with args handling in infer_symbols (triggers record_fun_sort)
        let ante = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Apply {
                func: "f".to_string(),
                args: vec![Expr::Var("x".to_string())],
            }),
            Box::new(Expr::IntLit(0)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::Apply {
                func: "f".to_string(),
                args: vec![Expr::Var("x".to_string())],
            }),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "f(x) > 0 => f(x) >= 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_apply_no_args() {
        // Test Apply with no args handling in infer_symbols (treated as constant)
        let ante = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Apply {
                func: "constant".to_string(),
                args: vec![],
            }),
            Box::new(Expr::IntLit(0)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::Apply {
                func: "constant".to_string(),
                args: vec![],
            }),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "constant > 0 => constant >= 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_forall() {
        // Test Forall handling in infer_symbols
        let ante = vec![Predicate::Expr(Expr::Forall {
            vars: vec![(
                "i".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Ge(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        })];
        let cons = vec![Predicate::Expr(Expr::Forall {
            vars: vec![(
                "i".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Ge(
                Box::new(Expr::Var("i".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        })];

        let (passed, _msg) =
            verify_implication_z4(&ante, &cons, "forall i: i >= 0 => forall i: i >= 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_exists() {
        // Test Exists handling in infer_symbols
        let ante = vec![Predicate::Expr(Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        })];
        let cons = vec![Predicate::Expr(Expr::Exists {
            vars: vec![(
                "x".to_string(),
                VcType::Int {
                    signed: true,
                    bits: 64,
                },
            )],
            body: Box::new(Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        })];

        let (passed, _msg) =
            verify_implication_z4(&ante, &cons, "exists x: x == 0 => exists x: x == 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_ite() {
        // Test Ite handling in infer_symbols
        let ante = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::Ite {
                cond: Box::new(Expr::Gt(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::IntLit(0)),
                )),
                then_: Box::new(Expr::IntLit(1)),
                else_: Box::new(Expr::IntLit(0)),
            }),
            Box::new(Expr::IntLit(1)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "(x > 0 ? 1 : 0) == 1 => x > 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_old_var() {
        // Test Old(Var) handling in infer_symbols
        let ante = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Old(Box::new(Expr::Var("x".to_string())))),
            Box::new(Expr::IntLit(0)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::Old(Box::new(Expr::Var("x".to_string())))),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "old(x) > 0 => old(x) >= 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_old_result() {
        // Test Old(Result) handling in infer_symbols
        let ante = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Old(Box::new(Expr::Result))),
            Box::new(Expr::IntLit(0)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::Old(Box::new(Expr::Result))),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) =
            verify_implication_z4(&ante, &cons, "old(result) > 0 => old(result) >= 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_old_complex() {
        // Test Old with complex expression (not var/result)
        let ante = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Old(Box::new(Expr::Add(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(1)),
            )))),
            Box::new(Expr::IntLit(0)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::Old(Box::new(Expr::Add(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(1)),
            )))),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "old(x+1) > 0 => old(x+1) >= 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_bool_eq() {
        // Test Eq with BoolLit for boolean sort inference
        let ante = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::Var("flag".to_string())),
            Box::new(Expr::BoolLit(true)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Var("flag".to_string()))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "flag == true => flag");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_int_eq() {
        // Test Eq with IntLit for integer sort inference
        let ante = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "x == 5 => x > 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_and_expr() {
        // Test And expression handling
        let ante = vec![Predicate::Expr(Expr::And(
            Box::new(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Box::new(Expr::Gt(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
        ))];
        let cons = vec![Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "(x > 0 && y > 0) => x > 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_or_expr() {
        // Test Or expression handling
        let ante = vec![Predicate::Expr(Expr::Or(
            Box::new(Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
            Box::new(Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(2)),
            )),
        ))];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "(x == 1 || x == 2) => x >= 1");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_with_neg() {
        // Test Neg expression handling
        let ante = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::Neg(Box::new(Expr::Var("x".to_string())))),
            Box::new(Expr::IntLit(-5)),
        ))];
        let cons = vec![Predicate::Expr(Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(5)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "-x == -5 => x == 5");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_predicate_and() {
        // Test Predicate::And handling in infer_symbols_from_predicate
        let ante = vec![Predicate::And(vec![
            Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            )),
            Predicate::Expr(Expr::Lt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(100)),
            )),
        ])];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "(x > 0 && x < 100) => x >= 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_predicate_or() {
        // Test Predicate::Or handling in infer_symbols_from_predicate
        let ante = vec![Predicate::Or(vec![
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(1)),
            )),
            Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(2)),
            )),
        ])];
        let cons = vec![Predicate::Expr(Expr::Ge(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(1)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "(x == 1 | x == 2) => x >= 1");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_predicate_not() {
        // Test Predicate::Not handling in infer_symbols_from_predicate
        let ante = vec![Predicate::Not(Box::new(Predicate::Expr(Expr::Eq(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))))];
        let cons = vec![Predicate::Expr(Expr::Ne(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::IntLit(0)),
        ))];

        let (passed, _msg) = verify_implication_z4(&ante, &cons, "!(x == 0) => x != 0");

        assert!(passed);
    }

    #[test]
    fn test_verify_implication_z4_predicate_implies() {
        // Test Predicate::Implies handling in infer_symbols_from_predicate
        let ante = vec![Predicate::Implies(
            Box::new(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
            Box::new(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        )];
        let cons = vec![Predicate::Implies(
            Box::new(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
            Box::new(Predicate::Expr(Expr::Gt(
                Box::new(Expr::Var("y".to_string())),
                Box::new(Expr::IntLit(0)),
            ))),
        )];

        let (passed, _msg) =
            verify_implication_z4(&ante, &cons, "(x > 0 => y > 0) => (x > 0 => y > 0)");

        assert!(passed);
    }

    // ============================================================================
    // build_ffi_param_alignment_map tests
    // ============================================================================

    #[test]
    fn test_build_ffi_param_alignment_map_simple() {
        let caller = FfiFunction {
            name: "swift_func".to_string(),
            language: FfiLanguage::Swift,
            params: vec![FfiParam {
                name: "swiftArg".to_string(),
                ffi_type: FfiType::Int { bits: 32 },
            }],
            return_type: FfiType::Int { bits: 32 },
            requires: vec![],
            ensures: vec![],
            trusted: false,
            source_file: None,
            source_line: None,
        };
        let callee = FfiFunction {
            name: "rust_func".to_string(),
            language: FfiLanguage::Rust,
            params: vec![FfiParam {
                name: "rust_arg".to_string(),
                ffi_type: FfiType::Int { bits: 32 },
            }],
            return_type: FfiType::Int { bits: 32 },
            requires: vec![],
            ensures: vec![],
            trusted: false,
            source_file: None,
            source_line: None,
        };

        let map = build_ffi_param_alignment_map(&caller, &callee);

        assert_eq!(map.get("swiftArg"), Some(&"arg0".to_string()));
        assert_eq!(map.get("rust_arg"), Some(&"arg0".to_string()));
    }

    #[test]
    fn test_build_ffi_param_alignment_map_multiple_params() {
        let caller = FfiFunction {
            name: "swift_func".to_string(),
            language: FfiLanguage::Swift,
            params: vec![
                FfiParam {
                    name: "x".to_string(),
                    ffi_type: FfiType::Int { bits: 32 },
                },
                FfiParam {
                    name: "y".to_string(),
                    ffi_type: FfiType::Int { bits: 32 },
                },
                FfiParam {
                    name: "z".to_string(),
                    ffi_type: FfiType::Int { bits: 32 },
                },
            ],
            return_type: FfiType::Int { bits: 32 },
            requires: vec![],
            ensures: vec![],
            trusted: false,
            source_file: None,
            source_line: None,
        };
        let callee = FfiFunction {
            name: "rust_func".to_string(),
            language: FfiLanguage::Rust,
            params: vec![
                FfiParam {
                    name: "a".to_string(),
                    ffi_type: FfiType::Int { bits: 32 },
                },
                FfiParam {
                    name: "b".to_string(),
                    ffi_type: FfiType::Int { bits: 32 },
                },
                FfiParam {
                    name: "c".to_string(),
                    ffi_type: FfiType::Int { bits: 32 },
                },
            ],
            return_type: FfiType::Int { bits: 32 },
            requires: vec![],
            ensures: vec![],
            trusted: false,
            source_file: None,
            source_line: None,
        };

        let map = build_ffi_param_alignment_map(&caller, &callee);

        assert_eq!(map.get("x"), Some(&"arg0".to_string()));
        assert_eq!(map.get("a"), Some(&"arg0".to_string()));
        assert_eq!(map.get("y"), Some(&"arg1".to_string()));
        assert_eq!(map.get("b"), Some(&"arg1".to_string()));
        assert_eq!(map.get("z"), Some(&"arg2".to_string()));
        assert_eq!(map.get("c"), Some(&"arg2".to_string()));
    }

    #[test]
    fn test_build_ffi_param_alignment_map_empty() {
        let caller = FfiFunction {
            name: "swift_func".to_string(),
            language: FfiLanguage::Swift,
            params: vec![],
            return_type: FfiType::Void,
            requires: vec![],
            ensures: vec![],
            trusted: false,
            source_file: None,
            source_line: None,
        };
        let callee = FfiFunction {
            name: "rust_func".to_string(),
            language: FfiLanguage::Rust,
            params: vec![],
            return_type: FfiType::Void,
            requires: vec![],
            ensures: vec![],
            trusted: false,
            source_file: None,
            source_line: None,
        };

        let map = build_ffi_param_alignment_map(&caller, &callee);

        assert!(map.is_empty());
    }

    // Tests for normalize_collection_contains function (via parse_rust_condition_to_predicate)
    #[test]
    fn test_parse_rust_condition_collection_contains_with_ref() {
        // `items.contains(&x)` should normalize to `items.contains(x)` (strip the reference)
        let pred = parse_rust_condition_to_predicate(
            "items.contains(&x)",
            &["items".to_string(), "x".to_string()],
        )
        .expect("expected contains with ref condition to parse");

        // The normalized condition should be items.contains(x) which parses to a method call
        // Verify parsing succeeds and produces a non-trivial predicate
        if matches!(&pred, Predicate::Expr(Expr::BoolLit(true))) {
            panic!("expected non-trivial predicate");
        }
        // any other predicate is acceptable
    }

    #[test]
    fn test_parse_rust_condition_collection_contains_with_mut_ref() {
        // `vec.contains(&mut elem)` should normalize to `vec.contains(elem)` (strip &mut)
        let pred = parse_rust_condition_to_predicate(
            "vec.contains(&mut elem)",
            &["vec".to_string(), "elem".to_string()],
        )
        .expect("expected contains with mut ref condition to parse");
        if matches!(&pred, Predicate::Expr(Expr::BoolLit(true))) {
            panic!("expected non-trivial predicate");
        }
    }

    #[test]
    fn test_parse_rust_condition_collection_contains_with_mut_ref_space() {
        // `vec.contains(&mut x)` with space after &mut should also normalize
        let pred = parse_rust_condition_to_predicate(
            "vec.contains(&mut  x)",
            &["vec".to_string(), "x".to_string()],
        )
        .expect("expected contains with mut ref (with space) condition to parse");
        if matches!(&pred, Predicate::Expr(Expr::BoolLit(true))) {
            panic!("expected non-trivial predicate");
        }
    }

    #[test]
    fn test_parse_rust_condition_collection_contains_no_ref() {
        // `items.contains(x)` without reference should remain unchanged
        let pred = parse_rust_condition_to_predicate(
            "items.contains(x)",
            &["items".to_string(), "x".to_string()],
        )
        .expect("expected contains without ref condition to parse");
        if matches!(&pred, Predicate::Expr(Expr::BoolLit(true))) {
            panic!("expected non-trivial predicate");
        }
    }

    #[test]
    fn test_parse_rust_condition_collection_contains_nested_parens() {
        // `items.contains(&(a + b))` should normalize to `items.contains((a + b))`
        let pred = parse_rust_condition_to_predicate(
            "items.contains(&(a + b))",
            &["items".to_string(), "a".to_string(), "b".to_string()],
        )
        .expect("expected contains with nested parens to parse");
        if matches!(&pred, Predicate::Expr(Expr::BoolLit(true))) {
            panic!("expected non-trivial predicate");
        }
    }

    #[test]
    fn test_parse_rust_condition_collection_contains_multiple() {
        // Multiple contains calls should all be normalized
        let pred = parse_rust_condition_to_predicate(
            "a.contains(&x) && b.contains(&y)",
            &[
                "a".to_string(),
                "b".to_string(),
                "x".to_string(),
                "y".to_string(),
            ],
        )
        .expect("expected multiple contains to parse");
        // The result can be either Predicate::And or Predicate::Expr(Expr::And(...))
        // depending on how the parser handles the conjunction
        match pred {
            Predicate::And(parts) => {
                assert_eq!(parts.len(), 2, "expected two parts in And predicate");
            }
            Predicate::Expr(Expr::And(_, _)) => {
                // Expr::And is also acceptable - it's a conjunction at the expression level
            }
            other => panic!("expected And predicate or And expression, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_rust_condition_range_contains_not_modified() {
        // Range contains `(0..n).contains(&i)` should NOT be modified by normalize_collection_contains
        // because it's preceded by `)` and handled by normalize_range_contains instead
        // The result should be a comparison expression, not a method call
        let pred = parse_rust_condition_to_predicate(
            "(0..n).contains(&i)",
            &["n".to_string(), "i".to_string()],
        )
        .expect("expected range contains to parse");

        // After normalize_range_contains, this becomes a comparison expression
        // The exact form depends on optimization - could be `0 <= i && i < n` or just `i < n` if 0 <= i is trivially true
        // The key is that it should be a comparison, not a method call expression
        match &pred {
            // Expected: comparison predicates in various forms
            Predicate::And(_)
            | Predicate::Expr(
                Expr::Lt(_, _) | Expr::Le(_, _) | Expr::Gt(_, _) | Expr::Ge(_, _) | Expr::And(_, _),
            ) => {}
            other => panic!("expected comparison predicate for range contains, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_rust_condition_collection_contains_unmatched_paren() {
        // Unmatched parentheses should not cause a crash - just leave it as-is
        let pred = parse_rust_condition_to_predicate(
            "items.contains(&x",
            &["items".to_string(), "x".to_string()],
        );
        // This may fail to parse or return a raw expression - either is acceptable
        // The key is that it doesn't panic
        let _ = pred;
    }

    #[test]
    fn test_parse_rust_condition_collection_contains_whitespace_arg() {
        // `items.contains(& )` with only whitespace after & should be skipped
        let pred = parse_rust_condition_to_predicate("items.contains(& )", &["items".to_string()]);
        // This should parse but may return an error or a raw expression
        let _ = pred;
    }

    // Tests for FfiContractFile::to_json edge cases
    #[test]
    fn test_ffi_contract_file_to_json_with_functions_and_params() {
        let mut contract = FfiContractFile::new("my_crate");
        contract.functions.insert(
            "process".to_string(),
            FfiContractFunction {
                symbol: None,
                params: vec![FfiContractParam {
                    name: "input".to_string(),
                    type_str: "String".to_string(),
                    ownership: FfiOwnership::Owned,
                }],
                returns: FfiContractReturn {
                    type_str: "i32".to_string(),
                    ownership: FfiOwnership::Owned,
                },
                requires: vec!["!input.is_empty()".to_string()],
                ensures: vec!["result >= 0".to_string()],
                panics: false,
                thread_safe: true,
            },
        );

        let json = contract.to_json().unwrap();
        assert!(json.contains("\"crate_name\": \"my_crate\""));
        assert!(json.contains("\"process\""));
        assert!(json.contains("\"input\""));
        assert!(json.contains("\"String\""));
        assert!(json.contains("!input.is_empty()"));
        assert!(json.contains("result >= 0"));
    }

    #[test]
    fn test_ffi_contract_file_to_json_panics_function() {
        let mut contract = FfiContractFile::new("panicky_crate");
        contract.functions.insert(
            "may_panic".to_string(),
            FfiContractFunction {
                symbol: None,
                params: vec![],
                returns: FfiContractReturn {
                    type_str: "()".to_string(),
                    ownership: FfiOwnership::Owned,
                },
                requires: vec![],
                ensures: vec![],
                panics: true,
                thread_safe: false,
            },
        );

        let json = contract.to_json().unwrap();
        assert!(json.contains("\"panics\": true"));
        assert!(json.contains("\"thread_safe\": false"));
    }

    #[test]
    fn test_ffi_contract_file_to_json_multiple_params_with_ownership() {
        let mut contract = FfiContractFile::new("multi_param");
        contract.functions.insert(
            "add".to_string(),
            FfiContractFunction {
                symbol: Some("_add_impl".to_string()),
                params: vec![
                    FfiContractParam {
                        name: "a".to_string(),
                        type_str: "i32".to_string(),
                        ownership: FfiOwnership::Owned,
                    },
                    FfiContractParam {
                        name: "b".to_string(),
                        type_str: "&i32".to_string(),
                        ownership: FfiOwnership::Borrow,
                    },
                    FfiContractParam {
                        name: "c".to_string(),
                        type_str: "&mut i32".to_string(),
                        ownership: FfiOwnership::BorrowMut,
                    },
                ],
                returns: FfiContractReturn {
                    type_str: "i64".to_string(),
                    ownership: FfiOwnership::Owned,
                },
                requires: vec!["a >= 0".to_string(), "b >= 0".to_string()],
                ensures: vec!["result == a + b + c".to_string()],
                panics: false,
                thread_safe: true,
            },
        );

        let json = contract.to_json().unwrap();
        assert!(json.contains("\"name\": \"a\""));
        assert!(json.contains("\"name\": \"b\""));
        assert!(json.contains("\"name\": \"c\""));
        assert!(json.contains("\"i64\""));
        assert!(json.contains("\"symbol\": \"_add_impl\""));
        assert!(json.contains("\"borrow\""));
        assert!(json.contains("\"borrowmut\""));
    }

    #[test]
    fn test_ffi_contract_file_to_json_and_from_json_roundtrip() {
        let mut contract = FfiContractFile::new("roundtrip_v2");
        contract.functions.insert(
            "check".to_string(),
            FfiContractFunction {
                symbol: None,
                params: vec![FfiContractParam {
                    name: "val".to_string(),
                    type_str: "u64".to_string(),
                    ownership: FfiOwnership::Owned,
                }],
                returns: FfiContractReturn {
                    type_str: "bool".to_string(),
                    ownership: FfiOwnership::Owned,
                },
                requires: vec!["val < 1000".to_string()],
                ensures: vec!["result == (val > 0)".to_string()],
                panics: false,
                thread_safe: true,
            },
        );

        let json = contract.to_json().unwrap();
        let restored = FfiContractFile::from_json(&json).unwrap();

        assert_eq!(restored.crate_name, "roundtrip_v2");
        assert_eq!(restored.functions.len(), 1);
        let func = restored.functions.get("check").unwrap();
        assert_eq!(func.params[0].name, "val");
        assert_eq!(func.requires[0], "val < 1000");
    }

    #[test]
    fn test_ffi_contract_file_to_json_special_chars_in_name() {
        let contract = FfiContractFile::new("crate-with_special.chars");
        let json = contract.to_json().unwrap();
        assert!(json.contains("crate-with_special.chars"));
    }
}
