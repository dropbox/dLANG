//! TLA2 State Machine Model Types
//!
//! This module defines the portable state machine format that can be consumed
//! by TLA2 for temporal property verification.
//!
//! Design follows: docs/design/TLA2_STATEMACHINE_SPEC.md

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt::Write;

/// State machine for TLA2 model checking.
/// Produced by tRust's tla-extract component from MIR analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TLA2Model {
    /// Format version
    pub version: String,
    /// Unique name identifying this state machine
    pub name: String,
    /// State variables that comprise the machine's state
    pub variables: Vec<Variable>,
    /// Initial state predicate
    pub init: Predicate,
    /// Available transitions (actions)
    pub transitions: Vec<Transition>,
    /// Initial state index
    pub initial_state: StateId,
    /// Terminal state indices
    pub terminal_states: Vec<StateId>,
    /// Source mapping for diagnostics
    #[serde(skip_serializing_if = "SourceMap::is_empty")]
    pub source_map: SourceMap,
}

impl TLA2Model {
    /// Create a new empty model
    #[must_use]
    pub fn new(name: &str) -> Self {
        Self {
            version: crate::TLA2_EXPORT_VERSION.to_string(),
            name: name.to_string(),
            variables: Vec::new(),
            init: Predicate::Bool(true),
            transitions: Vec::new(),
            initial_state: StateId(0),
            terminal_states: Vec::new(),
            source_map: SourceMap::default(),
        }
    }

    /// Convert to JSON string
    #[must_use]
    pub fn to_json(&self) -> String {
        self.to_json_pretty(2)
    }

    /// Convert to JSON with configurable indentation
    #[must_use]
    pub fn to_json_pretty(&self, indent: usize) -> String {
        let ind = " ".repeat(indent);
        let mut json = String::new();

        json.push_str("{\n");
        let _ = writeln!(json, "{ind}\"version\": \"{}\",", self.version);
        let _ = writeln!(json, "{ind}\"name\": \"{}\",", escape_json(&self.name));

        // Variables
        let _ = writeln!(json, "{ind}\"variables\": [");
        for (i, var) in self.variables.iter().enumerate() {
            json.push_str(&var.to_json(indent + 2));
            if i < self.variables.len() - 1 {
                json.push(',');
            }
            json.push('\n');
        }
        let _ = writeln!(json, "{ind}],");

        // Init predicate
        let _ = writeln!(json, "{ind}\"init\": {},", self.init.to_json());

        // Transitions
        let _ = writeln!(json, "{ind}\"transitions\": [");
        for (i, trans) in self.transitions.iter().enumerate() {
            json.push_str(&trans.to_json(indent + 2));
            if i < self.transitions.len() - 1 {
                json.push(',');
            }
            json.push('\n');
        }
        let _ = writeln!(json, "{ind}],");

        // Initial state
        let _ = writeln!(json, "{ind}\"initial_state\": {},", self.initial_state.0);

        // Terminal states
        let _ = write!(json, "{ind}\"terminal_states\": [");
        for (i, state) in self.terminal_states.iter().enumerate() {
            if i > 0 {
                json.push_str(", ");
            }
            let _ = write!(json, "{}", state.0);
        }
        json.push_str("]\n");

        json.push_str("}\n");
        json
    }

    /// Write to file
    pub fn write_to_file(&self, path: &std::path::Path) -> std::io::Result<()> {
        use std::io::Write;
        let mut file = std::fs::File::create(path)?;
        file.write_all(self.to_json().as_bytes())?;
        Ok(())
    }
}

/// State identifier
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct StateId(pub usize);

/// Action identifier for source mapping
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, Serialize, Deserialize)]
pub struct ActionId(pub u64);

/// A state variable tracked by the state machine
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Variable {
    /// Variable name (corresponds to captured Rust variable)
    pub name: String,
    /// Variable type
    pub ty: VarType,
    /// Optional type invariant (always-true predicate)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub invariant: Option<Predicate>,
    /// Initial value expression
    #[serde(skip_serializing_if = "Option::is_none")]
    pub initial_value: Option<Expr>,
}

impl Variable {
    fn to_json(&self, indent: usize) -> String {
        let ind = " ".repeat(indent);
        let mut json = String::new();
        let _ = write!(json, "{ind}{{ ");
        let _ = write!(json, "\"name\": \"{}\", ", escape_json(&self.name));
        let _ = write!(json, "\"type\": {} }}", self.ty.to_json());
        json
    }
}

/// Variable types supported in state machines
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VarType {
    Bool,
    Int {
        bits: u8,
        signed: bool,
    },
    Enum {
        name: String,
        variants: Vec<String>,
    },
    Tuple(Vec<VarType>),
    Array {
        elem: Box<VarType>,
        len: usize,
    },
    Set(Box<VarType>),
    Map {
        key: Box<VarType>,
        value: Box<VarType>,
    },
    /// Opaque type (modeled as uninterpreted)
    Opaque(String),
}

impl VarType {
    fn to_json(&self) -> String {
        match self {
            Self::Bool => "\"bool\"".to_string(),
            Self::Int { bits, signed } => {
                format!("\"{}{}\"", if *signed { "i" } else { "u" }, bits)
            }
            Self::Enum { name, .. } => format!("\"enum:{}\"", escape_json(name)),
            Self::Tuple(elems) => {
                let types: Vec<String> = elems.iter().map(Self::to_json).collect();
                format!("{{ \"tuple\": [{}] }}", types.join(", "))
            }
            Self::Array { elem, len } => {
                format!("{{ \"array\": {}, \"len\": {} }}", elem.to_json(), len)
            }
            Self::Set(elem) => {
                format!("{{ \"set\": {} }}", elem.to_json())
            }
            Self::Map { key, value } => {
                format!(
                    "{{ \"map_key\": {}, \"map_value\": {} }}",
                    key.to_json(),
                    value.to_json()
                )
            }
            Self::Opaque(name) => format!("\"opaque:{}\"", escape_json(name)),
        }
    }
}

/// A transition (action) in the state machine
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transition {
    /// Unique identifier for source mapping
    pub action_id: ActionId,
    /// Human-readable name
    pub name: String,
    /// Source state (None = enabled from any state)
    pub from: Option<StateId>,
    /// Target state (None = stays in same state)
    pub to: Option<StateId>,
    /// Guard condition (when is this transition enabled)
    pub guard: Predicate,
    /// State variable assignments
    pub assignments: Vec<Assignment>,
    /// Is this a yield/await point transition?
    pub is_yield: bool,
    /// Is this a poll/resume transition?
    pub is_poll: bool,
}

impl Transition {
    fn to_json(&self, indent: usize) -> String {
        let ind = " ".repeat(indent);
        let mut json = String::new();
        let _ = write!(json, "{ind}{{");
        let _ = write!(json, "\n{ind}  \"action_id\": {},", self.action_id.0);
        let _ = write!(json, "\n{ind}  \"name\": \"{}\",", escape_json(&self.name));

        if let Some(from) = &self.from {
            let _ = write!(json, "\n{ind}  \"from\": {},", from.0);
        }
        if let Some(to) = &self.to {
            let _ = write!(json, "\n{ind}  \"to\": {},", to.0);
        }

        let _ = write!(json, "\n{ind}  \"guard\": {},", self.guard.to_json());

        let _ = write!(json, "\n{ind}  \"assignments\": [");
        for (i, assign) in self.assignments.iter().enumerate() {
            if i > 0 {
                json.push_str(", ");
            }
            json.push_str(&assign.to_json());
        }
        json.push_str("],");

        let _ = write!(json, "\n{ind}  \"is_yield\": {},", self.is_yield);
        let _ = write!(json, "\n{ind}  \"is_poll\": {}", self.is_poll);
        let _ = write!(json, "\n{ind}}}");
        json
    }
}

/// An assignment to a state variable
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Assignment {
    /// Variable being assigned
    pub variable: String,
    /// New value expression
    pub value: Expr,
}

impl Assignment {
    fn to_json(&self) -> String {
        format!(
            "{{ \"variable\": \"{}\", \"value\": {} }}",
            escape_json(&self.variable),
            self.value.to_json()
        )
    }
}

/// A boolean predicate over state variables
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Predicate {
    /// Boolean literal
    Bool(bool),
    /// State variable reference
    Var(String),
    /// Comparison
    Compare {
        left: Box<Expr>,
        op: CompareOp,
        right: Box<Expr>,
    },
    /// Logical not
    Not(Box<Predicate>),
    /// Logical and
    And(Vec<Predicate>),
    /// Logical or
    Or(Vec<Predicate>),
    /// Implication
    Implies(Box<Predicate>, Box<Predicate>),
    /// Set membership
    In { elem: Box<Expr>, set: Box<Expr> },
    /// Universal quantifier
    ForAll {
        var: String,
        domain: Box<Expr>,
        body: Box<Predicate>,
    },
    /// Existential quantifier
    Exists {
        var: String,
        domain: Box<Expr>,
        body: Box<Predicate>,
    },
}

impl Predicate {
    fn to_json(&self) -> String {
        match self {
            Self::Bool(b) => format!("{{ \"bool\": {b} }}"),
            Self::Var(v) => format!("{{ \"var\": \"{}\" }}", escape_json(v)),
            Self::Compare { left, op, right } => {
                format!(
                    "{{ \"compare\": {{ \"left\": {}, \"op\": \"{:?}\", \"right\": {} }} }}",
                    left.to_json(),
                    op,
                    right.to_json()
                )
            }
            Self::Not(p) => format!("{{ \"not\": {} }}", p.to_json()),
            Self::And(preds) => {
                let parts: Vec<String> = preds.iter().map(Self::to_json).collect();
                format!("{{ \"and\": [{}] }}", parts.join(", "))
            }
            Self::Or(preds) => {
                let parts: Vec<String> = preds.iter().map(Self::to_json).collect();
                format!("{{ \"or\": [{}] }}", parts.join(", "))
            }
            Self::Implies(lhs, rhs) => {
                format!(
                    "{{ \"implies\": {{ \"lhs\": {}, \"rhs\": {} }} }}",
                    lhs.to_json(),
                    rhs.to_json()
                )
            }
            Self::In { elem, set } => {
                format!(
                    "{{ \"in\": {{ \"elem\": {}, \"set\": {} }} }}",
                    elem.to_json(),
                    set.to_json()
                )
            }
            Self::ForAll { var, domain, body } => {
                format!(
                    "{{ \"forall\": {{ \"var\": \"{}\", \"domain\": {}, \"body\": {} }} }}",
                    escape_json(var),
                    domain.to_json(),
                    body.to_json()
                )
            }
            Self::Exists { var, domain, body } => {
                format!(
                    "{{ \"exists\": {{ \"var\": \"{}\", \"domain\": {}, \"body\": {} }} }}",
                    escape_json(var),
                    domain.to_json(),
                    body.to_json()
                )
            }
        }
    }
}

/// Comparison operators
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum CompareOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// An expression over state variables
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Expr {
    /// Integer literal
    Int(i64),
    /// Boolean literal
    Bool(bool),
    /// Variable reference
    Var(String),
    /// Primed variable (next-state value)
    Prime(String),
    /// Arithmetic binary operation
    BinOp {
        left: Box<Expr>,
        op: BinOp,
        right: Box<Expr>,
    },
    /// Unary operations
    UnaryOp { op: UnaryOp, arg: Box<Expr> },
    /// Conditional expression
    If {
        cond: Box<Predicate>,
        then_: Box<Expr>,
        else_: Box<Expr>,
    },
    /// Tuple construction
    Tuple(Vec<Expr>),
    /// Tuple projection
    Project { tuple: Box<Expr>, index: usize },
    /// Set literal
    SetLit(Vec<Expr>),
    /// Set comprehension
    SetComp {
        var: String,
        domain: Box<Expr>,
        filter: Box<Predicate>,
    },
    /// Function application (for opaque functions)
    Apply { func: String, args: Vec<Expr> },
}

impl Expr {
    fn to_json(&self) -> String {
        match self {
            Self::Int(i) => format!("{{ \"int\": {i} }}"),
            Self::Bool(b) => format!("{{ \"bool\": {b} }}"),
            Self::Var(v) => format!("{{ \"var\": \"{}\" }}", escape_json(v)),
            Self::Prime(v) => format!("{{ \"prime\": \"{}\" }}", escape_json(v)),
            Self::BinOp { left, op, right } => {
                format!(
                    "{{ \"binop\": {{ \"left\": {}, \"op\": \"{:?}\", \"right\": {} }} }}",
                    left.to_json(),
                    op,
                    right.to_json()
                )
            }
            Self::UnaryOp { op, arg } => {
                format!(
                    "{{ \"unaryop\": {{ \"op\": \"{:?}\", \"arg\": {} }} }}",
                    op,
                    arg.to_json()
                )
            }
            Self::If { cond, then_, else_ } => {
                format!(
                    "{{ \"if\": {{ \"cond\": {}, \"then\": {}, \"else\": {} }} }}",
                    cond.to_json(),
                    then_.to_json(),
                    else_.to_json()
                )
            }
            Self::Tuple(elems) => {
                let parts: Vec<String> = elems.iter().map(Self::to_json).collect();
                format!("{{ \"tuple\": [{}] }}", parts.join(", "))
            }
            Self::Project { tuple, index } => {
                format!(
                    "{{ \"project\": {{ \"tuple\": {}, \"index\": {} }} }}",
                    tuple.to_json(),
                    index
                )
            }
            Self::SetLit(elems) => {
                let parts: Vec<String> = elems.iter().map(Self::to_json).collect();
                format!("{{ \"set\": [{}] }}", parts.join(", "))
            }
            Self::SetComp {
                var,
                domain,
                filter,
            } => {
                format!(
                    "{{ \"setcomp\": {{ \"var\": \"{}\", \"domain\": {}, \"filter\": {} }} }}",
                    escape_json(var),
                    domain.to_json(),
                    filter.to_json()
                )
            }
            Self::Apply { func, args } => {
                let arg_parts: Vec<String> = args.iter().map(Self::to_json).collect();
                format!(
                    "{{ \"apply\": {{ \"func\": \"{}\", \"args\": [{}] }} }}",
                    escape_json(func),
                    arg_parts.join(", ")
                )
            }
        }
    }
}

/// Binary operators
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

/// Unary operators
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum UnaryOp {
    Neg,
    Not,
    BitNot,
}

/// Source location mapping
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SourceMap {
    /// Maps ActionIds to Rust source spans
    pub action_spans: HashMap<ActionId, SourceSpan>,
    /// Maps StateIds to Rust source spans
    pub state_spans: HashMap<StateId, SourceSpan>,
    /// Maps variable names to their declaration spans
    pub variable_spans: HashMap<String, SourceSpan>,
}

impl SourceMap {
    fn is_empty(&self) -> bool {
        self.action_spans.is_empty()
            && self.state_spans.is_empty()
            && self.variable_spans.is_empty()
    }
}

/// Source span for error reporting
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceSpan {
    /// File path (relative to crate root)
    pub file: String,
    /// Start line (1-indexed)
    pub line_start: u32,
    /// Start column (1-indexed)
    pub col_start: u32,
    /// End line (1-indexed)
    pub line_end: u32,
    /// End column (1-indexed)
    pub col_end: u32,
}

/// Escape JSON special characters
fn escape_json(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c => result.push(c),
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_model() {
        let model = TLA2Model::new("empty");
        let json = model.to_json();
        assert!(json.contains("\"name\": \"empty\""));
        assert!(json.contains("\"version\": \"1.0\""));
    }

    #[test]
    fn test_var_type_json() {
        assert_eq!(VarType::Bool.to_json(), "\"bool\"");
        assert_eq!(
            VarType::Int {
                bits: 32,
                signed: true
            }
            .to_json(),
            "\"i32\""
        );
        assert_eq!(
            VarType::Int {
                bits: 64,
                signed: false
            }
            .to_json(),
            "\"u64\""
        );
    }

    #[test]
    fn test_predicate_json() {
        let pred = Predicate::Bool(true);
        assert_eq!(pred.to_json(), "{ \"bool\": true }");

        let var_pred = Predicate::Var("x".to_string());
        assert!(var_pred.to_json().contains("\"var\": \"x\""));
    }

    #[test]
    fn test_expr_json() {
        let expr = Expr::Int(42);
        assert_eq!(expr.to_json(), "{ \"int\": 42 }");

        let var_expr = Expr::Var("y".to_string());
        assert!(var_expr.to_json().contains("\"var\": \"y\""));
    }

    #[test]
    fn test_transition_json() {
        let trans = Transition {
            action_id: ActionId(1),
            name: "step".to_string(),
            from: Some(StateId(0)),
            to: Some(StateId(1)),
            guard: Predicate::Bool(true),
            assignments: vec![],
            is_yield: true,
            is_poll: false,
        };

        let json = trans.to_json(2);
        assert!(json.contains("\"action_id\": 1"));
        assert!(json.contains("\"name\": \"step\""));
        assert!(json.contains("\"is_yield\": true"));
    }
}
