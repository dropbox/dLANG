//! Kernel Intermediate Representation

/// Kernel IR node types
#[derive(Clone, Debug)]
pub enum KernelIR {
    Input { name: String, shape: Vec<usize> },
    Output { name: String },
    BinOp { op: BinOpKind, lhs: NodeId, rhs: NodeId },
    UnaryOp { op: UnaryOpKind, input: NodeId },
    Constant { value: f64 },
}

#[derive(Clone, Copy, Debug)]
pub struct NodeId(pub usize);

#[derive(Clone, Copy, Debug)]
pub enum BinOpKind { Add, Sub, Mul, Div }

#[derive(Clone, Copy, Debug)]
pub enum UnaryOpKind { Sin, Cos, Exp, Log, Relu, Sigmoid, Tanh }
