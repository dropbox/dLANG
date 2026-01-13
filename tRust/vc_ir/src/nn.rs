//! Neural Network Verification Specifications
//!
//! Support for CROWN-style certified bounds and robustness verification
//! of neural networks.

use crate::{Expr, Predicate};
use serde::{Deserialize, Serialize};

/// A neural network specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum NnSpec {
    /// Local robustness: small perturbations don't change output
    LocalRobustness(RobustnessSpec),

    /// Global robustness: property holds for all inputs in region
    GlobalProperty(GlobalPropertySpec),

    /// Output bounds: network output is within bounds
    OutputBounds(BoundsSpec),

    /// Monotonicity: output is monotonic in certain inputs
    Monotonicity(MonotonicitySpec),

    /// Lipschitz continuity: bounded rate of change
    Lipschitz(LipschitzSpec),

    /// Fairness: output doesn't depend on protected attributes
    Fairness(FairnessSpec),

    /// Reachability: can the network produce certain outputs?
    Reachability(ReachabilitySpec),
}

/// Local robustness specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RobustnessSpec {
    /// The input point
    pub input: Expr,
    /// Perturbation budget
    pub epsilon: f64,
    /// Norm type for perturbation
    pub norm: Norm,
    /// Property that must hold under perturbation
    pub property: RobustnessProperty,
}

/// Norm type for measuring perturbations
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Norm {
    /// L-infinity norm (max absolute value)
    Linf,
    /// L2 norm (Euclidean)
    L2,
    /// L1 norm (sum of absolute values)
    L1,
    /// L0 "norm" (number of changed elements)
    L0,
}

/// Property that must hold under perturbation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RobustnessProperty {
    /// Classification doesn't change
    ClassificationInvariant,
    /// Output stays within bounds of original
    BoundedDeviation { delta: f64 },
    /// Specific output constraint
    OutputConstraint(Predicate),
    /// Top-k classes don't change
    TopKInvariant { k: usize },
}

/// Global property specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalPropertySpec {
    /// Input region
    pub input_region: InputRegion,
    /// Property that must hold for all inputs in region
    pub property: Predicate,
}

/// Specification of an input region
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum InputRegion {
    /// Hyperrectangle (box)
    Box { lower: Vec<f64>, upper: Vec<f64> },
    /// Ball around a point
    Ball {
        center: Vec<f64>,
        radius: f64,
        norm: Norm,
    },
    /// Polytope defined by linear constraints
    Polytope { constraints: Vec<LinearConstraint> },
    /// Union of regions
    Union(Vec<InputRegion>),
    /// Intersection of regions
    Intersection(Vec<InputRegion>),
    /// Constraint on input
    Constrained {
        base: Box<InputRegion>,
        constraint: Predicate,
    },
}

/// Linear constraint for polytopes
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LinearConstraint {
    /// Coefficients
    pub coeffs: Vec<f64>,
    /// Comparison operator
    pub op: ComparisonOp,
    /// Right-hand side
    pub rhs: f64,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum ComparisonOp {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
}

/// Output bounds specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BoundsSpec {
    /// Input region
    pub input_region: InputRegion,
    /// Expected lower bounds on outputs
    pub lower_bounds: Option<Vec<f64>>,
    /// Expected upper bounds on outputs
    pub upper_bounds: Option<Vec<f64>>,
}

/// Monotonicity specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonotonicitySpec {
    /// Which input dimensions should be monotonic
    pub input_dims: Vec<usize>,
    /// Which output dimensions
    pub output_dims: Vec<usize>,
    /// Increasing or decreasing
    pub increasing: bool,
    /// Region where monotonicity should hold
    pub region: InputRegion,
}

/// Lipschitz continuity specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LipschitzSpec {
    /// Lipschitz constant bound
    pub constant: f64,
    /// Norm for measuring input distance
    pub input_norm: Norm,
    /// Norm for measuring output distance
    pub output_norm: Norm,
    /// Region where bound should hold
    pub region: Option<InputRegion>,
}

/// Fairness specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FairnessSpec {
    /// Protected attribute indices
    pub protected_attributes: Vec<usize>,
    /// Fairness criterion
    pub criterion: FairnessCriterion,
    /// Input region
    pub region: InputRegion,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FairnessCriterion {
    /// Output independent of protected attributes
    Independence,
    /// Equal opportunity
    EqualOpportunity,
    /// Individual fairness (similar inputs -> similar outputs)
    Individual { similarity_threshold: f64 },
}

/// Reachability specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReachabilitySpec {
    /// Input region
    pub input_region: InputRegion,
    /// Target output region
    pub target_region: OutputRegion,
    /// Check if reachable or unreachable
    pub check_reachable: bool,
}

/// Output region specification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OutputRegion {
    /// Specific class
    Class(usize),
    /// Set of classes
    Classes(Vec<usize>),
    /// Box bounds
    Box { lower: Vec<f64>, upper: Vec<f64> },
    /// General predicate on output
    Predicate(Predicate),
}

/// Neural network architecture description (for verification)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NnArchitecture {
    /// Layer specifications
    pub layers: Vec<Layer>,
    /// Input shape
    pub input_shape: Vec<usize>,
    /// Output shape
    pub output_shape: Vec<usize>,
}

/// Neural network layer
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Layer {
    /// Fully connected
    Linear {
        in_features: usize,
        out_features: usize,
    },
    /// Convolution
    Conv2d {
        in_channels: usize,
        out_channels: usize,
        kernel_size: (usize, usize),
        stride: (usize, usize),
        padding: (usize, usize),
    },
    /// Activation function
    Activation(ActivationFn),
    /// Batch normalization
    BatchNorm { num_features: usize },
    /// Pooling
    Pool {
        kind: PoolKind,
        kernel_size: (usize, usize),
    },
    /// Flatten
    Flatten,
    /// Dropout (ignored during verification)
    Dropout,
    /// Residual connection
    Residual { inner: Vec<Layer> },
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum ActivationFn {
    ReLU,
    LeakyReLU { negative_slope: f64 },
    Sigmoid,
    Tanh,
    Softmax,
    GELU,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum PoolKind {
    Max,
    Avg,
}

/// Result of neural network verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NnVerifyResult {
    /// Verified or counterexample found
    pub status: NnVerifyStatus,
    /// Computed bounds (if applicable)
    pub bounds: Option<ComputedBounds>,
    /// Counterexample (if found)
    pub counterexample: Option<NnCounterexample>,
    /// Verification statistics
    pub stats: NnVerifyStats,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum NnVerifyStatus {
    /// Property verified
    Verified,
    /// Property violated with counterexample
    Violated,
    /// Unknown (timeout or incomplete)
    Unknown,
}

/// Computed bounds from bound propagation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComputedBounds {
    pub lower: Vec<f64>,
    pub upper: Vec<f64>,
}

/// Counterexample for neural network property
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NnCounterexample {
    /// Input that violates property
    pub input: Vec<f64>,
    /// Corresponding output
    pub output: Vec<f64>,
    /// Optional adversarial perturbation
    pub perturbation: Option<Vec<f64>>,
}

/// Statistics from NN verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NnVerifyStats {
    /// Time spent in bound propagation
    pub bound_propagation_time_ms: u64,
    /// Time spent in branching
    pub branching_time_ms: u64,
    /// Number of subproblems solved
    pub subproblems: usize,
    /// Number of neurons split
    pub neurons_split: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    // ===== Norm enum tests =====
    #[test]
    fn test_norm_variants() {
        let norms = [Norm::Linf, Norm::L2, Norm::L1, Norm::L0];
        assert_eq!(norms.len(), 4);
        // Test Copy
        let n = Norm::L2;
        let n2 = n;
        assert!(matches!(n, Norm::L2));
        assert!(matches!(n2, Norm::L2));
    }

    #[test]
    fn test_norm_serialization() {
        let norm = Norm::Linf;
        let json = serde_json::to_string(&norm).expect("serialize");
        let parsed: Norm = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(parsed, Norm::Linf));
    }

    // ===== ComparisonOp enum tests =====
    #[test]
    fn test_comparison_op_variants() {
        let ops = [
            ComparisonOp::Le,
            ComparisonOp::Lt,
            ComparisonOp::Ge,
            ComparisonOp::Gt,
            ComparisonOp::Eq,
        ];
        assert_eq!(ops.len(), 5);
    }

    #[test]
    fn test_comparison_op_serialization() {
        let op = ComparisonOp::Le;
        let json = serde_json::to_string(&op).expect("serialize");
        let parsed: ComparisonOp = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(parsed, ComparisonOp::Le));
    }

    // ===== RobustnessProperty tests =====
    #[test]
    fn test_robustness_property_classification_invariant() {
        let prop = RobustnessProperty::ClassificationInvariant;
        assert!(format!("{prop:?}").contains("ClassificationInvariant"));
    }

    #[test]
    fn test_robustness_property_bounded_deviation() {
        let prop = RobustnessProperty::BoundedDeviation { delta: 0.1 };
        if let RobustnessProperty::BoundedDeviation { delta } = prop {
            assert!((delta - 0.1).abs() < f64::EPSILON);
        } else {
            panic!("Expected BoundedDeviation");
        }
    }

    #[test]
    fn test_robustness_property_top_k() {
        let prop = RobustnessProperty::TopKInvariant { k: 5 };
        if let RobustnessProperty::TopKInvariant { k } = prop {
            assert_eq!(k, 5);
        } else {
            panic!("Expected TopKInvariant");
        }
    }

    // ===== InputRegion tests =====
    #[test]
    fn test_input_region_box() {
        let region = InputRegion::Box {
            lower: vec![0.0, 0.0],
            upper: vec![1.0, 1.0],
        };
        if let InputRegion::Box { lower, upper } = &region {
            assert_eq!(lower.len(), 2);
            assert_eq!(upper.len(), 2);
        } else {
            panic!("Expected Box");
        }
    }

    #[test]
    fn test_input_region_ball() {
        let region = InputRegion::Ball {
            center: vec![0.5, 0.5],
            radius: 0.1,
            norm: Norm::L2,
        };
        if let InputRegion::Ball {
            center,
            radius,
            norm,
        } = &region
        {
            assert_eq!(center.len(), 2);
            assert!((radius - 0.1).abs() < f64::EPSILON);
            assert!(matches!(norm, Norm::L2));
        } else {
            panic!("Expected Ball");
        }
    }

    #[test]
    fn test_input_region_polytope() {
        let constraint = LinearConstraint {
            coeffs: vec![1.0, -1.0],
            op: ComparisonOp::Le,
            rhs: 0.0,
        };
        let region = InputRegion::Polytope {
            constraints: vec![constraint],
        };
        if let InputRegion::Polytope { constraints } = &region {
            assert_eq!(constraints.len(), 1);
        } else {
            panic!("Expected Polytope");
        }
    }

    #[test]
    fn test_input_region_union() {
        let r1 = InputRegion::Box {
            lower: vec![0.0],
            upper: vec![0.5],
        };
        let r2 = InputRegion::Box {
            lower: vec![0.5],
            upper: vec![1.0],
        };
        let union = InputRegion::Union(vec![r1, r2]);
        if let InputRegion::Union(regions) = &union {
            assert_eq!(regions.len(), 2);
        } else {
            panic!("Expected Union");
        }
    }

    #[test]
    fn test_input_region_intersection() {
        let r1 = InputRegion::Box {
            lower: vec![0.0],
            upper: vec![0.7],
        };
        let r2 = InputRegion::Box {
            lower: vec![0.3],
            upper: vec![1.0],
        };
        let intersection = InputRegion::Intersection(vec![r1, r2]);
        if let InputRegion::Intersection(regions) = &intersection {
            assert_eq!(regions.len(), 2);
        } else {
            panic!("Expected Intersection");
        }
    }

    #[test]
    fn test_input_region_serialization() {
        let region = InputRegion::Box {
            lower: vec![0.0, 0.0],
            upper: vec![1.0, 1.0],
        };
        let json = serde_json::to_string(&region).expect("serialize");
        let parsed: InputRegion = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(parsed, InputRegion::Box { .. }));
    }

    // ===== LinearConstraint tests =====
    #[test]
    fn test_linear_constraint() {
        let constraint = LinearConstraint {
            coeffs: vec![1.0, 2.0, 3.0],
            op: ComparisonOp::Le,
            rhs: 10.0,
        };
        assert_eq!(constraint.coeffs.len(), 3);
        assert!((constraint.rhs - 10.0).abs() < f64::EPSILON);
    }

    // ===== NnSpec tests =====
    #[test]
    fn test_nn_spec_local_robustness() {
        let spec = NnSpec::LocalRobustness(RobustnessSpec {
            input: Expr::var("x"),
            epsilon: 0.01,
            norm: Norm::Linf,
            property: RobustnessProperty::ClassificationInvariant,
        });
        assert!(matches!(spec, NnSpec::LocalRobustness(_)));
    }

    #[test]
    fn test_nn_spec_output_bounds() {
        let spec = NnSpec::OutputBounds(BoundsSpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            lower_bounds: Some(vec![0.0]),
            upper_bounds: Some(vec![1.0]),
        });
        assert!(matches!(spec, NnSpec::OutputBounds(_)));
    }

    #[test]
    fn test_nn_spec_monotonicity() {
        let spec = NnSpec::Monotonicity(MonotonicitySpec {
            input_dims: vec![0, 1],
            output_dims: vec![0],
            increasing: true,
            region: InputRegion::Box {
                lower: vec![0.0, 0.0],
                upper: vec![1.0, 1.0],
            },
        });
        assert!(matches!(spec, NnSpec::Monotonicity(_)));
    }

    #[test]
    fn test_nn_spec_lipschitz() {
        let spec = NnSpec::Lipschitz(LipschitzSpec {
            constant: 1.0,
            input_norm: Norm::L2,
            output_norm: Norm::L2,
            region: None,
        });
        assert!(matches!(spec, NnSpec::Lipschitz(_)));
    }

    #[test]
    fn test_nn_spec_fairness() {
        let spec = NnSpec::Fairness(FairnessSpec {
            protected_attributes: vec![0],
            criterion: FairnessCriterion::Independence,
            region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
        });
        assert!(matches!(spec, NnSpec::Fairness(_)));
    }

    #[test]
    fn test_nn_spec_reachability() {
        let spec = NnSpec::Reachability(ReachabilitySpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            target_region: OutputRegion::Class(0),
            check_reachable: true,
        });
        assert!(matches!(spec, NnSpec::Reachability(_)));
    }

    // ===== FairnessCriterion tests =====
    #[test]
    fn test_fairness_criterion_variants() {
        let independence = FairnessCriterion::Independence;
        let equal_opp = FairnessCriterion::EqualOpportunity;
        let individual = FairnessCriterion::Individual {
            similarity_threshold: 0.1,
        };
        assert!(format!("{independence:?}").contains("Independence"));
        assert!(format!("{equal_opp:?}").contains("EqualOpportunity"));
        assert!(format!("{individual:?}").contains("Individual"));
    }

    // ===== OutputRegion tests =====
    #[test]
    fn test_output_region_class() {
        let region = OutputRegion::Class(5);
        if let OutputRegion::Class(c) = region {
            assert_eq!(c, 5);
        } else {
            panic!("Expected Class");
        }
    }

    #[test]
    fn test_output_region_classes() {
        let region = OutputRegion::Classes(vec![0, 1, 2]);
        if let OutputRegion::Classes(cs) = &region {
            assert_eq!(cs.len(), 3);
        } else {
            panic!("Expected Classes");
        }
    }

    #[test]
    fn test_output_region_box() {
        let region = OutputRegion::Box {
            lower: vec![0.0],
            upper: vec![1.0],
        };
        assert!(matches!(region, OutputRegion::Box { .. }));
    }

    // ===== NnArchitecture tests =====
    #[test]
    fn test_nn_architecture() {
        let arch = NnArchitecture {
            layers: vec![
                Layer::Linear {
                    in_features: 784,
                    out_features: 256,
                },
                Layer::Activation(ActivationFn::ReLU),
                Layer::Linear {
                    in_features: 256,
                    out_features: 10,
                },
            ],
            input_shape: vec![1, 28, 28],
            output_shape: vec![10],
        };
        assert_eq!(arch.layers.len(), 3);
        assert_eq!(arch.input_shape, vec![1, 28, 28]);
    }

    // ===== Layer tests =====
    #[test]
    fn test_layer_linear() {
        let layer = Layer::Linear {
            in_features: 100,
            out_features: 50,
        };
        if let Layer::Linear {
            in_features,
            out_features,
        } = layer
        {
            assert_eq!(in_features, 100);
            assert_eq!(out_features, 50);
        } else {
            panic!("Expected Linear");
        }
    }

    #[test]
    fn test_layer_conv2d() {
        let layer = Layer::Conv2d {
            in_channels: 3,
            out_channels: 64,
            kernel_size: (3, 3),
            stride: (1, 1),
            padding: (1, 1),
        };
        assert!(matches!(layer, Layer::Conv2d { .. }));
    }

    #[test]
    fn test_layer_activation() {
        let relu = Layer::Activation(ActivationFn::ReLU);
        let sigmoid = Layer::Activation(ActivationFn::Sigmoid);
        let tanh = Layer::Activation(ActivationFn::Tanh);
        let softmax = Layer::Activation(ActivationFn::Softmax);
        let gelu = Layer::Activation(ActivationFn::GELU);
        let leaky = Layer::Activation(ActivationFn::LeakyReLU {
            negative_slope: 0.01,
        });
        assert!(matches!(relu, Layer::Activation(ActivationFn::ReLU)));
        assert!(matches!(sigmoid, Layer::Activation(ActivationFn::Sigmoid)));
        assert!(matches!(tanh, Layer::Activation(ActivationFn::Tanh)));
        assert!(matches!(softmax, Layer::Activation(ActivationFn::Softmax)));
        assert!(matches!(gelu, Layer::Activation(ActivationFn::GELU)));
        assert!(matches!(
            leaky,
            Layer::Activation(ActivationFn::LeakyReLU { .. })
        ));
    }

    #[test]
    fn test_layer_batch_norm() {
        let layer = Layer::BatchNorm { num_features: 64 };
        if let Layer::BatchNorm { num_features } = layer {
            assert_eq!(num_features, 64);
        } else {
            panic!("Expected BatchNorm");
        }
    }

    #[test]
    fn test_layer_pool() {
        let max_pool = Layer::Pool {
            kind: PoolKind::Max,
            kernel_size: (2, 2),
        };
        let avg_pool = Layer::Pool {
            kind: PoolKind::Avg,
            kernel_size: (2, 2),
        };
        assert!(matches!(
            max_pool,
            Layer::Pool {
                kind: PoolKind::Max,
                ..
            }
        ));
        assert!(matches!(
            avg_pool,
            Layer::Pool {
                kind: PoolKind::Avg,
                ..
            }
        ));
    }

    #[test]
    fn test_layer_flatten_dropout() {
        let flatten = Layer::Flatten;
        let dropout = Layer::Dropout;
        assert!(matches!(flatten, Layer::Flatten));
        assert!(matches!(dropout, Layer::Dropout));
    }

    #[test]
    fn test_layer_residual() {
        let residual = Layer::Residual {
            inner: vec![
                Layer::Linear {
                    in_features: 64,
                    out_features: 64,
                },
                Layer::Activation(ActivationFn::ReLU),
            ],
        };
        if let Layer::Residual { inner } = &residual {
            assert_eq!(inner.len(), 2);
        } else {
            panic!("Expected Residual");
        }
    }

    // ===== NnVerifyResult tests =====
    #[test]
    fn test_nn_verify_result() {
        let result = NnVerifyResult {
            status: NnVerifyStatus::Verified,
            bounds: Some(ComputedBounds {
                lower: vec![0.0],
                upper: vec![1.0],
            }),
            counterexample: None,
            stats: NnVerifyStats {
                bound_propagation_time_ms: 100,
                branching_time_ms: 50,
                subproblems: 10,
                neurons_split: 5,
            },
        };
        assert!(matches!(result.status, NnVerifyStatus::Verified));
        assert!(result.bounds.is_some());
        assert!(result.counterexample.is_none());
    }

    #[test]
    fn test_nn_verify_status_variants() {
        let verified = NnVerifyStatus::Verified;
        let violated = NnVerifyStatus::Violated;
        let unknown = NnVerifyStatus::Unknown;
        // Test Copy
        let v2 = verified;
        assert!(matches!(v2, NnVerifyStatus::Verified));
        assert!(matches!(violated, NnVerifyStatus::Violated));
        assert!(matches!(unknown, NnVerifyStatus::Unknown));
    }

    // ===== ComputedBounds tests =====
    #[test]
    fn test_computed_bounds() {
        let bounds = ComputedBounds {
            lower: vec![-1.0, -2.0],
            upper: vec![1.0, 2.0],
        };
        assert_eq!(bounds.lower.len(), 2);
        assert_eq!(bounds.upper.len(), 2);
    }

    // ===== NnCounterexample tests =====
    #[test]
    fn test_nn_counterexample() {
        let cex = NnCounterexample {
            input: vec![0.5, 0.5],
            output: vec![0.9, 0.1],
            perturbation: Some(vec![0.01, -0.01]),
        };
        assert_eq!(cex.input.len(), 2);
        assert_eq!(cex.output.len(), 2);
        assert!(cex.perturbation.is_some());
    }

    #[test]
    fn test_nn_counterexample_no_perturbation() {
        let cex = NnCounterexample {
            input: vec![0.5],
            output: vec![0.9],
            perturbation: None,
        };
        assert!(cex.perturbation.is_none());
    }

    // ===== NnVerifyStats tests =====
    #[test]
    fn test_nn_verify_stats() {
        let stats = NnVerifyStats {
            bound_propagation_time_ms: 1000,
            branching_time_ms: 500,
            subproblems: 100,
            neurons_split: 50,
        };
        assert_eq!(stats.bound_propagation_time_ms, 1000);
        assert_eq!(stats.branching_time_ms, 500);
        assert_eq!(stats.subproblems, 100);
        assert_eq!(stats.neurons_split, 50);
    }

    // ===== Serialization round-trip tests =====
    #[test]
    fn test_nn_spec_serialization() {
        let spec = NnSpec::OutputBounds(BoundsSpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            lower_bounds: None,
            upper_bounds: None,
        });
        let json = serde_json::to_string(&spec).expect("serialize");
        let parsed: NnSpec = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(parsed, NnSpec::OutputBounds(_)));
    }

    #[test]
    fn test_nn_architecture_serialization() {
        let arch = NnArchitecture {
            layers: vec![Layer::Flatten, Layer::Dropout],
            input_shape: vec![28, 28],
            output_shape: vec![10],
        };
        let json = serde_json::to_string(&arch).expect("serialize");
        let parsed: NnArchitecture = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(parsed.layers.len(), 2);
    }

    #[test]
    fn test_nn_verify_result_serialization() {
        let result = NnVerifyResult {
            status: NnVerifyStatus::Unknown,
            bounds: None,
            counterexample: None,
            stats: NnVerifyStats {
                bound_propagation_time_ms: 0,
                branching_time_ms: 0,
                subproblems: 0,
                neurons_split: 0,
            },
        };
        let json = serde_json::to_string(&result).expect("serialize");
        let parsed: NnVerifyResult = serde_json::from_str(&json).expect("deserialize");
        assert!(matches!(parsed.status, NnVerifyStatus::Unknown));
    }

    // ===== Clone tests =====
    #[test]
    fn test_nn_spec_clone() {
        let spec = NnSpec::Lipschitz(LipschitzSpec {
            constant: 1.5,
            input_norm: Norm::L2,
            output_norm: Norm::Linf,
            region: Some(InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            }),
        });
        let cloned = spec.clone();
        assert!(matches!(cloned, NnSpec::Lipschitz(_)));
    }
}
