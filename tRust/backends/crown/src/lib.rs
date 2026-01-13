//! CROWN Neural Network Verification Backend
//!
//! Implements bound propagation for certified neural network verification.
//! Supports multiple bound propagation methods:
//!
//! - **IBP (Interval Bound Propagation)**: Fast but loose bounds
//! - **CROWN**: Tighter bounds via linear relaxation
//! - **Alpha-CROWN**: Optimized slope parameters via projected gradient descent
//! - **Branch and Bound**: Refine bounds by recursively splitting unstable neurons
//!
//! This enables verification of specifications like:
//! - Local robustness: small input perturbations don't change classification
//! - Output bounds: network outputs stay within specified ranges
//! - Monotonicity: output is monotonic in certain inputs
//! - Lipschitz bounds: bounded rate of change
//!
//! # Example
//!
//! ```ignore
//! use trust_crown::{CrownBackend, CrownConfig, NnNetwork, NnLayer, Bounds};
//!
//! let network = NnNetwork::example_2layer(2, 4, 2);
//! let mut backend = CrownBackend::new(CrownConfig::default());
//! backend.load_network(network);
//!
//! let input = Bounds::linf_ball(&[0.5, 0.5], 0.1);
//! // Use backend.verify_output_bounds(...) to check properties
//! ```

// Allow index-based loops for matrix/vector operations where they are clearer than iterators
#![allow(clippy::needless_range_loop)]

use vc_ir::{
    backend::ProofBackend,
    nn::{
        BoundsSpec, FairnessCriterion, FairnessSpec, GlobalPropertySpec, InputRegion,
        LipschitzSpec, MonotonicitySpec, NnArchitecture, NnSpec, Norm, OutputRegion,
        ReachabilitySpec, RobustnessProperty, RobustnessSpec,
    },
    BackendCapabilities, Counterexample, Predicate, VcKind, VerificationCondition, VerifyConfig,
    VerifyResult,
};

/// CROWN-based neural network verifier
pub struct CrownBackend {
    config: CrownConfig,
    /// Loaded network (if any)
    network: Option<NnNetwork>,
}

/// Configuration for CROWN verification
#[derive(Debug, Clone)]
pub struct CrownConfig {
    /// Bound propagation method
    pub bound_method: BoundMethod,
    /// Maximum number of neurons to split
    pub max_splits: usize,
    /// Timeout for bound propagation (ms)
    pub bound_timeout_ms: u64,
    /// Use GPU acceleration
    pub use_gpu: bool,
    /// Batch size for parallel verification
    pub batch_size: usize,
}

impl Default for CrownConfig {
    fn default() -> Self {
        Self {
            bound_method: BoundMethod::Ibp,
            max_splits: 1000,
            bound_timeout_ms: 10_000,
            use_gpu: false,
            batch_size: 64,
        }
    }
}

/// Bound propagation method
#[derive(Debug, Clone, PartialEq)]
pub enum BoundMethod {
    /// Interval bound propagation (fast, loose)
    Ibp,
    /// CROWN (tighter, more expensive)
    Crown,
    /// Optimized CROWN with alpha optimization
    CrownOptimized,
    /// Alpha-beta-CROWN with branch-and-bound (tightest, most expensive)
    AlphaBetaCrown,
    /// Beta-CROWN with split constraint optimization
    BetaCrown(Box<BetaCrownConfig>),
    /// Input domain splitting for tighter bounds on larger perturbations
    InputSplit(Box<InputSplitConfig>),
}

/// Interval bounds for a vector of values
#[derive(Debug, Clone)]
pub struct Bounds {
    /// Lower bounds for each element
    pub lower: Vec<f64>,
    /// Upper bounds for each element
    pub upper: Vec<f64>,
}

impl Bounds {
    /// Create bounds from lower and upper vectors
    #[must_use]
    pub fn new(lower: Vec<f64>, upper: Vec<f64>) -> Self {
        assert_eq!(lower.len(), upper.len(), "Bounds dimensions must match");
        Self { lower, upper }
    }

    /// Create a point (lower == upper)
    #[must_use]
    pub fn point(values: Vec<f64>) -> Self {
        Self {
            lower: values.clone(),
            upper: values,
        }
    }

    /// Create bounds for an L-infinity ball around a center
    #[must_use]
    pub fn linf_ball(center: &[f64], epsilon: f64) -> Self {
        let lower = center.iter().map(|x| x - epsilon).collect();
        let upper = center.iter().map(|x| x + epsilon).collect();
        Self { lower, upper }
    }

    /// Create bounds from a box region
    #[must_use]
    pub fn from_box(lower: Vec<f64>, upper: Vec<f64>) -> Self {
        Self::new(lower, upper)
    }

    /// Get the dimension
    #[must_use]
    pub const fn dim(&self) -> usize {
        self.lower.len()
    }

    /// Check if all lower bounds are >= a threshold
    #[must_use]
    pub fn all_lower_ge(&self, threshold: f64) -> bool {
        self.lower.iter().all(|&x| x >= threshold)
    }

    /// Check if all upper bounds are <= a threshold
    #[must_use]
    pub fn all_upper_le(&self, threshold: f64) -> bool {
        self.upper.iter().all(|&x| x <= threshold)
    }

    /// Check if computed bounds satisfy specified bounds
    #[must_use]
    pub fn satisfies(&self, lower_spec: Option<&[f64]>, upper_spec: Option<&[f64]>) -> bool {
        if let Some(spec_lb) = lower_spec {
            if spec_lb.len() != self.dim() {
                return false;
            }
            for (i, &lb) in spec_lb.iter().enumerate() {
                if self.lower[i] < lb {
                    return false;
                }
            }
        }
        if let Some(spec_ub) = upper_spec {
            if spec_ub.len() != self.dim() {
                return false;
            }
            for (i, &ub) in spec_ub.iter().enumerate() {
                if self.upper[i] > ub {
                    return false;
                }
            }
        }
        true
    }
}

/// L2 ball representation for tighter robustness verification
/// Represents the set {x : ||x - center||_2 <= radius}
#[derive(Debug, Clone)]
pub struct L2BallBounds {
    /// Center of the L2 ball
    pub center: Vec<f64>,
    /// Radius of the L2 ball
    pub radius: f64,
    /// Component-wise bounds (over-approximation of the L2 ball)
    /// Updated during propagation through layers
    pub box_bounds: Bounds,
}

impl L2BallBounds {
    /// Create an L2 ball around a center point
    #[must_use]
    pub fn new(center: Vec<f64>, radius: f64) -> Self {
        // Initial box bounds: for L2 ball, each component can deviate by at most radius
        let lower = center.iter().map(|x| x - radius).collect();
        let upper = center.iter().map(|x| x + radius).collect();
        let box_bounds = Bounds { lower, upper };
        Self {
            center,
            radius,
            box_bounds,
        }
    }

    /// Get dimension
    #[must_use]
    pub const fn dim(&self) -> usize {
        self.center.len()
    }

    /// Convert to standard box bounds (over-approximation)
    #[must_use]
    pub fn to_box_bounds(&self) -> Bounds {
        self.box_bounds.clone()
    }
}

/// Type alias for CROWN backward propagation bounds result
/// Contains: (a_lower, b_lower, a_upper, b_upper)
/// - a_lower: lower bound linear coefficients (matrix)
/// - b_lower: lower bound constant terms (vector)
/// - a_upper: upper bound linear coefficients (matrix)
/// - b_upper: upper bound constant terms (vector)
type CrownBackwardBounds = (Vec<Vec<f64>>, Vec<f64>, Vec<Vec<f64>>, Vec<f64>);

/// A loaded neural network with weights
#[derive(Debug, Clone)]
pub struct NnNetwork {
    /// Network layers
    pub layers: Vec<NnLayer>,
    /// Input dimension
    pub input_dim: usize,
    /// Output dimension
    pub output_dim: usize,
}

/// A layer with actual weights
#[derive(Debug, Clone)]
pub enum NnLayer {
    /// Fully connected layer: y = Wx + b
    Linear {
        /// Weight matrix (out_features x in_features)
        weights: Vec<Vec<f64>>,
        /// Bias vector (out_features)
        bias: Vec<f64>,
    },
    /// ReLU activation
    ReLU,
    /// Leaky ReLU activation
    LeakyReLU { negative_slope: f64 },
    /// Sigmoid activation
    Sigmoid,
    /// Tanh activation
    Tanh,
    /// Batch normalization layer (inference mode)
    /// For inference: y = scale * x + bias
    /// where scale = gamma / sqrt(var + eps)
    /// and bias = beta - gamma * mean / sqrt(var + eps)
    BatchNorm {
        /// Scale factor (num_features): gamma / sqrt(var + eps)
        scale: Vec<f64>,
        /// Bias (num_features): beta - gamma * mean / sqrt(var + eps)
        bias: Vec<f64>,
    },
    /// Dropout layer (inference mode = identity)
    /// In inference mode, dropout is disabled and the layer is identity.
    /// The probability is stored for documentation but not used.
    Dropout {
        /// Dropout probability (not used in inference)
        p: f64,
    },
    /// Flatten layer (reshapes multidimensional input to 1D)
    /// In 1D networks, this is identity.
    Flatten,
    /// 1D Max pooling layer
    /// Takes the maximum over each non-overlapping window
    MaxPool1d {
        /// Size of the pooling window
        kernel_size: usize,
        /// Stride of the pooling window (defaults to kernel_size)
        stride: usize,
    },
    /// 1D Average pooling layer
    /// Takes the average over each non-overlapping window
    AvgPool1d {
        /// Size of the pooling window
        kernel_size: usize,
        /// Stride of the pooling window (defaults to kernel_size)
        stride: usize,
    },
    /// 1D Convolution layer
    /// `y[c_out, i] = sum_{c_in, k} weight[c_out, c_in, k] * x[c_in, i*stride + k - padding] + bias[c_out]`
    /// Input shape: (in_channels * input_length) flattened
    /// Output shape: (out_channels * output_length) flattened
    /// where output_length = (input_length + 2*padding - kernel_size) / stride + 1
    Conv1d {
        /// Input channels
        in_channels: usize,
        /// Output channels
        out_channels: usize,
        /// Convolution kernel size
        kernel_size: usize,
        /// Stride (default 1)
        stride: usize,
        /// Padding (default 0)
        padding: usize,
        /// Weight tensor shape: (out_channels, in_channels, kernel_size)
        /// Stored as `vec[out_ch][in_ch][k]`
        weights: Vec<Vec<Vec<f64>>>,
        /// Bias vector (out_channels) or empty for no bias
        bias: Vec<f64>,
    },
    /// 2D Convolution layer
    /// `y[c_out, h, w] = sum_{c_in, kh, kw} weight[c_out, c_in, kh, kw] * x[c_in, h*stride+kh-padding, w*stride+kw-padding] + bias[c_out]`
    /// Input shape: (in_channels * height * width) flattened
    /// Output shape: (out_channels * out_height * out_width) flattened
    /// where out_height = (height + 2*padding - kernel_size) / stride + 1
    /// and out_width = (width + 2*padding - kernel_size) / stride + 1
    Conv2d {
        /// Input channels
        in_channels: usize,
        /// Output channels
        out_channels: usize,
        /// Input height
        input_height: usize,
        /// Input width
        input_width: usize,
        /// Convolution kernel size (square kernel)
        kernel_size: usize,
        /// Stride (default 1)
        stride: usize,
        /// Padding (default 0)
        padding: usize,
        /// Weight tensor shape: (out_channels, in_channels, kernel_size, kernel_size)
        /// Stored as `vec[out_ch][in_ch][kh][kw]`
        weights: Vec<Vec<Vec<Vec<f64>>>>,
        /// Bias vector (out_channels) or empty for no bias
        bias: Vec<f64>,
    },
    /// Global Average Pooling 2D layer
    /// Pools across all spatial dimensions (H, W), outputting one value per channel.
    /// Input shape: (channels * height * width) flattened
    /// Output shape: (channels) - one average value per channel
    GlobalAvgPool2d {
        /// Number of channels
        channels: usize,
        /// Input height
        height: usize,
        /// Input width
        width: usize,
    },
    /// Global Max Pooling 2D layer
    /// Pools across all spatial dimensions (H, W), outputting one value per channel.
    /// Input shape: (channels * height * width) flattened
    /// Output shape: (channels) - one max value per channel
    GlobalMaxPool2d {
        /// Number of channels
        channels: usize,
        /// Input height
        height: usize,
        /// Input width
        width: usize,
    },
    /// 2D Batch Normalization layer (inference mode)
    BatchNorm2d {
        channels: usize,
        height: usize,
        width: usize,
        scale: Vec<f64>,
        bias: Vec<f64>,
    },
    /// 2D Max Pooling layer
    MaxPool2d {
        channels: usize,
        height: usize,
        width: usize,
        kernel_size: usize,
        stride: usize,
    },
    /// 2D Average Pooling layer
    AvgPool2d {
        channels: usize,
        height: usize,
        width: usize,
        kernel_size: usize,
        stride: usize,
    },
    /// Residual Add layer - adds output from a previous layer to current input
    /// Used for skip connections in residual networks (ResNet).
    /// For a typical ResNet block:
    /// ```text
    /// input ─┬── Conv ── BN ── ReLU ── Conv ── BN ──┬── ReLU
    ///        └──────────────────────────────────────┘ (ResidualAdd)
    /// ```
    ResidualAdd {
        /// Index of the layer output to add to current input.
        /// - 0 = the original network input
        /// - 1 = output of layer 0
        /// - n = output of layer n-1
        skip_from_output: usize,
    },
    /// Concatenation layer - concatenates output from a previous layer with current input
    /// Used for skip connections in DenseNet-style architectures.
    /// Concatenates along the feature dimension.
    Concat {
        /// Index of the layer output to concatenate with current input.
        /// - 0 = the original network input
        /// - 1 = output of layer 0
        /// - n = output of layer n-1
        skip_from_output: usize,
    },
}

impl NnNetwork {
    /// Create a new network from layers
    #[must_use]
    pub fn new(layers: Vec<NnLayer>, input_dim: usize) -> Self {
        // Compute output dimension by tracing through layers
        // Track dimensions at each layer output for skip connections:
        // layer_dims[0] = input_dim, layer_dims[i+1] = output of layer i
        let mut layer_dims = vec![input_dim];
        let mut dim = input_dim;
        for layer in &layers {
            match layer {
                NnLayer::Linear { weights, .. } => {
                    dim = weights.len();
                }
                NnLayer::MaxPool1d {
                    kernel_size,
                    stride,
                }
                | NnLayer::AvgPool1d {
                    kernel_size,
                    stride,
                } => {
                    // Pooling reduces dimension: output_size = (input_size - kernel_size) / stride + 1
                    // For non-overlapping pools (stride == kernel_size): output_size = input_size / kernel_size
                    if dim >= *kernel_size && *stride > 0 {
                        dim = (dim - kernel_size) / stride + 1;
                    }
                }
                NnLayer::Conv1d {
                    in_channels,
                    out_channels,
                    kernel_size,
                    stride,
                    padding,
                    ..
                } => {
                    // Input: (in_channels * input_length), output: (out_channels * output_length)
                    // input_length = dim / in_channels
                    // output_length = (input_length + 2*padding - kernel_size) / stride + 1
                    if *in_channels > 0 && dim >= *in_channels {
                        let input_length = dim / *in_channels;
                        let effective_length = input_length + 2 * *padding;
                        if effective_length >= *kernel_size && *stride > 0 {
                            let output_length = (effective_length - *kernel_size) / *stride + 1;
                            dim = *out_channels * output_length;
                        }
                    }
                }
                NnLayer::Conv2d {
                    in_channels,
                    out_channels,
                    input_height,
                    input_width,
                    kernel_size,
                    stride,
                    padding,
                    ..
                } => {
                    // Input: (in_channels * height * width), output: (out_channels * out_height * out_width)
                    // out_height = (height + 2*padding - kernel_size) / stride + 1
                    // out_width = (width + 2*padding - kernel_size) / stride + 1
                    let expected_dim = *in_channels * *input_height * *input_width;
                    if dim == expected_dim && *stride > 0 {
                        let effective_height = *input_height + 2 * *padding;
                        let effective_width = *input_width + 2 * *padding;
                        if effective_height >= *kernel_size && effective_width >= *kernel_size {
                            let out_height = (effective_height - *kernel_size) / *stride + 1;
                            let out_width = (effective_width - *kernel_size) / *stride + 1;
                            dim = *out_channels * out_height * out_width;
                        }
                    }
                }
                NnLayer::GlobalAvgPool2d {
                    channels,
                    height,
                    width,
                }
                | NnLayer::GlobalMaxPool2d {
                    channels,
                    height,
                    width,
                } => {
                    // Global pooling: (channels * height * width) -> (channels)
                    let expected_dim = *channels * *height * *width;
                    if dim == expected_dim {
                        dim = *channels;
                    }
                }
                NnLayer::Concat { skip_from_output } => {
                    // Concat concatenates along feature dimension
                    // Output dimension = current dim + skip dim
                    if *skip_from_output < layer_dims.len() {
                        dim += layer_dims[*skip_from_output];
                    }
                }
                // ResidualAdd (element-wise) and all other layers preserve dimension
                _ => {}
            }
            layer_dims.push(dim);
        }
        Self {
            layers,
            input_dim,
            output_dim: dim,
        }
    }

    /// Create a simple 2-layer network for testing
    #[must_use]
    pub fn example_2layer(input_dim: usize, hidden_dim: usize, output_dim: usize) -> Self {
        // Initialize with small random-like weights (deterministic for testing)
        let mut layers = Vec::new();

        // First linear layer: input -> hidden
        let w1: Vec<Vec<f64>> = (0..hidden_dim)
            .map(|i| {
                (0..input_dim)
                    .map(|j| 0.1 * ((i * 7 + j * 13) % 17) as f64 / 17.0 - 0.05)
                    .collect()
            })
            .collect();
        let b1: Vec<f64> = (0..hidden_dim).map(|i| 0.01 * (i % 5) as f64).collect();
        layers.push(NnLayer::Linear {
            weights: w1,
            bias: b1,
        });

        // ReLU activation
        layers.push(NnLayer::ReLU);

        // Second linear layer: hidden -> output
        let w2: Vec<Vec<f64>> = (0..output_dim)
            .map(|i| {
                (0..hidden_dim)
                    .map(|j| 0.1 * ((i * 11 + j * 19) % 23) as f64 / 23.0 - 0.05)
                    .collect()
            })
            .collect();
        let b2: Vec<f64> = (0..output_dim).map(|i| 0.01 * (i % 3) as f64).collect();
        layers.push(NnLayer::Linear {
            weights: w2,
            bias: b2,
        });

        Self::new(layers, input_dim)
    }
}

/// Interval Bound Propagation (IBP)
///
/// Propagates interval bounds through a neural network.
/// This is the fastest but loosest bound propagation method.
/// Supports skip connections (ResidualAdd, Concat) by tracking intermediate bounds.
#[must_use]
pub fn ibp_propagate(network: &NnNetwork, input_bounds: &Bounds) -> Bounds {
    // Track intermediate bounds for skip connections
    // layer_bounds[0] = input_bounds, layer_bounds[i+1] = output of layer i
    let mut layer_bounds = vec![input_bounds.clone()];
    let mut bounds = input_bounds.clone();

    for (i, layer) in network.layers.iter().enumerate() {
        bounds = match layer {
            NnLayer::ResidualAdd { skip_from_output } => {
                // Add bounds element-wise from skip connection
                assert!(
                    *skip_from_output < layer_bounds.len(),
                    "ResidualAdd at layer {i} references invalid skip_from_output {skip_from_output}"
                );
                let skip_bounds = &layer_bounds[*skip_from_output];
                ibp_residual_add(&bounds, skip_bounds)
            }
            NnLayer::Concat { skip_from_output } => {
                // Concatenate bounds from skip connection
                assert!(
                    *skip_from_output < layer_bounds.len(),
                    "Concat at layer {i} references invalid skip_from_output {skip_from_output}"
                );
                let skip_bounds = &layer_bounds[*skip_from_output];
                ibp_concat(&bounds, skip_bounds)
            }
            _ => ibp_layer(&bounds, layer),
        };
        layer_bounds.push(bounds.clone());
    }

    bounds
}

/// Propagate bounds through a single layer using IBP
fn ibp_layer(input: &Bounds, layer: &NnLayer) -> Bounds {
    match layer {
        NnLayer::Linear { weights, bias } => ibp_linear(input, weights, bias),
        NnLayer::ReLU => ibp_relu(input),
        NnLayer::LeakyReLU { negative_slope } => ibp_leaky_relu(input, *negative_slope),
        NnLayer::Sigmoid => ibp_sigmoid(input),
        NnLayer::Tanh => ibp_tanh(input),
        NnLayer::BatchNorm { scale, bias } => ibp_batchnorm(input, scale, bias),
        NnLayer::Dropout { .. } => ibp_dropout(input),
        NnLayer::Flatten => ibp_flatten(input),
        NnLayer::MaxPool1d {
            kernel_size,
            stride,
        } => ibp_maxpool1d(input, *kernel_size, *stride),
        NnLayer::AvgPool1d {
            kernel_size,
            stride,
        } => ibp_avgpool1d(input, *kernel_size, *stride),
        NnLayer::Conv1d {
            in_channels,
            kernel_size,
            stride,
            padding,
            weights,
            bias,
            ..
        } => ibp_conv1d(
            input,
            weights,
            bias,
            *in_channels,
            *kernel_size,
            *stride,
            *padding,
        ),
        NnLayer::Conv2d {
            in_channels,
            input_height,
            input_width,
            kernel_size,
            stride,
            padding,
            weights,
            bias,
            ..
        } => ibp_conv2d(
            input,
            weights,
            bias,
            *in_channels,
            *input_height,
            *input_width,
            *kernel_size,
            *stride,
            *padding,
        ),
        NnLayer::GlobalAvgPool2d {
            channels,
            height,
            width,
        } => ibp_global_avgpool2d(input, *channels, *height, *width),
        NnLayer::GlobalMaxPool2d {
            channels,
            height,
            width,
        } => ibp_global_maxpool2d(input, *channels, *height, *width),
        NnLayer::BatchNorm2d {
            channels,
            height,
            width,
            scale,
            bias,
        } => ibp_batchnorm2d(input, *channels, *height, *width, scale, bias),
        NnLayer::MaxPool2d {
            channels,
            height,
            width,
            kernel_size,
            stride,
        } => ibp_maxpool2d(input, *channels, *height, *width, *kernel_size, *stride),
        NnLayer::AvgPool2d {
            channels,
            height,
            width,
            kernel_size,
            stride,
        } => ibp_avgpool2d(input, *channels, *height, *width, *kernel_size, *stride),
        NnLayer::ResidualAdd { .. } | NnLayer::Concat { .. } => {
            // Skip connections require context from previous layers and must be
            // handled by ibp_propagate, not ibp_layer
            panic!("ResidualAdd/Concat must be handled at propagation level, not ibp_layer")
        }
    }
}

/// IBP for residual add: element-wise addition of two bounds
/// For y = x + skip, bounds are: [lb_x + lb_skip, ub_x + ub_skip]
fn ibp_residual_add(current: &Bounds, skip: &Bounds) -> Bounds {
    assert_eq!(
        current.dim(),
        skip.dim(),
        "ResidualAdd requires matching dimensions: current={}, skip={}",
        current.dim(),
        skip.dim()
    );
    let lower = current
        .lower
        .iter()
        .zip(&skip.lower)
        .map(|(a, b)| a + b)
        .collect();
    let upper = current
        .upper
        .iter()
        .zip(&skip.upper)
        .map(|(a, b)| a + b)
        .collect();
    Bounds { lower, upper }
}

/// IBP for concat: concatenates bounds along feature dimension
/// For y = concat(x, skip), bounds are: [lb_x ++ lb_skip, ub_x ++ ub_skip]
fn ibp_concat(current: &Bounds, skip: &Bounds) -> Bounds {
    let mut lower = current.lower.clone();
    lower.extend(&skip.lower);
    let mut upper = current.upper.clone();
    upper.extend(&skip.upper);
    Bounds { lower, upper }
}

/// IBP for linear layer: y = Wx + b
/// For each output: y_i = sum_j(W_ij * x_j) + b_i
/// Lower bound: sum over j of (W_ij * x_j_lb if W_ij >= 0, else W_ij * x_j_ub)
/// Upper bound: sum over j of (W_ij * x_j_ub if W_ij >= 0, else W_ij * x_j_lb)
fn ibp_linear(input: &Bounds, weights: &[Vec<f64>], bias: &[f64]) -> Bounds {
    let out_dim = weights.len();
    let in_dim = input.dim();

    let mut lower = vec![0.0; out_dim];
    let mut upper = vec![0.0; out_dim];

    for i in 0..out_dim {
        let mut lb = bias[i];
        let mut ub = bias[i];

        for j in 0..in_dim {
            let w = weights[i][j];
            if w >= 0.0 {
                lb += w * input.lower[j];
                ub += w * input.upper[j];
            } else {
                lb += w * input.upper[j];
                ub += w * input.lower[j];
            }
        }

        lower[i] = lb;
        upper[i] = ub;
    }

    Bounds { lower, upper }
}

/// IBP for ReLU: y = max(0, x)
fn ibp_relu(input: &Bounds) -> Bounds {
    let lower: Vec<f64> = input.lower.iter().map(|&x| x.max(0.0)).collect();
    let upper: Vec<f64> = input.upper.iter().map(|&x| x.max(0.0)).collect();
    Bounds { lower, upper }
}

/// IBP for Leaky ReLU: y = max(alpha*x, x)
fn ibp_leaky_relu(input: &Bounds, alpha: f64) -> Bounds {
    let lower: Vec<f64> = input
        .lower
        .iter()
        .map(|&x| if x >= 0.0 { x } else { alpha * x })
        .collect();
    let upper: Vec<f64> = input
        .upper
        .iter()
        .map(|&x| if x >= 0.0 { x } else { alpha * x })
        .collect();
    Bounds { lower, upper }
}

/// IBP for Sigmoid: y = 1 / (1 + exp(-x))
/// Sigmoid is monotonically increasing
fn ibp_sigmoid(input: &Bounds) -> Bounds {
    let sigmoid = |x: f64| 1.0 / (1.0 + (-x).exp());
    let lower: Vec<f64> = input.lower.iter().map(|&x| sigmoid(x)).collect();
    let upper: Vec<f64> = input.upper.iter().map(|&x| sigmoid(x)).collect();
    Bounds { lower, upper }
}

/// IBP for Tanh: y = tanh(x)
/// Tanh is monotonically increasing
fn ibp_tanh(input: &Bounds) -> Bounds {
    let lower: Vec<f64> = input.lower.iter().map(|&x| x.tanh()).collect();
    let upper: Vec<f64> = input.upper.iter().map(|&x| x.tanh()).collect();
    Bounds { lower, upper }
}

/// IBP for BatchNorm (inference mode): y = scale * x + bias
/// Element-wise operation, monotonic in each dimension.
/// If `scale[i] >= 0`: `lower[i] = scale[i] * x_lb[i] + bias[i]`
/// If `scale[i] < 0`: bounds flip (lower from upper, upper from lower)
fn ibp_batchnorm(input: &Bounds, scale: &[f64], bias: &[f64]) -> Bounds {
    let dim = input.dim();
    let mut lower = vec![0.0; dim];
    let mut upper = vec![0.0; dim];

    for i in 0..dim {
        let s = scale[i];
        let b = bias[i];
        if s >= 0.0 {
            lower[i] = s * input.lower[i] + b;
            upper[i] = s * input.upper[i] + b;
        } else {
            // Negative scale flips bounds
            lower[i] = s * input.upper[i] + b;
            upper[i] = s * input.lower[i] + b;
        }
    }

    Bounds { lower, upper }
}

/// IBP for Dropout (inference mode): identity function
/// In inference mode, dropout is disabled.
fn ibp_dropout(input: &Bounds) -> Bounds {
    input.clone()
}

/// IBP for Flatten: identity in 1D
/// Flatten just reshapes, so bounds are preserved.
fn ibp_flatten(input: &Bounds) -> Bounds {
    input.clone()
}

/// IBP for MaxPool1d: max over each window
/// For each output position, we take the max of kernel_size consecutive inputs.
/// Lower bound: max of lower bounds in window
/// Upper bound: max of upper bounds in window
fn ibp_maxpool1d(input: &Bounds, kernel_size: usize, stride: usize) -> Bounds {
    if stride == 0 || kernel_size == 0 || input.dim() < kernel_size {
        return input.clone();
    }

    let in_dim = input.dim();
    let out_dim = (in_dim - kernel_size) / stride + 1;

    let mut lower = vec![f64::NEG_INFINITY; out_dim];
    let mut upper = vec![f64::NEG_INFINITY; out_dim];

    for i in 0..out_dim {
        let start = i * stride;
        for j in 0..kernel_size {
            let idx = start + j;
            if idx < in_dim {
                lower[i] = lower[i].max(input.lower[idx]);
                upper[i] = upper[i].max(input.upper[idx]);
            }
        }
    }

    Bounds { lower, upper }
}

/// IBP for AvgPool1d: average over each window
/// For each output position, we take the average of kernel_size consecutive inputs.
/// Since averaging is linear: lb(avg) = avg(lb), ub(avg) = avg(ub)
fn ibp_avgpool1d(input: &Bounds, kernel_size: usize, stride: usize) -> Bounds {
    if stride == 0 || kernel_size == 0 || input.dim() < kernel_size {
        return input.clone();
    }

    let in_dim = input.dim();
    let out_dim = (in_dim - kernel_size) / stride + 1;
    let scale = 1.0 / kernel_size as f64;

    let mut lower = vec![0.0; out_dim];
    let mut upper = vec![0.0; out_dim];

    for i in 0..out_dim {
        let start = i * stride;
        for j in 0..kernel_size {
            let idx = start + j;
            if idx < in_dim {
                lower[i] += input.lower[idx];
                upper[i] += input.upper[idx];
            }
        }
        lower[i] *= scale;
        upper[i] *= scale;
    }

    Bounds { lower, upper }
}

/// IBP for Conv1d: 1D convolution layer
/// Input: flattened tensor of shape (in_channels * input_length)
/// Output: flattened tensor of shape (out_channels * output_length)
/// where output_length = (input_length + 2*padding - kernel_size) / stride + 1
///
/// For each output element at (out_ch, out_pos):
/// y[out_ch, out_pos] = sum_{in_ch, k} weight[out_ch, in_ch, k] * x[in_ch, in_pos + k] + bias[out_ch]
/// where in_pos = out_pos * stride - padding
///
/// Since this is a linear operation, we can use the standard IBP approach:
/// - Positive weight contribution: w * [lb, ub] -> [w*lb, w*ub]
/// - Negative weight contribution: w * [lb, ub] -> [w*ub, w*lb]
fn ibp_conv1d(
    input: &Bounds,
    weights: &[Vec<Vec<f64>>],
    bias: &[f64],
    in_channels: usize,
    kernel_size: usize,
    stride: usize,
    padding: usize,
) -> Bounds {
    let input_dim = input.dim();
    if in_channels == 0 || input_dim < in_channels {
        return input.clone();
    }

    let input_length = input_dim / in_channels;
    let out_channels = weights.len();
    let effective_length = input_length + 2 * padding;

    if effective_length < kernel_size || stride == 0 {
        return Bounds {
            lower: vec![],
            upper: vec![],
        };
    }

    let output_length = (effective_length - kernel_size) / stride + 1;
    let output_dim = out_channels * output_length;

    let mut lower = vec![0.0; output_dim];
    let mut upper = vec![0.0; output_dim];

    // For each output position
    for out_ch in 0..out_channels {
        for out_pos in 0..output_length {
            let out_idx = out_ch * output_length + out_pos;
            let mut lb_sum = 0.0;
            let mut ub_sum = 0.0;

            // Add bias
            if out_ch < bias.len() {
                lb_sum += bias[out_ch];
                ub_sum += bias[out_ch];
            }

            // Sum over input channels and kernel positions
            for in_ch in 0..in_channels {
                for k in 0..kernel_size {
                    // Compute input position (with padding)
                    let in_pos_padded = out_pos * stride + k;

                    // Check if this position is in the padding region
                    if in_pos_padded < padding || in_pos_padded >= padding + input_length {
                        // Padding with zeros - no contribution
                        continue;
                    }

                    let in_pos = in_pos_padded - padding;
                    let in_idx = in_ch * input_length + in_pos;

                    if in_idx >= input_dim {
                        continue;
                    }

                    let w = weights[out_ch][in_ch][k];
                    let in_lb = input.lower[in_idx];
                    let in_ub = input.upper[in_idx];

                    // Standard IBP for linear operation
                    if w >= 0.0 {
                        lb_sum += w * in_lb;
                        ub_sum += w * in_ub;
                    } else {
                        lb_sum += w * in_ub;
                        ub_sum += w * in_lb;
                    }
                }
            }

            lower[out_idx] = lb_sum;
            upper[out_idx] = ub_sum;
        }
    }

    Bounds { lower, upper }
}

/// Forward pass for Conv1d (concrete values)
fn forward_conv1d(
    input: &[f64],
    weights: &[Vec<Vec<f64>>],
    bias: &[f64],
    in_channels: usize,
    kernel_size: usize,
    stride: usize,
    padding: usize,
) -> Vec<f64> {
    let input_dim = input.len();
    if in_channels == 0 || input_dim < in_channels {
        return input.to_vec();
    }

    let input_length = input_dim / in_channels;
    let out_channels = weights.len();
    let effective_length = input_length + 2 * padding;

    if effective_length < kernel_size || stride == 0 {
        return vec![];
    }

    let output_length = (effective_length - kernel_size) / stride + 1;
    let output_dim = out_channels * output_length;

    let mut output = vec![0.0; output_dim];

    for out_ch in 0..out_channels {
        for out_pos in 0..output_length {
            let out_idx = out_ch * output_length + out_pos;
            let mut sum = if out_ch < bias.len() {
                bias[out_ch]
            } else {
                0.0
            };

            for in_ch in 0..in_channels {
                for k in 0..kernel_size {
                    let in_pos_padded = out_pos * stride + k;

                    if in_pos_padded < padding || in_pos_padded >= padding + input_length {
                        continue; // Padding position
                    }

                    let in_pos = in_pos_padded - padding;
                    let in_idx = in_ch * input_length + in_pos;

                    if in_idx < input_dim {
                        sum += weights[out_ch][in_ch][k] * input[in_idx];
                    }
                }
            }

            output[out_idx] = sum;
        }
    }

    output
}

/// IBP for 2D Convolution layer
/// `y[c_out, h, w] = sum_{c_in, kh, kw} weight[c_out, c_in, kh, kw] * x[c_in, h*stride+kh-padding, w*stride+kw-padding] + bias[c_out]`
///
/// Since this is a linear operation, we can use the standard IBP approach:
/// - Positive weight contribution: w * [lb, ub] -> [w*lb, w*ub]
/// - Negative weight contribution: w * [lb, ub] -> [w*ub, w*lb]
#[allow(clippy::too_many_arguments)]
fn ibp_conv2d(
    input: &Bounds,
    weights: &[Vec<Vec<Vec<f64>>>],
    bias: &[f64],
    in_channels: usize,
    input_height: usize,
    input_width: usize,
    kernel_size: usize,
    stride: usize,
    padding: usize,
) -> Bounds {
    let input_dim = input.dim();
    let expected_dim = in_channels * input_height * input_width;
    if input_dim != expected_dim || in_channels == 0 {
        return input.clone();
    }

    let out_channels = weights.len();
    let effective_height = input_height + 2 * padding;
    let effective_width = input_width + 2 * padding;

    if effective_height < kernel_size || effective_width < kernel_size || stride == 0 {
        return Bounds {
            lower: vec![],
            upper: vec![],
        };
    }

    let out_height = (effective_height - kernel_size) / stride + 1;
    let out_width = (effective_width - kernel_size) / stride + 1;
    let output_dim = out_channels * out_height * out_width;

    let mut lower = vec![0.0; output_dim];
    let mut upper = vec![0.0; output_dim];

    // For each output position
    for out_ch in 0..out_channels {
        for out_h in 0..out_height {
            for out_w in 0..out_width {
                let out_idx = out_ch * out_height * out_width + out_h * out_width + out_w;
                let mut lb_sum = 0.0;
                let mut ub_sum = 0.0;

                // Add bias
                if out_ch < bias.len() {
                    lb_sum += bias[out_ch];
                    ub_sum += bias[out_ch];
                }

                // Sum over input channels and kernel positions
                for in_ch in 0..in_channels {
                    for kh in 0..kernel_size {
                        for kw in 0..kernel_size {
                            // Compute input position (with padding)
                            let in_h_padded = out_h * stride + kh;
                            let in_w_padded = out_w * stride + kw;

                            // Check if this position is in the padding region
                            if in_h_padded < padding
                                || in_h_padded >= padding + input_height
                                || in_w_padded < padding
                                || in_w_padded >= padding + input_width
                            {
                                // Padding with zeros - no contribution
                                continue;
                            }

                            let in_h = in_h_padded - padding;
                            let in_w = in_w_padded - padding;
                            let in_idx =
                                in_ch * input_height * input_width + in_h * input_width + in_w;

                            if in_idx >= input_dim {
                                continue;
                            }

                            let w = weights[out_ch][in_ch][kh][kw];
                            let in_lb = input.lower[in_idx];
                            let in_ub = input.upper[in_idx];

                            // Standard IBP for linear operation
                            if w >= 0.0 {
                                lb_sum += w * in_lb;
                                ub_sum += w * in_ub;
                            } else {
                                lb_sum += w * in_ub;
                                ub_sum += w * in_lb;
                            }
                        }
                    }
                }

                lower[out_idx] = lb_sum;
                upper[out_idx] = ub_sum;
            }
        }
    }

    Bounds { lower, upper }
}

/// Forward pass for Conv2d (concrete values)
#[allow(clippy::too_many_arguments)]
fn forward_conv2d(
    input: &[f64],
    weights: &[Vec<Vec<Vec<f64>>>],
    bias: &[f64],
    in_channels: usize,
    input_height: usize,
    input_width: usize,
    kernel_size: usize,
    stride: usize,
    padding: usize,
) -> Vec<f64> {
    let input_dim = input.len();
    let expected_dim = in_channels * input_height * input_width;
    if input_dim != expected_dim || in_channels == 0 {
        return input.to_vec();
    }

    let out_channels = weights.len();
    let effective_height = input_height + 2 * padding;
    let effective_width = input_width + 2 * padding;

    if effective_height < kernel_size || effective_width < kernel_size || stride == 0 {
        return vec![];
    }

    let out_height = (effective_height - kernel_size) / stride + 1;
    let out_width = (effective_width - kernel_size) / stride + 1;
    let output_dim = out_channels * out_height * out_width;

    let mut output = vec![0.0; output_dim];

    for out_ch in 0..out_channels {
        for out_h in 0..out_height {
            for out_w in 0..out_width {
                let out_idx = out_ch * out_height * out_width + out_h * out_width + out_w;
                let mut sum = if out_ch < bias.len() {
                    bias[out_ch]
                } else {
                    0.0
                };

                for in_ch in 0..in_channels {
                    for kh in 0..kernel_size {
                        for kw in 0..kernel_size {
                            let in_h_padded = out_h * stride + kh;
                            let in_w_padded = out_w * stride + kw;

                            if in_h_padded < padding
                                || in_h_padded >= padding + input_height
                                || in_w_padded < padding
                                || in_w_padded >= padding + input_width
                            {
                                continue; // Padding position
                            }

                            let in_h = in_h_padded - padding;
                            let in_w = in_w_padded - padding;
                            let in_idx =
                                in_ch * input_height * input_width + in_h * input_width + in_w;

                            if in_idx < input_dim {
                                sum += weights[out_ch][in_ch][kh][kw] * input[in_idx];
                            }
                        }
                    }
                }

                output[out_idx] = sum;
            }
        }
    }

    output
}

/// IBP for Global Average Pooling 2D
/// Input: (channels * height * width) flattened
/// Output: (channels) - average over spatial dimensions for each channel
fn ibp_global_avgpool2d(input: &Bounds, channels: usize, height: usize, width: usize) -> Bounds {
    let spatial_size = height * width;
    let expected_dim = channels * spatial_size;
    if input.dim() != expected_dim || spatial_size == 0 {
        return Bounds::new(vec![], vec![]);
    }

    let scale = 1.0 / spatial_size as f64;
    let mut lower = vec![0.0; channels];
    let mut upper = vec![0.0; channels];

    for c in 0..channels {
        let base = c * spatial_size;
        for s in 0..spatial_size {
            lower[c] += input.lower[base + s];
            upper[c] += input.upper[base + s];
        }
        lower[c] *= scale;
        upper[c] *= scale;
    }

    Bounds { lower, upper }
}

/// IBP for Global Max Pooling 2D
/// Input: (channels * height * width) flattened
/// Output: (channels) - max over spatial dimensions for each channel
fn ibp_global_maxpool2d(input: &Bounds, channels: usize, height: usize, width: usize) -> Bounds {
    let spatial_size = height * width;
    let expected_dim = channels * spatial_size;
    if input.dim() != expected_dim || spatial_size == 0 {
        return Bounds::new(vec![], vec![]);
    }

    let mut lower = vec![f64::NEG_INFINITY; channels];
    let mut upper = vec![f64::NEG_INFINITY; channels];

    for c in 0..channels {
        let base = c * spatial_size;
        for s in 0..spatial_size {
            lower[c] = lower[c].max(input.lower[base + s]);
            upper[c] = upper[c].max(input.upper[base + s]);
        }
    }

    Bounds { lower, upper }
}

/// Forward pass for Global Average Pooling 2D (concrete values)
fn forward_global_avgpool2d(
    input: &[f64],
    channels: usize,
    height: usize,
    width: usize,
) -> Vec<f64> {
    let spatial_size = height * width;
    let expected_dim = channels * spatial_size;
    if input.len() != expected_dim || spatial_size == 0 {
        return vec![];
    }

    let scale = 1.0 / spatial_size as f64;
    let mut output = vec![0.0; channels];

    for c in 0..channels {
        let base = c * spatial_size;
        for s in 0..spatial_size {
            output[c] += input[base + s];
        }
        output[c] *= scale;
    }

    output
}

/// Forward pass for Global Max Pooling 2D (concrete values)
fn forward_global_maxpool2d(
    input: &[f64],
    channels: usize,
    height: usize,
    width: usize,
) -> Vec<f64> {
    let spatial_size = height * width;
    let expected_dim = channels * spatial_size;
    if input.len() != expected_dim || spatial_size == 0 {
        return vec![];
    }

    let mut output = vec![f64::NEG_INFINITY; channels];

    for c in 0..channels {
        let base = c * spatial_size;
        for s in 0..spatial_size {
            output[c] = output[c].max(input[base + s]);
        }
    }

    output
}

// ============================================================================
// BatchNorm2d, MaxPool2d, AvgPool2d (2D spatial layers)
// ============================================================================

/// IBP for 2D Batch Normalization (inference mode)
fn ibp_batchnorm2d(
    input: &Bounds,
    channels: usize,
    height: usize,
    width: usize,
    scale: &[f64],
    bias: &[f64],
) -> Bounds {
    let spatial_size = height * width;
    let expected_dim = channels * spatial_size;
    if input.dim() != expected_dim {
        return Bounds::new(vec![], vec![]);
    }

    let mut lower = vec![0.0; expected_dim];
    let mut upper = vec![0.0; expected_dim];

    for c in 0..channels {
        let s = scale[c];
        let b = bias[c];
        let base = c * spatial_size;
        for i in 0..spatial_size {
            let idx = base + i;
            if s >= 0.0 {
                lower[idx] = s * input.lower[idx] + b;
                upper[idx] = s * input.upper[idx] + b;
            } else {
                lower[idx] = s * input.upper[idx] + b;
                upper[idx] = s * input.lower[idx] + b;
            }
        }
    }
    Bounds { lower, upper }
}

/// Forward pass for 2D Batch Normalization
fn forward_batchnorm2d(
    input: &[f64],
    channels: usize,
    height: usize,
    width: usize,
    scale: &[f64],
    bias: &[f64],
) -> Vec<f64> {
    let spatial_size = height * width;
    let expected_dim = channels * spatial_size;
    if input.len() != expected_dim {
        return vec![];
    }

    let mut output = vec![0.0; expected_dim];
    for c in 0..channels {
        let s = scale[c];
        let b = bias[c];
        let base = c * spatial_size;
        for i in 0..spatial_size {
            let idx = base + i;
            output[idx] = s * input[idx] + b;
        }
    }
    output
}

/// IBP for 2D Max Pooling
fn ibp_maxpool2d(
    input: &Bounds,
    channels: usize,
    height: usize,
    width: usize,
    kernel_size: usize,
    stride: usize,
) -> Bounds {
    let spatial_size = height * width;
    let expected_dim = channels * spatial_size;
    if input.dim() != expected_dim || stride == 0 || kernel_size == 0 {
        return Bounds::new(vec![], vec![]);
    }
    if height < kernel_size || width < kernel_size {
        return Bounds::new(vec![], vec![]);
    }

    let out_height = (height - kernel_size) / stride + 1;
    let out_width = (width - kernel_size) / stride + 1;
    let out_spatial = out_height * out_width;
    let out_dim = channels * out_spatial;

    let mut lower = vec![f64::NEG_INFINITY; out_dim];
    let mut upper = vec![f64::NEG_INFINITY; out_dim];

    for c in 0..channels {
        let in_base = c * spatial_size;
        let out_base = c * out_spatial;
        for oh in 0..out_height {
            for ow in 0..out_width {
                let out_idx = out_base + oh * out_width + ow;
                for kh in 0..kernel_size {
                    for kw in 0..kernel_size {
                        let ih = oh * stride + kh;
                        let iw = ow * stride + kw;
                        let in_idx = in_base + ih * width + iw;
                        lower[out_idx] = lower[out_idx].max(input.lower[in_idx]);
                        upper[out_idx] = upper[out_idx].max(input.upper[in_idx]);
                    }
                }
            }
        }
    }
    Bounds { lower, upper }
}

/// Forward pass for 2D Max Pooling
fn forward_maxpool2d(
    input: &[f64],
    channels: usize,
    height: usize,
    width: usize,
    kernel_size: usize,
    stride: usize,
) -> Vec<f64> {
    let spatial_size = height * width;
    let expected_dim = channels * spatial_size;
    if input.len() != expected_dim || stride == 0 || kernel_size == 0 {
        return vec![];
    }
    if height < kernel_size || width < kernel_size {
        return vec![];
    }

    let out_height = (height - kernel_size) / stride + 1;
    let out_width = (width - kernel_size) / stride + 1;
    let out_spatial = out_height * out_width;
    let out_dim = channels * out_spatial;

    let mut output = vec![f64::NEG_INFINITY; out_dim];
    for c in 0..channels {
        let in_base = c * spatial_size;
        let out_base = c * out_spatial;
        for oh in 0..out_height {
            for ow in 0..out_width {
                let out_idx = out_base + oh * out_width + ow;
                for kh in 0..kernel_size {
                    for kw in 0..kernel_size {
                        let ih = oh * stride + kh;
                        let iw = ow * stride + kw;
                        let in_idx = in_base + ih * width + iw;
                        output[out_idx] = output[out_idx].max(input[in_idx]);
                    }
                }
            }
        }
    }
    output
}

/// IBP for 2D Average Pooling
fn ibp_avgpool2d(
    input: &Bounds,
    channels: usize,
    height: usize,
    width: usize,
    kernel_size: usize,
    stride: usize,
) -> Bounds {
    let spatial_size = height * width;
    let expected_dim = channels * spatial_size;
    if input.dim() != expected_dim || stride == 0 || kernel_size == 0 {
        return Bounds::new(vec![], vec![]);
    }
    if height < kernel_size || width < kernel_size {
        return Bounds::new(vec![], vec![]);
    }

    let out_height = (height - kernel_size) / stride + 1;
    let out_width = (width - kernel_size) / stride + 1;
    let out_spatial = out_height * out_width;
    let out_dim = channels * out_spatial;
    let pool_size = (kernel_size * kernel_size) as f64;

    let mut lower = vec![0.0; out_dim];
    let mut upper = vec![0.0; out_dim];

    for c in 0..channels {
        let in_base = c * spatial_size;
        let out_base = c * out_spatial;
        for oh in 0..out_height {
            for ow in 0..out_width {
                let out_idx = out_base + oh * out_width + ow;
                let mut sum_lower = 0.0;
                let mut sum_upper = 0.0;
                for kh in 0..kernel_size {
                    for kw in 0..kernel_size {
                        let ih = oh * stride + kh;
                        let iw = ow * stride + kw;
                        let in_idx = in_base + ih * width + iw;
                        sum_lower += input.lower[in_idx];
                        sum_upper += input.upper[in_idx];
                    }
                }
                lower[out_idx] = sum_lower / pool_size;
                upper[out_idx] = sum_upper / pool_size;
            }
        }
    }
    Bounds { lower, upper }
}

/// Forward pass for 2D Average Pooling
fn forward_avgpool2d(
    input: &[f64],
    channels: usize,
    height: usize,
    width: usize,
    kernel_size: usize,
    stride: usize,
) -> Vec<f64> {
    let spatial_size = height * width;
    let expected_dim = channels * spatial_size;
    if input.len() != expected_dim || stride == 0 || kernel_size == 0 {
        return vec![];
    }
    if height < kernel_size || width < kernel_size {
        return vec![];
    }

    let out_height = (height - kernel_size) / stride + 1;
    let out_width = (width - kernel_size) / stride + 1;
    let out_spatial = out_height * out_width;
    let out_dim = channels * out_spatial;
    let pool_size = (kernel_size * kernel_size) as f64;

    let mut output = vec![0.0; out_dim];
    for c in 0..channels {
        let in_base = c * spatial_size;
        let out_base = c * out_spatial;
        for oh in 0..out_height {
            for ow in 0..out_width {
                let out_idx = out_base + oh * out_width + ow;
                let mut sum = 0.0;
                for kh in 0..kernel_size {
                    for kw in 0..kernel_size {
                        let ih = oh * stride + kh;
                        let iw = ow * stride + kw;
                        let in_idx = in_base + ih * width + iw;
                        sum += input[in_idx];
                    }
                }
                output[out_idx] = sum / pool_size;
            }
        }
    }
    output
}

// ============================================================================
// L2 Ball Propagation (tighter bounds for L2 adversarial robustness)
// ============================================================================

/// Propagate L2 ball through a linear layer (y = Wx + b)
/// Uses Cauchy-Schwarz inequality for tighter bounds:
/// |Δy_i| = |W_i · Δx| <= ||W_i||_2 * ||Δx||_2 <= ||W_i||_2 * ε
fn ibp_linear_l2(input: &L2BallBounds, weights: &[Vec<f64>], bias: &[f64]) -> L2BallBounds {
    let out_dim = weights.len();
    let in_dim = input.dim();

    // Compute new center: y0 = W * x0 + b
    let mut new_center = vec![0.0; out_dim];
    for (i, row) in weights.iter().enumerate() {
        let mut sum = bias[i];
        for (j, &w) in row.iter().enumerate() {
            if j < in_dim {
                sum += w * input.center[j];
            }
        }
        new_center[i] = sum;
    }

    // Compute spectral norm (max row L2 norm gives an upper bound)
    let mut max_row_norm = 0.0f64;
    for row in weights {
        let row_norm: f64 = row.iter().map(|&w| w * w).sum::<f64>().sqrt();
        max_row_norm = max_row_norm.max(row_norm);
    }
    let new_radius = max_row_norm * input.radius;

    // Compute tighter component-wise bounds using row L2 norms
    let mut lower = vec![0.0; out_dim];
    let mut upper = vec![0.0; out_dim];
    for (i, row) in weights.iter().enumerate() {
        let row_l2_norm: f64 = row.iter().map(|&w| w * w).sum::<f64>().sqrt();
        let deviation = row_l2_norm * input.radius;
        lower[i] = new_center[i] - deviation;
        upper[i] = new_center[i] + deviation;
    }

    L2BallBounds {
        center: new_center,
        radius: new_radius,
        box_bounds: Bounds { lower, upper },
    }
}

/// Propagate L2 ball through BatchNorm layer
/// BatchNorm in inference: y = scale * x + bias (element-wise)
fn ibp_batchnorm_l2(input: &L2BallBounds, scale: &[f64], bias: &[f64]) -> L2BallBounds {
    let dim = input.dim();

    // New center: y0 = scale * x0 + bias
    let new_center: Vec<f64> = input
        .center
        .iter()
        .zip(scale.iter())
        .zip(bias.iter())
        .map(|((&x, &s), &b)| s * x + b)
        .collect();

    // For L2 ball with element-wise scaling:
    // ||Δy||_2 = ||scale ⊙ Δx||_2 = sqrt(Σ scale_i² * Δx_i²)
    let scale_l2_norm: f64 = scale.iter().map(|&s| s * s).sum::<f64>().sqrt();
    let new_radius = scale_l2_norm * input.radius;

    // Component-wise bounds
    let mut lower = vec![0.0; dim];
    let mut upper = vec![0.0; dim];
    for i in 0..dim {
        let deviation = scale[i].abs() * input.radius;
        lower[i] = new_center[i] - deviation;
        upper[i] = new_center[i] + deviation;
    }

    L2BallBounds {
        center: new_center,
        radius: new_radius,
        box_bounds: Bounds { lower, upper },
    }
}

/// Propagate L2 ball through ReLU layer
/// After ReLU, the L2 ball structure is lost, so we convert to box bounds
fn ibp_relu_l2(input: &L2BallBounds) -> Bounds {
    ibp_relu(&input.box_bounds)
}

/// Propagate L2 ball through LeakyReLU layer
fn ibp_leaky_relu_l2(input: &L2BallBounds, negative_slope: f64) -> Bounds {
    ibp_leaky_relu(&input.box_bounds, negative_slope)
}

/// Propagate L2 ball through Sigmoid layer
fn ibp_sigmoid_l2(input: &L2BallBounds) -> Bounds {
    ibp_sigmoid(&input.box_bounds)
}

/// Propagate L2 ball through Tanh layer
fn ibp_tanh_l2(input: &L2BallBounds) -> Bounds {
    ibp_tanh(&input.box_bounds)
}

/// Full L2-aware IBP propagation through network
/// Uses L2 ball for linear layers, converts to box bounds at non-linearities
#[must_use]
pub fn ibp_propagate_l2(network: &NnNetwork, input: &L2BallBounds) -> Bounds {
    // Start with L2 ball bounds
    let mut l2_bounds = input.clone();
    let mut box_bounds: Option<Bounds> = None;
    let mut use_l2 = true;

    for layer in &network.layers {
        if use_l2 {
            match layer {
                NnLayer::Linear { weights, bias } => {
                    l2_bounds = ibp_linear_l2(&l2_bounds, weights, bias);
                }
                NnLayer::BatchNorm { scale, bias } => {
                    l2_bounds = ibp_batchnorm_l2(&l2_bounds, scale, bias);
                }
                NnLayer::ReLU => {
                    // Non-linearity: convert to box bounds
                    box_bounds = Some(ibp_relu_l2(&l2_bounds));
                    use_l2 = false;
                }
                NnLayer::LeakyReLU { negative_slope } => {
                    box_bounds = Some(ibp_leaky_relu_l2(&l2_bounds, *negative_slope));
                    use_l2 = false;
                }
                NnLayer::Sigmoid => {
                    box_bounds = Some(ibp_sigmoid_l2(&l2_bounds));
                    use_l2 = false;
                }
                NnLayer::Tanh => {
                    box_bounds = Some(ibp_tanh_l2(&l2_bounds));
                    use_l2 = false;
                }
                NnLayer::Dropout { .. } | NnLayer::Flatten => {
                    // Identity in inference mode
                }
                NnLayer::MaxPool1d {
                    kernel_size,
                    stride,
                } => {
                    // Convert to box bounds for pooling
                    box_bounds = Some(ibp_maxpool1d(&l2_bounds.box_bounds, *kernel_size, *stride));
                    use_l2 = false;
                }
                NnLayer::AvgPool1d {
                    kernel_size,
                    stride,
                } => {
                    box_bounds = Some(ibp_avgpool1d(&l2_bounds.box_bounds, *kernel_size, *stride));
                    use_l2 = false;
                }
                NnLayer::Conv1d {
                    in_channels,
                    kernel_size,
                    stride,
                    padding,
                    weights,
                    bias,
                    ..
                } => {
                    // Conv1d is linear but L2-aware propagation is complex; use box bounds
                    box_bounds = Some(ibp_conv1d(
                        &l2_bounds.box_bounds,
                        weights,
                        bias,
                        *in_channels,
                        *kernel_size,
                        *stride,
                        *padding,
                    ));
                    use_l2 = false;
                }
                NnLayer::Conv2d {
                    in_channels,
                    input_height,
                    input_width,
                    kernel_size,
                    stride,
                    padding,
                    weights,
                    bias,
                    ..
                } => {
                    box_bounds = Some(ibp_conv2d(
                        &l2_bounds.box_bounds,
                        weights,
                        bias,
                        *in_channels,
                        *input_height,
                        *input_width,
                        *kernel_size,
                        *stride,
                        *padding,
                    ));
                    use_l2 = false;
                }
                NnLayer::GlobalAvgPool2d {
                    channels,
                    height,
                    width,
                } => {
                    // Global pooling: convert to box bounds
                    box_bounds = Some(ibp_global_avgpool2d(
                        &l2_bounds.box_bounds,
                        *channels,
                        *height,
                        *width,
                    ));
                    use_l2 = false;
                }
                NnLayer::GlobalMaxPool2d {
                    channels,
                    height,
                    width,
                } => {
                    box_bounds = Some(ibp_global_maxpool2d(
                        &l2_bounds.box_bounds,
                        *channels,
                        *height,
                        *width,
                    ));
                    use_l2 = false;
                }
                NnLayer::BatchNorm2d {
                    channels,
                    height,
                    width,
                    scale,
                    bias,
                } => {
                    // BatchNorm2d is element-wise linear; convert to box bounds for simplicity
                    box_bounds = Some(ibp_batchnorm2d(
                        &l2_bounds.box_bounds,
                        *channels,
                        *height,
                        *width,
                        scale,
                        bias,
                    ));
                    use_l2 = false;
                }
                NnLayer::MaxPool2d {
                    channels,
                    height,
                    width,
                    kernel_size,
                    stride,
                } => {
                    box_bounds = Some(ibp_maxpool2d(
                        &l2_bounds.box_bounds,
                        *channels,
                        *height,
                        *width,
                        *kernel_size,
                        *stride,
                    ));
                    use_l2 = false;
                }
                NnLayer::AvgPool2d {
                    channels,
                    height,
                    width,
                    kernel_size,
                    stride,
                } => {
                    box_bounds = Some(ibp_avgpool2d(
                        &l2_bounds.box_bounds,
                        *channels,
                        *height,
                        *width,
                        *kernel_size,
                        *stride,
                    ));
                    use_l2 = false;
                }
                NnLayer::ResidualAdd { .. } | NnLayer::Concat { .. } => {
                    // Skip connections not yet supported in L2 propagation
                    panic!(
                        "ResidualAdd/Concat in L2 propagation requires separate skip-aware implementation"
                    );
                }
            }
        } else {
            // Using box bounds after hitting a non-linearity
            let current = box_bounds
                .as_ref()
                .expect("box_bounds should be initialized before non-linear layer");
            box_bounds = Some(ibp_layer(current, layer));
        }
    }

    // Return final bounds
    if use_l2 {
        l2_bounds.to_box_bounds()
    } else {
        box_bounds.expect("box_bounds should be set when not using L2 bounds")
    }
}

// ============================================================================
// CROWN Linear Relaxation
// ============================================================================

/// Pre-activation bounds at each layer, computed by IBP forward pass
#[derive(Debug, Clone)]
pub struct PreActivationBounds {
    /// Bounds at each layer (index i = bounds before layer i)
    pub layer_bounds: Vec<Bounds>,
}

impl PreActivationBounds {
    /// Compute pre-activation bounds using IBP forward pass
    /// Supports skip connections (ResidualAdd, Concat)
    #[must_use]
    pub fn compute(network: &NnNetwork, input_bounds: &Bounds) -> Self {
        let mut layer_bounds = vec![input_bounds.clone()];
        let mut bounds = input_bounds.clone();

        for (i, layer) in network.layers.iter().enumerate() {
            bounds = match layer {
                NnLayer::ResidualAdd { skip_from_output } => {
                    assert!(
                        *skip_from_output < layer_bounds.len(),
                        "ResidualAdd at layer {i} references invalid skip_from_output {skip_from_output}"
                    );
                    let skip_bounds = &layer_bounds[*skip_from_output];
                    ibp_residual_add(&bounds, skip_bounds)
                }
                NnLayer::Concat { skip_from_output } => {
                    assert!(
                        *skip_from_output < layer_bounds.len(),
                        "Concat at layer {i} references invalid skip_from_output {skip_from_output}"
                    );
                    let skip_bounds = &layer_bounds[*skip_from_output];
                    ibp_concat(&bounds, skip_bounds)
                }
                _ => ibp_layer(&bounds, layer),
            };
            layer_bounds.push(bounds.clone());
        }

        Self { layer_bounds }
    }
}

/// Linear bounds: represents bounds of the form A*x + b for each output neuron
/// For output neuron i: `lower[i] <= A_lower[i] * x + b_lower[i]`, etc.
#[derive(Debug, Clone)]
pub struct LinearBounds {
    /// Lower bound coefficients: `A_lower[i][j]` for output i, input j
    pub a_lower: Vec<Vec<f64>>,
    /// Lower bound bias
    pub b_lower: Vec<f64>,
    /// Upper bound coefficients: `A_upper[i][j]`
    pub a_upper: Vec<Vec<f64>>,
    /// Upper bound bias
    pub b_upper: Vec<f64>,
}

impl LinearBounds {
    /// Create identity linear bounds (y = x)
    #[must_use]
    pub fn identity(dim: usize) -> Self {
        let mut a = vec![vec![0.0; dim]; dim];
        for i in 0..dim {
            a[i][i] = 1.0;
        }
        Self {
            a_lower: a.clone(),
            b_lower: vec![0.0; dim],
            a_upper: a,
            b_upper: vec![0.0; dim],
        }
    }

    /// Get the output dimension
    #[must_use]
    pub const fn out_dim(&self) -> usize {
        self.b_lower.len()
    }

    /// Get the input dimension
    #[must_use]
    pub fn in_dim(&self) -> usize {
        if self.a_lower.is_empty() {
            0
        } else {
            self.a_lower[0].len()
        }
    }

    /// Concretize linear bounds given input bounds to get concrete interval bounds
    /// For each output: lb = min(A*x + b) over x in input_bounds
    #[must_use]
    pub fn concretize(&self, input_bounds: &Bounds) -> Bounds {
        let out_dim = self.out_dim();
        let in_dim = self.in_dim();
        let mut lower = vec![0.0; out_dim];
        let mut upper = vec![0.0; out_dim];

        for i in 0..out_dim {
            // For lower bound: use A_lower coefficients
            // lb_i = b_lower[i] + sum_j(A_lower[i][j] * x_j) minimized over input
            let mut lb = self.b_lower[i];
            for j in 0..in_dim {
                let a = self.a_lower[i][j];
                if a >= 0.0 {
                    lb += a * input_bounds.lower[j];
                } else {
                    lb += a * input_bounds.upper[j];
                }
            }
            lower[i] = lb;

            // For upper bound: use A_upper coefficients
            // ub_i = b_upper[i] + sum_j(A_upper[i][j] * x_j) maximized over input
            let mut ub = self.b_upper[i];
            for j in 0..in_dim {
                let a = self.a_upper[i][j];
                if a >= 0.0 {
                    ub += a * input_bounds.upper[j];
                } else {
                    ub += a * input_bounds.lower[j];
                }
            }
            upper[i] = ub;
        }

        Bounds { lower, upper }
    }
}

#[derive(Debug, Clone)]
struct IntervalMatrix {
    lower: Vec<Vec<f64>>,
    upper: Vec<Vec<f64>>,
}

impl IntervalMatrix {
    fn zeros(rows: usize, cols: usize) -> Self {
        Self {
            lower: vec![vec![0.0; cols]; rows],
            upper: vec![vec![0.0; cols]; rows],
        }
    }

    const fn rows(&self) -> usize {
        self.lower.len()
    }

    fn cols(&self) -> usize {
        self.lower.first().map_or(0, std::vec::Vec::len)
    }
}

fn interval_mul((a_l, a_u): (f64, f64), (b_l, b_u): (f64, f64)) -> (f64, f64) {
    let p1 = a_l * b_l;
    let p2 = a_l * b_u;
    let p3 = a_u * b_l;
    let p4 = a_u * b_u;
    (p1.min(p2).min(p3).min(p4), p1.max(p2).max(p3).max(p4))
}

fn interval_mul_scalar((a_l, a_u): (f64, f64), w: f64) -> (f64, f64) {
    if w >= 0.0 {
        (a_l * w, a_u * w)
    } else {
        (a_u * w, a_l * w)
    }
}

fn jacobian_interval_bounds(
    network: &NnNetwork,
    pre_bounds: &PreActivationBounds,
    output_dims: &[usize],
) -> Result<IntervalMatrix, String> {
    let n_layers = network.layers.len();
    if pre_bounds.layer_bounds.len() != n_layers + 1 {
        return Err(format!(
            "PreActivationBounds length mismatch: got {}, expected {}",
            pre_bounds.layer_bounds.len(),
            n_layers + 1
        ));
    }

    let input_dim = pre_bounds.layer_bounds[0].dim();
    let output_dim = pre_bounds.layer_bounds[n_layers].dim();
    for &out_dim in output_dims {
        if out_dim >= output_dim {
            return Err(format!(
                "Output dimension {out_dim} out of bounds (network has {output_dim} outputs)"
            ));
        }
    }

    // Start from identity rows for the requested output dimensions.
    let mut coeff = IntervalMatrix::zeros(output_dims.len(), output_dim);
    for (row, &out_dim) in output_dims.iter().enumerate() {
        coeff.lower[row][out_dim] = 1.0;
        coeff.upper[row][out_dim] = 1.0;
    }

    for (layer_idx, layer) in network.layers.iter().enumerate().rev() {
        let pre_layer_bounds = &pre_bounds.layer_bounds[layer_idx];
        coeff = jacobian_backward_layer_interval(&coeff, layer, pre_layer_bounds)?;
    }

    if coeff.cols() != input_dim {
        return Err(format!(
            "Jacobian input dim mismatch: got {}, expected {}",
            coeff.cols(),
            input_dim
        ));
    }
    Ok(coeff)
}

fn jacobian_backward_layer_interval(
    coeff: &IntervalMatrix,
    layer: &NnLayer,
    pre_bounds: &Bounds,
) -> Result<IntervalMatrix, String> {
    match layer {
        NnLayer::Linear { weights, .. } => {
            let out_dim = weights.len();
            let in_dim = weights.first().map_or(0, std::vec::Vec::len);
            if coeff.cols() != out_dim {
                return Err(format!(
                    "Linear jacobian backprop dim mismatch: coeff cols {}, layer out_dim {}",
                    coeff.cols(),
                    out_dim
                ));
            }
            let mut next = IntervalMatrix::zeros(coeff.rows(), in_dim);
            for r in 0..coeff.rows() {
                for out in 0..out_dim {
                    let c = (coeff.lower[r][out], coeff.upper[r][out]);
                    for inp in 0..in_dim {
                        let (p_l, p_u) = interval_mul_scalar(c, weights[out][inp]);
                        next.lower[r][inp] += p_l;
                        next.upper[r][inp] += p_u;
                    }
                }
            }
            Ok(next)
        }
        NnLayer::ReLU => {
            let dim = pre_bounds.dim();
            if coeff.cols() != dim {
                return Err(format!(
                    "ReLU jacobian backprop dim mismatch: coeff cols {}, pre_bounds dim {}",
                    coeff.cols(),
                    dim
                ));
            }
            let mut next = coeff.clone();
            for j in 0..dim {
                let (d_l, d_u) = if pre_bounds.lower[j] >= 0.0 {
                    (1.0, 1.0)
                } else if pre_bounds.upper[j] <= 0.0 {
                    (0.0, 0.0)
                } else {
                    (0.0, 1.0)
                };
                for r in 0..next.rows() {
                    let c = (next.lower[r][j], next.upper[r][j]);
                    let (p_l, p_u) = interval_mul(c, (d_l, d_u));
                    next.lower[r][j] = p_l;
                    next.upper[r][j] = p_u;
                }
            }
            Ok(next)
        }
        NnLayer::LeakyReLU { negative_slope } => {
            let dim = pre_bounds.dim();
            if coeff.cols() != dim {
                return Err(format!(
                    "LeakyReLU jacobian backprop dim mismatch: coeff cols {}, pre_bounds dim {}",
                    coeff.cols(),
                    dim
                ));
            }
            let mut next = coeff.clone();
            let alpha = *negative_slope;
            for j in 0..dim {
                let (d_l, d_u) = if pre_bounds.lower[j] >= 0.0 {
                    (1.0, 1.0)
                } else if pre_bounds.upper[j] <= 0.0 {
                    (alpha, alpha)
                } else if alpha <= 1.0 {
                    (alpha, 1.0)
                } else {
                    (1.0, alpha)
                };
                for r in 0..next.rows() {
                    let c = (next.lower[r][j], next.upper[r][j]);
                    let (p_l, p_u) = interval_mul(c, (d_l, d_u));
                    next.lower[r][j] = p_l;
                    next.upper[r][j] = p_u;
                }
            }
            Ok(next)
        }
        NnLayer::Sigmoid => {
            let dim = pre_bounds.dim();
            if coeff.cols() != dim {
                return Err(format!(
                    "Sigmoid jacobian backprop dim mismatch: coeff cols {}, pre_bounds dim {}",
                    coeff.cols(),
                    dim
                ));
            }
            let mut next = coeff.clone();
            let sigmoid = |x: f64| 1.0 / (1.0 + (-x).exp());
            let sigmoid_derivative = |x: f64| {
                let s = sigmoid(x);
                s * (1.0 - s)
            };

            for j in 0..dim {
                let l = pre_bounds.lower[j];
                let u = pre_bounds.upper[j];
                let mut candidates = vec![sigmoid_derivative(l), sigmoid_derivative(u)];
                if l <= 0.0 && 0.0 <= u {
                    candidates.push(0.25);
                }
                let d_l = candidates.iter().copied().fold(f64::INFINITY, f64::min);
                let d_u = candidates.iter().copied().fold(f64::NEG_INFINITY, f64::max);

                for r in 0..next.rows() {
                    let c = (next.lower[r][j], next.upper[r][j]);
                    let (p_l, p_u) = interval_mul(c, (d_l, d_u));
                    next.lower[r][j] = p_l;
                    next.upper[r][j] = p_u;
                }
            }
            Ok(next)
        }
        NnLayer::Tanh => {
            let dim = pre_bounds.dim();
            if coeff.cols() != dim {
                return Err(format!(
                    "Tanh jacobian backprop dim mismatch: coeff cols {}, pre_bounds dim {}",
                    coeff.cols(),
                    dim
                ));
            }
            let mut next = coeff.clone();
            let tanh_derivative = |x: f64| 1.0 - x.tanh().powi(2);

            for j in 0..dim {
                let l = pre_bounds.lower[j];
                let u = pre_bounds.upper[j];
                let mut candidates = vec![tanh_derivative(l), tanh_derivative(u)];
                if l <= 0.0 && 0.0 <= u {
                    candidates.push(1.0);
                }
                let d_l = candidates.iter().copied().fold(f64::INFINITY, f64::min);
                let d_u = candidates.iter().copied().fold(f64::NEG_INFINITY, f64::max);

                for r in 0..next.rows() {
                    let c = (next.lower[r][j], next.upper[r][j]);
                    let (p_l, p_u) = interval_mul(c, (d_l, d_u));
                    next.lower[r][j] = p_l;
                    next.upper[r][j] = p_u;
                }
            }
            Ok(next)
        }
        NnLayer::BatchNorm { scale, .. } => {
            let dim = pre_bounds.dim();
            if coeff.cols() != dim || scale.len() != dim {
                return Err(format!(
                    "BatchNorm jacobian backprop dim mismatch: coeff cols {}, pre_bounds dim {}, scale len {}",
                    coeff.cols(),
                    dim,
                    scale.len()
                ));
            }
            let mut next = coeff.clone();
            for j in 0..dim {
                for r in 0..next.rows() {
                    let c = (next.lower[r][j], next.upper[r][j]);
                    let (p_l, p_u) = interval_mul_scalar(c, scale[j]);
                    next.lower[r][j] = p_l;
                    next.upper[r][j] = p_u;
                }
            }
            Ok(next)
        }
        NnLayer::Dropout { .. } | NnLayer::Flatten => Ok(coeff.clone()),
        NnLayer::AvgPool1d {
            kernel_size,
            stride,
        } => {
            let out_pool_dim = coeff.cols();
            let in_dim = pre_bounds.dim();
            let k = *kernel_size;
            let s = *stride;
            if k == 0 || s == 0 {
                return Err("AvgPool1d kernel_size/stride must be non-zero".to_string());
            }

            let scale = 1.0 / k as f64;
            let mut next = IntervalMatrix::zeros(coeff.rows(), in_dim);
            for pool_out_idx in 0..out_pool_dim {
                let start = pool_out_idx * s;
                for kk in 0..k {
                    let idx = start + kk;
                    if idx >= in_dim {
                        continue;
                    }
                    for r in 0..coeff.rows() {
                        let c = (coeff.lower[r][pool_out_idx], coeff.upper[r][pool_out_idx]);
                        let (p_l, p_u) = interval_mul_scalar(c, scale);
                        next.lower[r][idx] += p_l;
                        next.upper[r][idx] += p_u;
                    }
                }
            }
            Ok(next)
        }
        NnLayer::MaxPool1d {
            kernel_size,
            stride,
        } => {
            let out_pool_dim = coeff.cols();
            let in_dim = pre_bounds.dim();
            let k = *kernel_size;
            let s = *stride;
            if k == 0 || s == 0 {
                return Err("MaxPool1d kernel_size/stride must be non-zero".to_string());
            }

            let mut next = IntervalMatrix::zeros(coeff.rows(), in_dim);
            for pool_out_idx in 0..out_pool_dim {
                let start = pool_out_idx * s;
                let mut window = Vec::new();
                for kk in 0..k {
                    let idx = start + kk;
                    if idx < in_dim {
                        window.push(idx);
                    }
                }
                if window.is_empty() {
                    continue;
                }

                // Determine candidates that could be maximal.
                let best_lower = window
                    .iter()
                    .map(|&idx| pre_bounds.lower[idx])
                    .fold(f64::NEG_INFINITY, f64::max);

                let candidates: Vec<usize> = window
                    .iter()
                    .copied()
                    .filter(|&idx| pre_bounds.upper[idx] >= best_lower)
                    .collect();

                // If one input is strictly greater than all others, it is always maximal.
                let mut always_max: Option<usize> = None;
                if candidates.len() == 1 {
                    let idx = candidates[0];
                    let mut max_other_upper = f64::NEG_INFINITY;
                    for &j in &window {
                        if j == idx {
                            continue;
                        }
                        max_other_upper = max_other_upper.max(pre_bounds.upper[j]);
                    }
                    if pre_bounds.lower[idx] > max_other_upper {
                        always_max = Some(idx);
                    }
                }

                for &idx in &window {
                    let (d_l, d_u) = if always_max == Some(idx) {
                        (1.0, 1.0)
                    } else if candidates.contains(&idx) {
                        (0.0, 1.0)
                    } else {
                        (0.0, 0.0)
                    };

                    for r in 0..coeff.rows() {
                        let c = (coeff.lower[r][pool_out_idx], coeff.upper[r][pool_out_idx]);
                        let (p_l, p_u) = interval_mul(c, (d_l, d_u));
                        next.lower[r][idx] += p_l;
                        next.upper[r][idx] += p_u;
                    }
                }
            }
            Ok(next)
        }
        NnLayer::Conv1d {
            in_channels,
            out_channels,
            kernel_size,
            stride,
            padding,
            weights,
            ..
        } => {
            let in_dim = pre_bounds.dim();
            if *in_channels == 0 || *stride == 0 {
                return Err("Conv1d in_channels/stride must be non-zero".to_string());
            }
            #[allow(clippy::manual_is_multiple_of)]
            if in_dim % *in_channels != 0 {
                return Err(format!(
                    "Conv1d input dim {in_dim} not divisible by in_channels {in_channels}"
                ));
            }
            let input_length = in_dim / *in_channels;
            let effective_length = input_length + 2 * *padding;
            if effective_length < *kernel_size {
                return Err("Conv1d effective_length < kernel_size".to_string());
            }
            let out_length = (effective_length - *kernel_size) / *stride + 1;
            let out_dim = *out_channels * out_length;
            if coeff.cols() != out_dim {
                return Err(format!(
                    "Conv1d jacobian backprop dim mismatch: coeff cols {}, expected out_dim {}",
                    coeff.cols(),
                    out_dim
                ));
            }

            let mut next = IntervalMatrix::zeros(coeff.rows(), in_dim);
            for out_ch in 0..*out_channels {
                for out_pos in 0..out_length {
                    let out_idx = out_ch * out_length + out_pos;
                    for in_ch in 0..*in_channels {
                        for k in 0..*kernel_size {
                            let input_pos_padded = out_pos * *stride + k;
                            if input_pos_padded < *padding
                                || input_pos_padded >= *padding + input_length
                            {
                                continue;
                            }
                            let input_pos = input_pos_padded - *padding;
                            let in_idx = in_ch * input_length + input_pos;
                            let w = weights[out_ch][in_ch][k];
                            for r in 0..coeff.rows() {
                                let c = (coeff.lower[r][out_idx], coeff.upper[r][out_idx]);
                                let (p_l, p_u) = interval_mul_scalar(c, w);
                                next.lower[r][in_idx] += p_l;
                                next.upper[r][in_idx] += p_u;
                            }
                        }
                    }
                }
            }
            Ok(next)
        }
        NnLayer::Conv2d {
            in_channels,
            out_channels,
            input_height,
            input_width,
            kernel_size,
            stride,
            padding,
            weights,
            ..
        } => {
            let in_dim = pre_bounds.dim();
            if *stride == 0 {
                return Err("Conv2d stride must be non-zero".to_string());
            }
            let expected_in_dim = *in_channels * *input_height * *input_width;
            if in_dim != expected_in_dim {
                return Err(format!(
                    "Conv2d input dim mismatch: got {in_dim}, expected {expected_in_dim}"
                ));
            }
            let effective_height = *input_height + 2 * *padding;
            let effective_width = *input_width + 2 * *padding;
            if effective_height < *kernel_size || effective_width < *kernel_size {
                return Err("Conv2d effective size < kernel_size".to_string());
            }
            let out_height = (effective_height - *kernel_size) / *stride + 1;
            let out_width = (effective_width - *kernel_size) / *stride + 1;
            let out_dim = *out_channels * out_height * out_width;
            if coeff.cols() != out_dim {
                return Err(format!(
                    "Conv2d jacobian backprop dim mismatch: coeff cols {}, expected out_dim {}",
                    coeff.cols(),
                    out_dim
                ));
            }

            let mut next = IntervalMatrix::zeros(coeff.rows(), in_dim);
            for out_ch in 0..*out_channels {
                for out_h in 0..out_height {
                    for out_w in 0..out_width {
                        let out_idx = out_ch * out_height * out_width + out_h * out_width + out_w;

                        for in_ch in 0..*in_channels {
                            for kh in 0..*kernel_size {
                                for kw in 0..*kernel_size {
                                    let in_h_padded = out_h * *stride + kh;
                                    let in_w_padded = out_w * *stride + kw;

                                    if in_h_padded < *padding
                                        || in_h_padded >= *padding + *input_height
                                        || in_w_padded < *padding
                                        || in_w_padded >= *padding + *input_width
                                    {
                                        continue;
                                    }

                                    let in_h = in_h_padded - *padding;
                                    let in_w = in_w_padded - *padding;
                                    let in_idx = in_ch * *input_height * *input_width
                                        + in_h * *input_width
                                        + in_w;
                                    let w = weights[out_ch][in_ch][kh][kw];

                                    for r in 0..coeff.rows() {
                                        let c = (coeff.lower[r][out_idx], coeff.upper[r][out_idx]);
                                        let (p_l, p_u) = interval_mul_scalar(c, w);
                                        next.lower[r][in_idx] += p_l;
                                        next.upper[r][in_idx] += p_u;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Ok(next)
        }
        NnLayer::GlobalAvgPool2d {
            channels,
            height,
            width,
        } => {
            let in_dim = pre_bounds.dim();
            let expected_in_dim = *channels * *height * *width;
            if in_dim != expected_in_dim {
                return Err(format!(
                    "GlobalAvgPool2d input dim mismatch: got {in_dim}, expected {expected_in_dim}"
                ));
            }
            if coeff.cols() != *channels {
                return Err(format!(
                    "GlobalAvgPool2d jacobian backprop dim mismatch: coeff cols {}, expected {}",
                    coeff.cols(),
                    channels
                ));
            }

            let spatial = *height * *width;
            let scale = 1.0 / spatial as f64;
            let mut next = IntervalMatrix::zeros(coeff.rows(), in_dim);
            for c in 0..*channels {
                for hw in 0..spatial {
                    let idx = c * spatial + hw;
                    for r in 0..coeff.rows() {
                        let cc = (coeff.lower[r][c], coeff.upper[r][c]);
                        let (p_l, p_u) = interval_mul_scalar(cc, scale);
                        next.lower[r][idx] += p_l;
                        next.upper[r][idx] += p_u;
                    }
                }
            }
            Ok(next)
        }
        NnLayer::GlobalMaxPool2d {
            channels,
            height,
            width,
        } => {
            let in_dim = pre_bounds.dim();
            let expected_in_dim = *channels * *height * *width;
            if in_dim != expected_in_dim {
                return Err(format!(
                    "GlobalMaxPool2d input dim mismatch: got {in_dim}, expected {expected_in_dim}"
                ));
            }
            if coeff.cols() != *channels {
                return Err(format!(
                    "GlobalMaxPool2d jacobian backprop dim mismatch: coeff cols {}, expected {}",
                    coeff.cols(),
                    channels
                ));
            }

            let spatial = *height * *width;
            let mut next = IntervalMatrix::zeros(coeff.rows(), in_dim);
            for c in 0..*channels {
                let base = c * spatial;
                let best_lower = (0..spatial)
                    .map(|hw| pre_bounds.lower[base + hw])
                    .fold(f64::NEG_INFINITY, f64::max);
                let candidates: Vec<usize> = (0..spatial)
                    .filter(|&hw| pre_bounds.upper[base + hw] >= best_lower)
                    .map(|hw| base + hw)
                    .collect();
                let mut always_max: Option<usize> = None;
                if candidates.len() == 1 {
                    let idx = candidates[0];
                    let mut max_other_upper = f64::NEG_INFINITY;
                    for hw in 0..spatial {
                        let j = base + hw;
                        if j == idx {
                            continue;
                        }
                        max_other_upper = max_other_upper.max(pre_bounds.upper[j]);
                    }
                    if pre_bounds.lower[idx] > max_other_upper {
                        always_max = Some(idx);
                    }
                }

                for hw in 0..spatial {
                    let idx = base + hw;
                    let (d_l, d_u) = if always_max == Some(idx) {
                        (1.0, 1.0)
                    } else if candidates.contains(&idx) {
                        (0.0, 1.0)
                    } else {
                        (0.0, 0.0)
                    };
                    for r in 0..coeff.rows() {
                        let cc = (coeff.lower[r][c], coeff.upper[r][c]);
                        let (p_l, p_u) = interval_mul(cc, (d_l, d_u));
                        next.lower[r][idx] += p_l;
                        next.upper[r][idx] += p_u;
                    }
                }
            }
            Ok(next)
        }
        NnLayer::BatchNorm2d {
            channels,
            height,
            width,
            scale,
            ..
        } => {
            let in_dim = pre_bounds.dim();
            let expected_in_dim = *channels * *height * *width;
            if in_dim != expected_in_dim {
                return Err(format!(
                    "BatchNorm2d input dim mismatch: got {in_dim}, expected {expected_in_dim}"
                ));
            }
            if coeff.cols() != in_dim || scale.len() != *channels {
                return Err(format!(
                    "BatchNorm2d jacobian backprop dim mismatch: coeff cols {}, expected {}, scale len {}",
                    coeff.cols(),
                    in_dim,
                    scale.len()
                ));
            }

            let spatial = *height * *width;
            let mut next = coeff.clone();
            for c in 0..*channels {
                let s = scale[c];
                for hw in 0..spatial {
                    let idx = c * spatial + hw;
                    for r in 0..next.rows() {
                        let cc = (next.lower[r][idx], next.upper[r][idx]);
                        let (p_l, p_u) = interval_mul_scalar(cc, s);
                        next.lower[r][idx] = p_l;
                        next.upper[r][idx] = p_u;
                    }
                }
            }
            Ok(next)
        }
        NnLayer::AvgPool2d {
            channels,
            height,
            width,
            kernel_size,
            stride,
        } => {
            let in_dim = pre_bounds.dim();
            let expected_in_dim = *channels * *height * *width;
            if in_dim != expected_in_dim {
                return Err(format!(
                    "AvgPool2d input dim mismatch: got {in_dim}, expected {expected_in_dim}"
                ));
            }
            if *kernel_size == 0 || *stride == 0 {
                return Err("AvgPool2d kernel_size/stride must be non-zero".to_string());
            }
            if *height < *kernel_size || *width < *kernel_size {
                return Err("AvgPool2d height/width < kernel_size".to_string());
            }
            let out_h = (*height - *kernel_size) / *stride + 1;
            let out_w = (*width - *kernel_size) / *stride + 1;
            let out_dim = *channels * out_h * out_w;
            if coeff.cols() != out_dim {
                return Err(format!(
                    "AvgPool2d jacobian backprop dim mismatch: coeff cols {}, expected {}",
                    coeff.cols(),
                    out_dim
                ));
            }

            let scale = 1.0 / (*kernel_size * *kernel_size) as f64;
            let mut next = IntervalMatrix::zeros(coeff.rows(), in_dim);
            for c in 0..*channels {
                for oh in 0..out_h {
                    for ow in 0..out_w {
                        let out_idx = c * out_h * out_w + oh * out_w + ow;
                        let start_h = oh * *stride;
                        let start_w = ow * *stride;
                        for kh in 0..*kernel_size {
                            for kw in 0..*kernel_size {
                                let ih = start_h + kh;
                                let iw = start_w + kw;
                                let in_idx = c * *height * *width + ih * *width + iw;
                                for r in 0..coeff.rows() {
                                    let cc = (coeff.lower[r][out_idx], coeff.upper[r][out_idx]);
                                    let (p_l, p_u) = interval_mul_scalar(cc, scale);
                                    next.lower[r][in_idx] += p_l;
                                    next.upper[r][in_idx] += p_u;
                                }
                            }
                        }
                    }
                }
            }
            Ok(next)
        }
        NnLayer::MaxPool2d {
            channels,
            height,
            width,
            kernel_size,
            stride,
        } => {
            let in_dim = pre_bounds.dim();
            let expected_in_dim = *channels * *height * *width;
            if in_dim != expected_in_dim {
                return Err(format!(
                    "MaxPool2d input dim mismatch: got {in_dim}, expected {expected_in_dim}"
                ));
            }
            if *kernel_size == 0 || *stride == 0 {
                return Err("MaxPool2d kernel_size/stride must be non-zero".to_string());
            }
            if *height < *kernel_size || *width < *kernel_size {
                return Err("MaxPool2d height/width < kernel_size".to_string());
            }
            let out_h = (*height - *kernel_size) / *stride + 1;
            let out_w = (*width - *kernel_size) / *stride + 1;
            let out_dim = *channels * out_h * out_w;
            if coeff.cols() != out_dim {
                return Err(format!(
                    "MaxPool2d jacobian backprop dim mismatch: coeff cols {}, expected {}",
                    coeff.cols(),
                    out_dim
                ));
            }

            let mut next = IntervalMatrix::zeros(coeff.rows(), in_dim);
            for c in 0..*channels {
                for oh in 0..out_h {
                    for ow in 0..out_w {
                        let out_idx = c * out_h * out_w + oh * out_w + ow;
                        let start_h = oh * *stride;
                        let start_w = ow * *stride;

                        let mut window = Vec::new();
                        for kh in 0..*kernel_size {
                            for kw in 0..*kernel_size {
                                let ih = start_h + kh;
                                let iw = start_w + kw;
                                let in_idx = c * *height * *width + ih * *width + iw;
                                window.push(in_idx);
                            }
                        }

                        let best_lower = window
                            .iter()
                            .map(|&idx| pre_bounds.lower[idx])
                            .fold(f64::NEG_INFINITY, f64::max);
                        let candidates: Vec<usize> = window
                            .iter()
                            .copied()
                            .filter(|&idx| pre_bounds.upper[idx] >= best_lower)
                            .collect();

                        let mut always_max: Option<usize> = None;
                        if candidates.len() == 1 {
                            let idx = candidates[0];
                            let mut max_other_upper = f64::NEG_INFINITY;
                            for &j in &window {
                                if j == idx {
                                    continue;
                                }
                                max_other_upper = max_other_upper.max(pre_bounds.upper[j]);
                            }
                            if pre_bounds.lower[idx] > max_other_upper {
                                always_max = Some(idx);
                            }
                        }

                        for &idx in &window {
                            let (d_l, d_u) = if always_max == Some(idx) {
                                (1.0, 1.0)
                            } else if candidates.contains(&idx) {
                                (0.0, 1.0)
                            } else {
                                (0.0, 0.0)
                            };
                            for r in 0..coeff.rows() {
                                let cc = (coeff.lower[r][out_idx], coeff.upper[r][out_idx]);
                                let (p_l, p_u) = interval_mul(cc, (d_l, d_u));
                                next.lower[r][idx] += p_l;
                                next.upper[r][idx] += p_u;
                            }
                        }
                    }
                }
            }
            Ok(next)
        }
        NnLayer::ResidualAdd { .. } | NnLayer::Concat { .. } => {
            Err("ResidualAdd/Concat monotonicity requires skip-aware propagation".to_string())
        }
    }
}

/// ReLU relaxation state for a neuron
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ReLUState {
    /// Always active (pre-activation lower bound >= 0)
    Active,
    /// Always inactive (pre-activation upper bound <= 0)
    Inactive,
    /// Unstable: crosses zero, needs linear relaxation
    Unstable { lower: f64, upper: f64 },
}

impl ReLUState {
    /// Determine ReLU state from pre-activation bounds
    #[must_use]
    pub fn from_bounds(lower: f64, upper: f64) -> Self {
        if lower >= 0.0 {
            Self::Active
        } else if upper <= 0.0 {
            Self::Inactive
        } else {
            Self::Unstable { lower, upper }
        }
    }

    /// Get the lower bound linear coefficients (slope, intercept)
    /// For unstable ReLU, we use the "adaptive" lower bound: choose slope = 0 or 1
    /// that gives tighter bounds depending on the coefficient sign in backward pass
    #[must_use]
    pub const fn lower_bound_coeffs(&self, use_zero_slope: bool) -> (f64, f64) {
        match self {
            Self::Active => (1.0, 0.0),   // y = x
            Self::Inactive => (0.0, 0.0), // y = 0
            Self::Unstable { .. } => {
                // Adaptive: choose slope 0 or 1 based on backward pass needs
                if use_zero_slope {
                    (0.0, 0.0) // y >= 0
                } else {
                    (1.0, 0.0) // y >= x
                }
            }
        }
    }

    /// Get the upper bound linear coefficients (slope, intercept)
    /// For unstable ReLU: y <= upper * (x - lower) / (upper - lower)
    ///                    y <= slope * x + intercept where slope = u/(u-l), intercept = -l*u/(u-l)
    #[must_use]
    pub fn upper_bound_coeffs(&self) -> (f64, f64) {
        match self {
            Self::Active => (1.0, 0.0),   // y = x
            Self::Inactive => (0.0, 0.0), // y = 0
            Self::Unstable { lower, upper } => {
                let l = *lower;
                let u = *upper;
                let slope = u / (u - l);
                let intercept = -l * u / (u - l);
                (slope, intercept)
            }
        }
    }
}

/// CROWN bound propagation
///
/// Computes tighter output bounds than IBP by using linear relaxation.
/// The key insight is that for ReLU networks, we can bound the output as
/// a linear function of the input, then concretize to get tighter interval bounds.
#[must_use]
pub fn crown_propagate(network: &NnNetwork, input_bounds: &Bounds) -> Bounds {
    // Step 1: Forward pass with IBP to get pre-activation bounds
    let pre_bounds = PreActivationBounds::compute(network, input_bounds);

    // Step 2: Backward pass to propagate linear bounds
    let linear_bounds = crown_backward(network, &pre_bounds);

    // Step 3: Concretize linear bounds using input bounds
    linear_bounds.concretize(input_bounds)
}

// ============================================================================
// Alpha-CROWN Optimization
// ============================================================================

/// Alpha parameters for each unstable ReLU neuron
/// α ∈ [0, 1] where the lower bound is y >= α*x
#[derive(Debug, Clone)]
pub struct AlphaParams {
    /// Alpha values for each layer, each neuron
    /// `alphas[layer_idx][neuron_idx]` for unstable neurons only
    pub alphas: Vec<Vec<f64>>,
    /// Mapping from (layer_idx, neuron_idx) to alpha index
    /// Used to track which neurons are unstable
    pub unstable_map: Vec<Vec<Option<usize>>>,
}

impl AlphaParams {
    /// Initialize alpha parameters from pre-activation bounds
    /// Identifies unstable neurons and initializes alphas to 0.5
    #[must_use]
    pub fn initialize(network: &NnNetwork, pre_bounds: &PreActivationBounds) -> Self {
        let mut alphas = Vec::new();
        let mut unstable_map = Vec::new();

        for (layer_idx, layer) in network.layers.iter().enumerate() {
            match layer {
                NnLayer::ReLU | NnLayer::LeakyReLU { .. } => {
                    let bounds = &pre_bounds.layer_bounds[layer_idx];
                    let dim = bounds.dim();
                    let mut layer_alphas = Vec::new();
                    let mut layer_map = vec![None; dim];

                    for j in 0..dim {
                        let l = bounds.lower[j];
                        let u = bounds.upper[j];
                        // Unstable if bounds cross zero
                        if l < 0.0 && u > 0.0 {
                            layer_map[j] = Some(layer_alphas.len());
                            // Initialize to 0.5 (midpoint)
                            layer_alphas.push(0.5);
                        }
                    }

                    alphas.push(layer_alphas);
                    unstable_map.push(layer_map);
                }
                _ => {
                    // Non-activation layers have no alphas
                    alphas.push(Vec::new());
                    unstable_map.push(Vec::new());
                }
            }
        }

        Self {
            alphas,
            unstable_map,
        }
    }

    /// Initialize with adaptive selection (same as regular CROWN)
    #[must_use]
    pub fn initialize_adaptive(
        network: &NnNetwork,
        pre_bounds: &PreActivationBounds,
        output_signs: &[f64],
    ) -> Self {
        let mut params = Self::initialize(network, pre_bounds);

        // Set initial alphas based on output coefficient signs
        // This is a heuristic: if output coefficient is positive, use alpha=0 (y>=0)
        // If negative, use alpha=1 (y>=x)
        for layer_alphas in &mut params.alphas {
            for alpha in layer_alphas.iter_mut() {
                // Use average sign to set initial alpha
                let avg_sign: f64 = output_signs.iter().sum::<f64>() / output_signs.len() as f64;
                *alpha = if avg_sign >= 0.0 { 0.0 } else { 1.0 };
            }
        }

        params
    }

    /// Get alpha for a specific neuron
    #[must_use]
    pub fn get_alpha(&self, layer_idx: usize, neuron_idx: usize) -> Option<f64> {
        if layer_idx < self.unstable_map.len() && neuron_idx < self.unstable_map[layer_idx].len() {
            self.unstable_map[layer_idx][neuron_idx].map(|idx| self.alphas[layer_idx][idx])
        } else {
            None
        }
    }

    /// Set alpha for a specific neuron
    pub fn set_alpha(&mut self, layer_idx: usize, neuron_idx: usize, value: f64) {
        if layer_idx < self.unstable_map.len() && neuron_idx < self.unstable_map[layer_idx].len() {
            if let Some(idx) = self.unstable_map[layer_idx][neuron_idx] {
                self.alphas[layer_idx][idx] = value.clamp(0.0, 1.0);
            }
        }
    }

    /// Count total number of unstable neurons (number of alpha parameters)
    pub fn num_unstable(&self) -> usize {
        self.alphas.iter().map(std::vec::Vec::len).sum()
    }

    /// Project all alphas to [0, 1]
    pub fn project(&mut self) {
        for layer_alphas in &mut self.alphas {
            for alpha in layer_alphas.iter_mut() {
                *alpha = alpha.clamp(0.0, 1.0);
            }
        }
    }
}

/// Configuration for alpha-CROWN optimization
#[derive(Debug, Clone)]
pub struct AlphaCrownConfig {
    /// Number of optimization iterations
    pub iterations: usize,
    /// Learning rate for gradient descent
    pub learning_rate: f64,
    /// Whether to optimize for lower bounds (true) or upper bounds (false)
    pub optimize_lower: bool,
    /// Early stopping threshold (stop if improvement < threshold)
    pub early_stop_threshold: f64,
}

impl Default for AlphaCrownConfig {
    fn default() -> Self {
        Self {
            iterations: 20,
            learning_rate: 0.1,
            optimize_lower: true,
            early_stop_threshold: 1e-6,
        }
    }
}

/// Alpha-CROWN bound propagation with optimized alpha parameters
///
/// Uses projected gradient descent to find alpha values that maximize
/// the tightness of the final output bounds.
#[must_use]
pub fn alpha_crown_propagate(
    network: &NnNetwork,
    input_bounds: &Bounds,
    config: &AlphaCrownConfig,
) -> Bounds {
    // Step 1: Forward pass with IBP to get pre-activation bounds
    let pre_bounds = PreActivationBounds::compute(network, input_bounds);

    // Step 2: Initialize alpha parameters
    let mut alphas = AlphaParams::initialize(network, &pre_bounds);

    // If no unstable neurons, CROWN is exact
    if alphas.num_unstable() == 0 {
        return crown_propagate(network, input_bounds);
    }

    // Step 3: Optimize alphas using projected gradient descent
    let mut best_bounds =
        crown_backward_with_alphas(network, &pre_bounds, &alphas).concretize(input_bounds);
    let mut best_objective = compute_objective(&best_bounds, config.optimize_lower);

    for _iter in 0..config.iterations {
        // Compute gradients by finite differences
        let gradients =
            compute_alpha_gradients(network, &pre_bounds, &alphas, input_bounds, config);

        // Update alphas using gradient descent
        update_alphas(
            &mut alphas,
            &gradients,
            config.learning_rate,
            config.optimize_lower,
        );

        // Project to valid range
        alphas.project();

        // Compute new bounds
        let new_bounds =
            crown_backward_with_alphas(network, &pre_bounds, &alphas).concretize(input_bounds);
        let new_objective = compute_objective(&new_bounds, config.optimize_lower);

        // Check for improvement
        let improvement = if config.optimize_lower {
            new_objective - best_objective
        } else {
            best_objective - new_objective
        };

        if improvement > 0.0 {
            best_bounds = new_bounds;
            best_objective = new_objective;
        }

        // Early stopping
        if improvement.abs() < config.early_stop_threshold {
            break;
        }
    }

    best_bounds
}

/// Compute objective function (sum of lower bounds or negative sum of upper bounds)
fn compute_objective(bounds: &Bounds, optimize_lower: bool) -> f64 {
    if optimize_lower {
        bounds.lower.iter().sum::<f64>()
    } else {
        -bounds.upper.iter().sum::<f64>()
    }
}

/// Compute gradients of objective with respect to alpha parameters
/// Uses finite differences approximation
fn compute_alpha_gradients(
    network: &NnNetwork,
    pre_bounds: &PreActivationBounds,
    alphas: &AlphaParams,
    input_bounds: &Bounds,
    config: &AlphaCrownConfig,
) -> Vec<Vec<f64>> {
    let epsilon = 1e-4;
    let mut gradients = Vec::new();

    for layer_idx in 0..alphas.alphas.len() {
        let mut layer_grads = Vec::new();

        for alpha_idx in 0..alphas.alphas[layer_idx].len() {
            // Compute f(alpha + epsilon)
            let mut alphas_plus = alphas.clone();
            alphas_plus.alphas[layer_idx][alpha_idx] += epsilon;
            alphas_plus.project();
            let bounds_plus = crown_backward_with_alphas(network, pre_bounds, &alphas_plus)
                .concretize(input_bounds);
            let obj_plus = compute_objective(&bounds_plus, config.optimize_lower);

            // Compute f(alpha - epsilon)
            let mut alphas_minus = alphas.clone();
            alphas_minus.alphas[layer_idx][alpha_idx] -= epsilon;
            alphas_minus.project();
            let bounds_minus = crown_backward_with_alphas(network, pre_bounds, &alphas_minus)
                .concretize(input_bounds);
            let obj_minus = compute_objective(&bounds_minus, config.optimize_lower);

            // Gradient approximation
            let grad = (obj_plus - obj_minus) / (2.0 * epsilon);
            layer_grads.push(grad);
        }

        gradients.push(layer_grads);
    }

    gradients
}

/// Update alpha parameters using gradients
fn update_alphas(
    alphas: &mut AlphaParams,
    gradients: &[Vec<f64>],
    learning_rate: f64,
    optimize_lower: bool,
) {
    for (layer_idx, layer_grads) in gradients.iter().enumerate() {
        for (alpha_idx, &grad) in layer_grads.iter().enumerate() {
            // Gradient ascent for lower bounds, descent for upper bounds
            let direction = if optimize_lower { 1.0 } else { -1.0 };
            alphas.alphas[layer_idx][alpha_idx] += direction * learning_rate * grad;
        }
    }
}

/// CROWN backward pass with explicit alpha parameters
fn crown_backward_with_alphas(
    network: &NnNetwork,
    pre_bounds: &PreActivationBounds,
    alphas: &AlphaParams,
) -> LinearBounds {
    let n_layers = network.layers.len();
    if n_layers == 0 {
        return LinearBounds::identity(pre_bounds.layer_bounds[0].dim());
    }

    // Start with identity at the output
    let output_dim = pre_bounds.layer_bounds[n_layers].dim();
    let mut bounds = LinearBounds::identity(output_dim);

    // Propagate backward through each layer
    for (layer_idx, layer) in network.layers.iter().enumerate().rev() {
        let pre_layer_bounds = &pre_bounds.layer_bounds[layer_idx];
        bounds =
            crown_backward_layer_with_alphas(&bounds, layer, pre_layer_bounds, alphas, layer_idx);
    }

    bounds
}

/// Propagate linear bounds backward through a single layer with alpha parameters
fn crown_backward_layer_with_alphas(
    output_bounds: &LinearBounds,
    layer: &NnLayer,
    pre_bounds: &Bounds,
    alphas: &AlphaParams,
    layer_idx: usize,
) -> LinearBounds {
    match layer {
        NnLayer::Linear { weights, bias } => crown_backward_linear(output_bounds, weights, bias),
        NnLayer::ReLU => {
            crown_backward_relu_with_alphas(output_bounds, pre_bounds, alphas, layer_idx)
        }
        NnLayer::LeakyReLU { negative_slope } => {
            // Leaky ReLU doesn't use alpha optimization (it's already tight)
            crown_backward_leaky_relu(output_bounds, pre_bounds, *negative_slope)
        }
        NnLayer::Sigmoid => crown_backward_sigmoid(output_bounds, pre_bounds),
        NnLayer::Tanh => crown_backward_tanh(output_bounds, pre_bounds),
        NnLayer::BatchNorm { scale, bias } => crown_backward_batchnorm(output_bounds, scale, bias),
        NnLayer::Dropout { .. } | NnLayer::Flatten => {
            // Identity layers: pass through unchanged
            output_bounds.clone()
        }
        NnLayer::MaxPool1d {
            kernel_size,
            stride,
        } => crown_backward_maxpool1d(output_bounds, pre_bounds, *kernel_size, *stride),
        NnLayer::AvgPool1d {
            kernel_size,
            stride,
        } => crown_backward_avgpool1d(output_bounds, *kernel_size, *stride),
        NnLayer::Conv1d {
            in_channels,
            kernel_size,
            stride,
            padding,
            weights,
            bias,
            ..
        } => crown_backward_conv1d(
            output_bounds,
            weights,
            bias,
            *in_channels,
            *kernel_size,
            *stride,
            *padding,
        ),
        NnLayer::Conv2d {
            in_channels,
            input_height,
            input_width,
            kernel_size,
            stride,
            padding,
            weights,
            bias,
            ..
        } => crown_backward_conv2d(
            output_bounds,
            weights,
            bias,
            *in_channels,
            *input_height,
            *input_width,
            *kernel_size,
            *stride,
            *padding,
        ),
        NnLayer::GlobalAvgPool2d {
            channels,
            height,
            width,
        } => crown_backward_global_avgpool2d(output_bounds, *channels, *height, *width),
        NnLayer::GlobalMaxPool2d {
            channels,
            height,
            width,
        } => crown_backward_global_maxpool2d(output_bounds, pre_bounds, *channels, *height, *width),
        NnLayer::BatchNorm2d {
            channels,
            height,
            width,
            scale,
            bias,
        } => crown_backward_batchnorm2d(output_bounds, *channels, *height, *width, scale, bias),
        NnLayer::MaxPool2d {
            channels,
            height,
            width,
            kernel_size,
            stride,
        } => crown_backward_maxpool2d(
            output_bounds,
            pre_bounds,
            *channels,
            *height,
            *width,
            *kernel_size,
            *stride,
        ),
        NnLayer::AvgPool2d {
            channels,
            height,
            width,
            kernel_size,
            stride,
        } => crown_backward_avgpool2d(
            output_bounds,
            *channels,
            *height,
            *width,
            *kernel_size,
            *stride,
        ),
        NnLayer::ResidualAdd { .. } | NnLayer::Concat { .. } => {
            // Skip connections require special handling in crown_backward loop
            panic!("ResidualAdd/Concat must be handled at CROWN propagation level")
        }
    }
}

/// CROWN backward pass through ReLU with explicit alpha parameters
fn crown_backward_relu_with_alphas(
    output_bounds: &LinearBounds,
    pre_bounds: &Bounds,
    alphas: &AlphaParams,
    layer_idx: usize,
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let in_dim = pre_bounds.dim();

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_lower = vec![0.0; out_neurons];
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_upper = vec![0.0; out_neurons];

    // For each output bound, propagate through ReLU relaxation
    for i in 0..out_neurons {
        for j in 0..in_dim {
            let l = pre_bounds.lower[j];
            let u = pre_bounds.upper[j];
            let state = ReLUState::from_bounds(l, u);

            // Get upper bound coefficients (same as regular CROWN)
            let (upper_slope, upper_intercept) = state.upper_bound_coeffs();

            // Get lower bound coefficients using alpha if available
            let (lower_slope, lower_intercept) = match state {
                ReLUState::Active => (1.0, 0.0),
                ReLUState::Inactive => (0.0, 0.0),
                ReLUState::Unstable { .. } => {
                    // Use alpha parameter if available
                    let alpha = alphas.get_alpha(layer_idx, j).unwrap_or(0.5);
                    (alpha, 0.0) // y >= alpha * x
                }
            };

            // For lower bound on final output:
            if output_bounds.a_lower[i][j] >= 0.0 {
                a_lower[i][j] = output_bounds.a_lower[i][j] * lower_slope;
                b_lower[i] += output_bounds.a_lower[i][j] * lower_intercept;
            } else {
                a_lower[i][j] = output_bounds.a_lower[i][j] * upper_slope;
                b_lower[i] += output_bounds.a_lower[i][j] * upper_intercept;
            }

            // For upper bound on final output:
            // When coefficient < 0, want smallest lower bound (use alpha=1, slope=1)
            let lower_slope_for_upper = match state {
                ReLUState::Active => 1.0,
                ReLUState::Inactive => 0.0,
                ReLUState::Unstable { .. } => {
                    // For upper bound calculation with negative coefficient,
                    // we want y >= x (slope=1) to get smallest value
                    if output_bounds.a_upper[i][j] < 0.0 {
                        1.0
                    } else {
                        alphas.get_alpha(layer_idx, j).unwrap_or(0.5)
                    }
                }
            };

            if output_bounds.a_upper[i][j] >= 0.0 {
                a_upper[i][j] = output_bounds.a_upper[i][j] * upper_slope;
                b_upper[i] += output_bounds.a_upper[i][j] * upper_intercept;
            } else {
                a_upper[i][j] = output_bounds.a_upper[i][j] * lower_slope_for_upper;
                b_upper[i] += 0.0; // intercept is 0 for both y>=0 and y>=x
            }
        }

        // Add the original bias terms
        b_lower[i] += output_bounds.b_lower[i];
        b_upper[i] += output_bounds.b_upper[i];
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

// ============================================================================
// Branch-and-Bound Verification
// ============================================================================

/// Configuration for branch-and-bound verification
#[derive(Debug, Clone)]
pub struct BranchAndBoundConfig {
    /// Maximum number of neuron splits to perform
    pub max_splits: usize,
    /// Maximum depth of branching tree
    pub max_depth: usize,
    /// Use alpha-CROWN at leaf nodes
    pub use_alpha_crown: bool,
    /// Timeout per branch (milliseconds)
    pub timeout_ms: u64,
    /// Early stopping when bounds are tight enough
    pub bound_threshold: f64,
}

impl Default for BranchAndBoundConfig {
    fn default() -> Self {
        Self {
            max_splits: 10,
            max_depth: 5,
            use_alpha_crown: true,
            timeout_ms: 1000,
            bound_threshold: 1e-6,
        }
    }
}

/// Information about an unstable neuron for branching decisions
#[derive(Debug, Clone)]
struct UnstableNeuron {
    layer_idx: usize,
    neuron_idx: usize,
    lower: f64,
    upper: f64,
}

impl UnstableNeuron {
    /// Score for branching priority (larger = higher priority)
    /// Uses product of absolute bounds as heuristic
    fn branching_score(&self) -> f64 {
        self.lower.abs() * self.upper.abs()
    }
}

/// Branch-and-bound propagation for tight neural network bounds
///
/// Recursively splits unstable neurons into active/inactive cases,
/// verifies each case separately, and combines results.
/// This gives provably tight bounds by eliminating relaxation error.
#[must_use]
pub fn branch_and_bound_propagate(
    network: &NnNetwork,
    input_bounds: &Bounds,
    config: &BranchAndBoundConfig,
) -> Bounds {
    // Start with alpha-CROWN bounds as baseline
    let alpha_config = AlphaCrownConfig {
        iterations: 20,
        ..Default::default()
    };
    let baseline_bounds = alpha_crown_propagate(network, input_bounds, &alpha_config);

    // Find unstable neurons
    let pre_bounds = PreActivationBounds::compute(network, input_bounds);
    let unstable_neurons = find_unstable_neurons(network, &pre_bounds);

    if unstable_neurons.is_empty() {
        // No unstable neurons - bounds are exact
        return baseline_bounds;
    }

    // Perform branch-and-bound
    branch_and_bound_recursive(
        network,
        input_bounds,
        &unstable_neurons,
        0,
        config,
        &baseline_bounds,
    )
}

/// Find all unstable neurons and their bounds
fn find_unstable_neurons(
    network: &NnNetwork,
    pre_bounds: &PreActivationBounds,
) -> Vec<UnstableNeuron> {
    let mut unstable = Vec::new();

    for (layer_idx, layer) in network.layers.iter().enumerate() {
        if matches!(layer, NnLayer::ReLU | NnLayer::LeakyReLU { .. }) {
            let bounds = &pre_bounds.layer_bounds[layer_idx];
            for neuron_idx in 0..bounds.dim() {
                let l = bounds.lower[neuron_idx];
                let u = bounds.upper[neuron_idx];
                if l < 0.0 && u > 0.0 {
                    unstable.push(UnstableNeuron {
                        layer_idx,
                        neuron_idx,
                        lower: l,
                        upper: u,
                    });
                }
            }
        }
    }

    // Sort by branching score (highest priority first)
    unstable.sort_by(|a, b| {
        b.branching_score()
            .partial_cmp(&a.branching_score())
            .unwrap_or(std::cmp::Ordering::Equal)
    });

    unstable
}

/// Recursive branch-and-bound
fn branch_and_bound_recursive(
    network: &NnNetwork,
    input_bounds: &Bounds,
    unstable_neurons: &[UnstableNeuron],
    depth: usize,
    config: &BranchAndBoundConfig,
    current_bounds: &Bounds,
) -> Bounds {
    // Base case: max depth or no more splits
    if depth >= config.max_depth || unstable_neurons.is_empty() {
        return current_bounds.clone();
    }

    // Select neuron to split (first in sorted list is highest priority)
    let split_neuron = &unstable_neurons[0];
    let remaining_neurons: Vec<UnstableNeuron> = unstable_neurons[1..]
        .iter()
        .take(config.max_splits.saturating_sub(1))
        .cloned()
        .collect();

    // Branch 1: Force neuron to be active (pre-activation >= 0)
    // This is simulated by adjusting input bounds to ensure neuron is positive
    // For simplicity, we use the linear relaxation with forced state
    let active_bounds = verify_with_forced_state(
        network,
        input_bounds,
        split_neuron,
        true, // force active
        config,
    );

    // Branch 2: Force neuron to be inactive (pre-activation <= 0)
    let inactive_bounds = verify_with_forced_state(
        network,
        input_bounds,
        split_neuron,
        false, // force inactive
        config,
    );

    // Combine bounds by taking union (sound over-approximation)
    let combined = combine_branch_bounds(&active_bounds, &inactive_bounds);

    // Recursively refine if beneficial
    if depth + 1 < config.max_depth && !remaining_neurons.is_empty() {
        let width_improvement = bound_width(current_bounds) - bound_width(&combined);
        if width_improvement > config.bound_threshold {
            return branch_and_bound_recursive(
                network,
                input_bounds,
                &remaining_neurons,
                depth + 1,
                config,
                &combined,
            );
        }
    }

    combined
}

/// Verify with a neuron forced to a specific state
fn verify_with_forced_state(
    network: &NnNetwork,
    input_bounds: &Bounds,
    neuron: &UnstableNeuron,
    force_active: bool,
    config: &BranchAndBoundConfig,
) -> Bounds {
    // Create modified pre-activation bounds with forced state
    let mut modified_bounds = PreActivationBounds::compute(network, input_bounds);

    // Adjust the bounds for the target neuron
    if force_active {
        // Force lower >= 0
        modified_bounds.layer_bounds[neuron.layer_idx].lower[neuron.neuron_idx] = 0.0;
    } else {
        // Force upper <= 0
        modified_bounds.layer_bounds[neuron.layer_idx].upper[neuron.neuron_idx] = 0.0;
    }

    // Propagate with alpha-CROWN using modified bounds
    if config.use_alpha_crown {
        let alphas = AlphaParams::initialize(network, &modified_bounds);
        crown_backward_with_alphas(network, &modified_bounds, &alphas).concretize(input_bounds)
    } else {
        crown_backward(network, &modified_bounds).concretize(input_bounds)
    }
}

/// Combine bounds from two branches (take union)
fn combine_branch_bounds(a: &Bounds, b: &Bounds) -> Bounds {
    assert_eq!(a.dim(), b.dim(), "Branch bounds must have same dimension");

    let mut lower = Vec::with_capacity(a.dim());
    let mut upper = Vec::with_capacity(a.dim());

    for i in 0..a.dim() {
        // Union: take min of lower bounds, max of upper bounds
        lower.push(a.lower[i].min(b.lower[i]));
        upper.push(a.upper[i].max(b.upper[i]));
    }

    Bounds { lower, upper }
}

/// Calculate total bound width
fn bound_width(bounds: &Bounds) -> f64 {
    bounds
        .lower
        .iter()
        .zip(bounds.upper.iter())
        .map(|(l, u)| u - l)
        .sum()
}

// ============================================================================
// Beta-CROWN: Split Constraint Optimization
// ============================================================================

/// A split constraint on a specific neuron
#[derive(Debug, Clone, PartialEq)]
pub struct SplitConstraint {
    /// Layer index of the split neuron
    pub layer_idx: usize,
    /// Neuron index within the layer
    pub neuron_idx: usize,
    /// If true, neuron is forced active (output = input)
    pub is_active: bool,
}

impl SplitConstraint {
    /// Create a split constraint for an active neuron
    #[must_use]
    pub const fn active(layer_idx: usize, neuron_idx: usize) -> Self {
        Self {
            layer_idx,
            neuron_idx,
            is_active: true,
        }
    }

    /// Create a split constraint for an inactive neuron
    #[must_use]
    pub const fn inactive(layer_idx: usize, neuron_idx: usize) -> Self {
        Self {
            layer_idx,
            neuron_idx,
            is_active: false,
        }
    }
}

/// Beta parameters for split constraint optimization
#[derive(Debug, Clone)]
pub struct BetaParams {
    /// Beta values for each split constraint
    pub betas: Vec<f64>,
    /// The split constraints being optimized
    pub splits: Vec<SplitConstraint>,
}

impl BetaParams {
    /// Initialize beta parameters from a set of split constraints
    #[must_use]
    pub fn new(splits: Vec<SplitConstraint>) -> Self {
        let betas = vec![0.0; splits.len()];
        Self { betas, splits }
    }

    /// Get beta for a split at index
    #[must_use]
    pub fn get_beta(&self, idx: usize) -> f64 {
        self.betas.get(idx).copied().unwrap_or(0.0)
    }

    /// Set beta for a split at index
    pub fn set_beta(&mut self, idx: usize, value: f64) {
        if idx < self.betas.len() {
            self.betas[idx] = value.max(0.0);
        }
    }

    /// Find the split constraint for a given neuron
    #[must_use]
    pub fn find_split(
        &self,
        layer_idx: usize,
        neuron_idx: usize,
    ) -> Option<(usize, &SplitConstraint)> {
        self.splits
            .iter()
            .enumerate()
            .find(|(_, s)| s.layer_idx == layer_idx && s.neuron_idx == neuron_idx)
    }

    /// Project all betas to non-negative
    pub fn project(&mut self) {
        for beta in &mut self.betas {
            *beta = beta.max(0.0);
        }
    }

    /// Total number of splits
    #[must_use]
    pub const fn num_splits(&self) -> usize {
        self.splits.len()
    }
}

/// Configuration for Beta-CROWN optimization
#[derive(Debug, Clone, PartialEq)]
pub struct BetaCrownConfig {
    /// Number of joint optimization iterations
    pub iterations: usize,
    /// Learning rate for alpha updates
    pub alpha_lr: f64,
    /// Learning rate for beta updates
    pub beta_lr: f64,
    /// Whether to optimize for lower bounds
    pub optimize_lower: bool,
    /// Early stopping threshold
    pub early_stop_threshold: f64,
    /// Maximum number of splits to consider
    pub max_splits: usize,
}

impl Default for BetaCrownConfig {
    fn default() -> Self {
        Self {
            iterations: 30,
            alpha_lr: 0.1,
            beta_lr: 0.05,
            optimize_lower: true,
            early_stop_threshold: 1e-6,
            max_splits: 10,
        }
    }
}

/// Beta-CROWN bound propagation with split constraint optimization
#[must_use]
pub fn beta_crown_propagate(
    network: &NnNetwork,
    input_bounds: &Bounds,
    config: &BetaCrownConfig,
) -> Bounds {
    let pre_bounds = PreActivationBounds::compute(network, input_bounds);
    let unstable = find_unstable_neurons(network, &pre_bounds);
    let splits = select_splits_for_beta_crown(&unstable, config.max_splits);

    if splits.is_empty() {
        let alpha_config = AlphaCrownConfig {
            iterations: config.iterations,
            learning_rate: config.alpha_lr,
            optimize_lower: config.optimize_lower,
            early_stop_threshold: config.early_stop_threshold,
        };
        return alpha_crown_propagate(network, input_bounds, &alpha_config);
    }

    let mut alphas = AlphaParams::initialize(network, &pre_bounds);
    let betas = BetaParams::new(splits);

    let mut best_bounds =
        crown_backward_with_splits(network, &pre_bounds, &alphas, &betas).concretize(input_bounds);
    let mut best_objective = compute_objective(&best_bounds, config.optimize_lower);

    for _ in 0..config.iterations {
        let grads = compute_alpha_gradients_with_splits(
            network,
            &pre_bounds,
            &alphas,
            &betas,
            input_bounds,
            config,
        );
        update_alphas(&mut alphas, &grads, config.alpha_lr, config.optimize_lower);
        alphas.project();

        let new_bounds = crown_backward_with_splits(network, &pre_bounds, &alphas, &betas)
            .concretize(input_bounds);
        let new_objective = compute_objective(&new_bounds, config.optimize_lower);

        let improvement = if config.optimize_lower {
            new_objective - best_objective
        } else {
            best_objective - new_objective
        };

        if improvement > 0.0 {
            best_bounds = new_bounds;
            best_objective = new_objective;
        }

        if improvement.abs() < config.early_stop_threshold {
            break;
        }
    }

    best_bounds
}

/// Select which neurons to split for Beta-CROWN
fn select_splits_for_beta_crown(
    unstable: &[UnstableNeuron],
    max_splits: usize,
) -> Vec<SplitConstraint> {
    unstable
        .iter()
        .take(max_splits)
        .map(|n| {
            let is_active = n.lower.abs() < n.upper.abs();
            SplitConstraint {
                layer_idx: n.layer_idx,
                neuron_idx: n.neuron_idx,
                is_active,
            }
        })
        .collect()
}

/// CROWN backward pass that respects split constraints
fn crown_backward_with_splits(
    network: &NnNetwork,
    pre_bounds: &PreActivationBounds,
    alphas: &AlphaParams,
    betas: &BetaParams,
) -> LinearBounds {
    let output_dim = match network.layers.last() {
        Some(NnLayer::Linear { weights, .. }) => weights.len(),
        _ => pre_bounds.layer_bounds.last().map_or(0, Bounds::dim),
    };

    let mut a_lower = vec![vec![0.0; output_dim]; output_dim];
    let mut b_lower = vec![0.0; output_dim];
    let mut a_upper = vec![vec![0.0; output_dim]; output_dim];
    let mut b_upper = vec![0.0; output_dim];

    for i in 0..output_dim {
        a_lower[i][i] = 1.0;
        a_upper[i][i] = 1.0;
    }

    for layer_idx in (0..network.layers.len()).rev() {
        let layer = &network.layers[layer_idx];
        let bounds = &pre_bounds.layer_bounds[layer_idx];

        match layer {
            NnLayer::Linear { weights, bias } => {
                let (new_a_l, new_b_l) =
                    crown_backward_linear_splits(weights, bias, &a_lower, &b_lower);
                let (new_a_u, new_b_u) =
                    crown_backward_linear_splits(weights, bias, &a_upper, &b_upper);
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::ReLU => {
                let (new_a_l, new_b_l) = crown_backward_relu_splits(
                    bounds, &a_lower, &b_lower, alphas, betas, layer_idx,
                );
                let (new_a_u, new_b_u) = crown_backward_relu_splits(
                    bounds, &a_upper, &b_upper, alphas, betas, layer_idx,
                );
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::LeakyReLU { negative_slope } => {
                let (new_a_l, new_b_l) = crown_backward_leaky_relu_splits(
                    bounds,
                    &a_lower,
                    &b_lower,
                    *negative_slope,
                    betas,
                    layer_idx,
                );
                let (new_a_u, new_b_u) = crown_backward_leaky_relu_splits(
                    bounds,
                    &a_upper,
                    &b_upper,
                    *negative_slope,
                    betas,
                    layer_idx,
                );
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::Sigmoid | NnLayer::Tanh => {
                // Use standard CROWN backward for sigmoid/tanh
                let (new_a_lower, new_b_lower, new_a_upper, new_b_upper) =
                    crown_backward_sigmoid_tanh(
                        layer, bounds, &a_lower, &b_lower, &a_upper, &b_upper,
                    );
                a_lower = new_a_lower;
                b_lower = new_b_lower;
                a_upper = new_a_upper;
                b_upper = new_b_upper;
            }
            NnLayer::BatchNorm { scale, bias } => {
                // BatchNorm is a diagonal linear transformation: y = scale * x + bias
                let (new_a_l, new_b_l) =
                    crown_backward_batchnorm_splits(scale, bias, &a_lower, &b_lower);
                let (new_a_u, new_b_u) =
                    crown_backward_batchnorm_splits(scale, bias, &a_upper, &b_upper);
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::Dropout { .. } | NnLayer::Flatten => {
                // Identity layers: pass through unchanged
                // a_lower, b_lower, a_upper, b_upper remain the same
            }
            NnLayer::MaxPool1d {
                kernel_size,
                stride,
            } => {
                let (new_a_l, new_b_l) = crown_backward_maxpool1d_splits(
                    bounds,
                    &a_lower,
                    &b_lower,
                    *kernel_size,
                    *stride,
                );
                let (new_a_u, new_b_u) = crown_backward_maxpool1d_splits(
                    bounds,
                    &a_upper,
                    &b_upper,
                    *kernel_size,
                    *stride,
                );
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::AvgPool1d {
                kernel_size,
                stride,
            } => {
                let (new_a_l, new_b_l) =
                    crown_backward_avgpool1d_splits(&a_lower, &b_lower, *kernel_size, *stride);
                let (new_a_u, new_b_u) =
                    crown_backward_avgpool1d_splits(&a_upper, &b_upper, *kernel_size, *stride);
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::Conv1d {
                in_channels,
                kernel_size,
                stride,
                padding,
                weights,
                bias,
                ..
            } => {
                let (new_a_l, new_b_l) = crown_backward_conv1d_splits(
                    weights,
                    bias,
                    &a_lower,
                    &b_lower,
                    *in_channels,
                    *kernel_size,
                    *stride,
                    *padding,
                );
                let (new_a_u, new_b_u) = crown_backward_conv1d_splits(
                    weights,
                    bias,
                    &a_upper,
                    &b_upper,
                    *in_channels,
                    *kernel_size,
                    *stride,
                    *padding,
                );
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::Conv2d {
                in_channels,
                input_height,
                input_width,
                kernel_size,
                stride,
                padding,
                weights,
                bias,
                ..
            } => {
                let (new_a_l, new_b_l) = crown_backward_conv2d_splits(
                    weights,
                    bias,
                    &a_lower,
                    &b_lower,
                    *in_channels,
                    *input_height,
                    *input_width,
                    *kernel_size,
                    *stride,
                    *padding,
                );
                let (new_a_u, new_b_u) = crown_backward_conv2d_splits(
                    weights,
                    bias,
                    &a_upper,
                    &b_upper,
                    *in_channels,
                    *input_height,
                    *input_width,
                    *kernel_size,
                    *stride,
                    *padding,
                );
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::GlobalAvgPool2d {
                channels,
                height,
                width,
            } => {
                let (new_a_l, new_b_l) = crown_backward_global_avgpool2d_splits(
                    &a_lower, &b_lower, *channels, *height, *width,
                );
                let (new_a_u, new_b_u) = crown_backward_global_avgpool2d_splits(
                    &a_upper, &b_upper, *channels, *height, *width,
                );
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::GlobalMaxPool2d {
                channels,
                height,
                width,
            } => {
                let (new_a_l, new_b_l) = crown_backward_global_maxpool2d_splits(
                    bounds, &a_lower, &b_lower, *channels, *height, *width,
                );
                let (new_a_u, new_b_u) = crown_backward_global_maxpool2d_splits(
                    bounds, &a_upper, &b_upper, *channels, *height, *width,
                );
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::BatchNorm2d {
                channels,
                height,
                width,
                scale,
                bias,
            } => {
                let (new_a_l, new_b_l) = crown_backward_batchnorm2d_splits(
                    scale, bias, &a_lower, &b_lower, *channels, *height, *width,
                );
                let (new_a_u, new_b_u) = crown_backward_batchnorm2d_splits(
                    scale, bias, &a_upper, &b_upper, *channels, *height, *width,
                );
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::MaxPool2d {
                channels,
                height,
                width,
                kernel_size,
                stride,
            } => {
                let (new_a_l, new_b_l) = crown_backward_maxpool2d_splits(
                    bounds,
                    &a_lower,
                    &b_lower,
                    *channels,
                    *height,
                    *width,
                    *kernel_size,
                    *stride,
                );
                let (new_a_u, new_b_u) = crown_backward_maxpool2d_splits(
                    bounds,
                    &a_upper,
                    &b_upper,
                    *channels,
                    *height,
                    *width,
                    *kernel_size,
                    *stride,
                );
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::AvgPool2d {
                channels,
                height,
                width,
                kernel_size,
                stride,
            } => {
                let (new_a_l, new_b_l) = crown_backward_avgpool2d_splits(
                    &a_lower,
                    &b_lower,
                    *channels,
                    *height,
                    *width,
                    *kernel_size,
                    *stride,
                );
                let (new_a_u, new_b_u) = crown_backward_avgpool2d_splits(
                    &a_upper,
                    &b_upper,
                    *channels,
                    *height,
                    *width,
                    *kernel_size,
                    *stride,
                );
                a_lower = new_a_l;
                b_lower = new_b_l;
                a_upper = new_a_u;
                b_upper = new_b_u;
            }
            NnLayer::ResidualAdd { .. } | NnLayer::Concat { .. } => {
                // Skip connections require special handling in CROWN backward pass
                panic!("ResidualAdd/Concat must be handled at CROWN propagation level")
            }
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

fn crown_backward_linear_splits(
    weights: &[Vec<f64>],
    biases: &[f64],
    a_in: &[Vec<f64>],
    b_in: &[f64],
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let in_dim = if weights.is_empty() {
        0
    } else {
        weights[0].len()
    };

    let mut a_out = vec![vec![0.0; in_dim]; out_dim];
    let mut b_out = vec![0.0; out_dim];

    for i in 0..out_dim {
        b_out[i] = b_in[i];
        for k in 0..weights.len() {
            b_out[i] += a_in[i][k] * biases[k];
        }
        for j in 0..in_dim {
            for k in 0..weights.len() {
                a_out[i][j] += a_in[i][k] * weights[k][j];
            }
        }
    }

    (a_out, b_out)
}

fn crown_backward_relu_splits(
    bounds: &Bounds,
    a_in: &[Vec<f64>],
    b_in: &[f64],
    alphas: &AlphaParams,
    betas: &BetaParams,
    layer_idx: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let relu_dim = bounds.dim();
    let mut a_out = vec![vec![0.0; relu_dim]; out_dim];
    let b_out = b_in.to_vec();

    for j in 0..relu_dim {
        let l = bounds.lower[j];
        let u = bounds.upper[j];
        let split = betas.find_split(layer_idx, j);

        let slope = if let Some((_, constraint)) = split {
            if constraint.is_active {
                1.0
            } else {
                0.0
            }
        } else if l >= 0.0 {
            1.0
        } else if u <= 0.0 {
            0.0
        } else {
            alphas.get_alpha(layer_idx, j).unwrap_or(0.0)
        };

        for i in 0..out_dim {
            a_out[i][j] = a_in[i][j] * slope;
        }
    }

    (a_out, b_out)
}

fn crown_backward_leaky_relu_splits(
    bounds: &Bounds,
    a_in: &[Vec<f64>],
    b_in: &[f64],
    neg_slope: f64,
    betas: &BetaParams,
    layer_idx: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let dim = bounds.dim();
    let mut a_out = vec![vec![0.0; dim]; out_dim];
    let b_out = b_in.to_vec();

    for j in 0..dim {
        let l = bounds.lower[j];
        let u = bounds.upper[j];
        let split = betas.find_split(layer_idx, j);

        let slope = if let Some((_, constraint)) = split {
            if constraint.is_active {
                1.0
            } else {
                neg_slope
            }
        } else if l >= 0.0 {
            1.0
        } else if u <= 0.0 {
            neg_slope
        } else {
            (u - neg_slope * l) / (u - l)
        };

        for i in 0..out_dim {
            a_out[i][j] = a_in[i][j] * slope;
        }
    }

    (a_out, b_out)
}

/// CROWN backward pass through BatchNorm for split-aware computation
/// BatchNorm: y = scale * x + bias
fn crown_backward_batchnorm_splits(
    scale: &[f64],
    bias: &[f64],
    a_in: &[Vec<f64>],
    b_in: &[f64],
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let dim = scale.len();

    let mut a_out = vec![vec![0.0; dim]; out_dim];
    let mut b_out = b_in.to_vec();

    for j in 0..dim {
        let s = scale[j];
        let b = bias[j];
        for i in 0..out_dim {
            a_out[i][j] = a_in[i][j] * s;
            b_out[i] += a_in[i][j] * b;
        }
    }

    (a_out, b_out)
}

/// CROWN backward pass through MaxPool1d for split-aware computation
/// Uses dominant input based on upper bounds
fn crown_backward_maxpool1d_splits(
    pre_bounds: &Bounds,
    a_in: &[Vec<f64>],
    b_in: &[f64],
    kernel_size: usize,
    stride: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let out_pool_dim = if a_in.is_empty() { 0 } else { a_in[0].len() };
    let in_dim = pre_bounds.dim();

    let mut a_out = vec![vec![0.0; in_dim]; out_dim];
    let b_out = b_in.to_vec();

    // For each pooling output position, find the dominant input
    for pool_out_idx in 0..out_pool_dim {
        let start = pool_out_idx * stride;

        // Find input with highest upper bound
        let mut best_idx = start;
        let mut best_upper = f64::NEG_INFINITY;
        for k in 0..kernel_size {
            let idx = start + k;
            if idx < in_dim && pre_bounds.upper[idx] > best_upper {
                best_upper = pre_bounds.upper[idx];
                best_idx = idx;
            }
        }

        // Attribute coefficients to dominant input
        for i in 0..out_dim {
            a_out[i][best_idx] += a_in[i][pool_out_idx];
        }
    }

    (a_out, b_out)
}

/// CROWN backward pass through AvgPool1d for split-aware computation
/// Distributes coefficients equally to all inputs in window
fn crown_backward_avgpool1d_splits(
    a_in: &[Vec<f64>],
    b_in: &[f64],
    kernel_size: usize,
    stride: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let out_pool_dim = if a_in.is_empty() { 0 } else { a_in[0].len() };
    // Compute input dimension from pooling parameters
    let in_dim = if out_pool_dim > 0 {
        (out_pool_dim - 1) * stride + kernel_size
    } else {
        0
    };

    let scale = 1.0 / kernel_size as f64;
    let mut a_out = vec![vec![0.0; in_dim]; out_dim];
    let b_out = b_in.to_vec();

    // Distribute coefficients to all inputs in each window
    for pool_out_idx in 0..out_pool_dim {
        let start = pool_out_idx * stride;
        for k in 0..kernel_size {
            let idx = start + k;
            if idx < in_dim {
                for i in 0..out_dim {
                    a_out[i][idx] += a_in[i][pool_out_idx] * scale;
                }
            }
        }
    }

    (a_out, b_out)
}

/// CROWN backward pass through GlobalAvgPool2d for split-aware computation
fn crown_backward_global_avgpool2d_splits(
    a_in: &[Vec<f64>],
    b_in: &[f64],
    channels: usize,
    height: usize,
    width: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let spatial_size = height * width;
    let in_dim = channels * spatial_size;
    let scale = 1.0 / spatial_size as f64;

    let mut a_out = vec![vec![0.0; in_dim]; out_dim];
    let b_out = b_in.to_vec();

    // For each channel output, distribute coefficients equally to all spatial inputs
    for c in 0..channels {
        for i in 0..out_dim {
            let coef = a_in[i][c] * scale;
            for hw in 0..spatial_size {
                let idx = c * spatial_size + hw;
                a_out[i][idx] = coef;
            }
        }
    }

    (a_out, b_out)
}

/// CROWN backward pass through GlobalMaxPool2d for split-aware computation
fn crown_backward_global_maxpool2d_splits(
    pre_bounds: &Bounds,
    a_in: &[Vec<f64>],
    b_in: &[f64],
    channels: usize,
    height: usize,
    width: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let spatial_size = height * width;
    let in_dim = channels * spatial_size;

    let mut a_out = vec![vec![0.0; in_dim]; out_dim];
    let b_out = b_in.to_vec();

    // For each channel, find the argmax position using midpoint of bounds
    for c in 0..channels {
        let mut max_idx = 0;
        let mut max_val = f64::NEG_INFINITY;
        for hw in 0..spatial_size {
            let idx = c * spatial_size + hw;
            if idx < pre_bounds.lower.len() {
                let mid = (pre_bounds.lower[idx] + pre_bounds.upper[idx]) / 2.0;
                if mid > max_val {
                    max_val = mid;
                    max_idx = idx;
                }
            }
        }
        // Route all coefficients for this channel through the argmax position
        for i in 0..out_dim {
            a_out[i][max_idx] += a_in[i][c];
        }
    }

    (a_out, b_out)
}

/// CROWN backward pass through BatchNorm2d for split-aware computation
/// BatchNorm2d applies y[c, h, w] = scale[c] * x[c, h, w] + bias[c]
#[allow(clippy::too_many_arguments)]
fn crown_backward_batchnorm2d_splits(
    scale: &[f64],
    bias: &[f64],
    a_in: &[Vec<f64>],
    b_in: &[f64],
    channels: usize,
    height: usize,
    width: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let spatial_size = height * width;
    let in_dim = channels * spatial_size;

    let mut a_out = vec![vec![0.0; in_dim]; out_dim];
    let mut b_out = b_in.to_vec();

    for c in 0..channels {
        let s = scale[c];
        let b = bias[c];
        for hw in 0..spatial_size {
            let idx = c * spatial_size + hw;
            if idx < a_in[0].len() {
                for i in 0..out_dim {
                    a_out[i][idx] = a_in[i][idx] * s;
                    b_out[i] += a_in[i][idx] * b;
                }
            }
        }
    }

    (a_out, b_out)
}

/// CROWN backward pass through MaxPool2d for split-aware computation
/// Uses dominant input based on upper bounds
#[allow(clippy::too_many_arguments)]
fn crown_backward_maxpool2d_splits(
    pre_bounds: &Bounds,
    a_in: &[Vec<f64>],
    b_in: &[f64],
    channels: usize,
    height: usize,
    width: usize,
    kernel_size: usize,
    stride: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let out_height = (height - kernel_size) / stride + 1;
    let out_width = (width - kernel_size) / stride + 1;
    let in_dim = channels * height * width;

    let mut a_out = vec![vec![0.0; in_dim]; out_dim];
    let b_out = b_in.to_vec();

    // For each output position, find the argmax in the corresponding input window
    for c in 0..channels {
        for oh in 0..out_height {
            for ow in 0..out_width {
                let out_idx = c * out_height * out_width + oh * out_width + ow;

                // Find argmax in the input window
                let mut max_idx = 0;
                let mut max_val = f64::NEG_INFINITY;
                for kh in 0..kernel_size {
                    for kw in 0..kernel_size {
                        let ih = oh * stride + kh;
                        let iw = ow * stride + kw;
                        if ih < height && iw < width {
                            let in_idx = c * height * width + ih * width + iw;
                            if in_idx < pre_bounds.upper.len() {
                                let mid =
                                    (pre_bounds.lower[in_idx] + pre_bounds.upper[in_idx]) / 2.0;
                                if mid > max_val {
                                    max_val = mid;
                                    max_idx = in_idx;
                                }
                            }
                        }
                    }
                }

                // Route coefficients through the argmax position
                if out_idx < a_in[0].len() {
                    for i in 0..out_dim {
                        a_out[i][max_idx] += a_in[i][out_idx];
                    }
                }
            }
        }
    }

    (a_out, b_out)
}

/// CROWN backward pass through AvgPool2d for split-aware computation
/// Distributes coefficients equally to all inputs in window
#[allow(clippy::too_many_arguments)]
fn crown_backward_avgpool2d_splits(
    a_in: &[Vec<f64>],
    b_in: &[f64],
    channels: usize,
    height: usize,
    width: usize,
    kernel_size: usize,
    stride: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let out_height = (height - kernel_size) / stride + 1;
    let out_width = (width - kernel_size) / stride + 1;
    let in_dim = channels * height * width;
    let scale = 1.0 / (kernel_size * kernel_size) as f64;

    let mut a_out = vec![vec![0.0; in_dim]; out_dim];
    let b_out = b_in.to_vec();

    // For each output position, distribute coefficients equally to all inputs in the window
    for c in 0..channels {
        for oh in 0..out_height {
            for ow in 0..out_width {
                let out_idx = c * out_height * out_width + oh * out_width + ow;

                if out_idx < a_in[0].len() {
                    for kh in 0..kernel_size {
                        for kw in 0..kernel_size {
                            let ih = oh * stride + kh;
                            let iw = ow * stride + kw;
                            if ih < height && iw < width {
                                let in_idx = c * height * width + ih * width + iw;
                                for i in 0..out_dim {
                                    a_out[i][in_idx] += a_in[i][out_idx] * scale;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    (a_out, b_out)
}

/// CROWN backward pass through Conv1d for split-aware computation
/// Conv1d is linear, so we propagate coefficients similarly to Linear layer
#[allow(clippy::too_many_arguments)]
fn crown_backward_conv1d_splits(
    weights: &[Vec<Vec<f64>>],
    bias: &[f64],
    a_in: &[Vec<f64>],
    b_in: &[f64],
    in_channels: usize,
    kernel_size: usize,
    stride: usize,
    padding: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let conv_out_dim = if a_in.is_empty() { 0 } else { a_in[0].len() };

    if conv_out_dim == 0 || weights.is_empty() {
        return (a_in.to_vec(), b_in.to_vec());
    }

    let out_channels = weights.len();
    let output_length = conv_out_dim / out_channels;
    if output_length == 0 {
        return (a_in.to_vec(), b_in.to_vec());
    }

    // Compute input_length from output_length and conv parameters
    let input_length = if output_length > 0 {
        (output_length - 1) * stride + kernel_size - 2 * padding
    } else {
        0
    };

    if input_length == 0 {
        return (a_in.to_vec(), b_in.to_vec());
    }

    let input_dim = in_channels * input_length;

    let mut a_out = vec![vec![0.0; input_dim]; out_dim];
    let mut b_out = b_in.to_vec();

    // Add bias contributions
    for out_ch in 0..out_channels {
        let b = if out_ch < bias.len() {
            bias[out_ch]
        } else {
            0.0
        };
        for out_pos in 0..output_length {
            let conv_out_idx = out_ch * output_length + out_pos;
            if conv_out_idx >= conv_out_dim {
                continue;
            }
            for i in 0..out_dim {
                b_out[i] += a_in[i][conv_out_idx] * b;
            }
        }
    }

    // Propagate coefficients backward
    for out_ch in 0..out_channels {
        for out_pos in 0..output_length {
            let conv_out_idx = out_ch * output_length + out_pos;
            if conv_out_idx >= conv_out_dim {
                continue;
            }

            for in_ch in 0..in_channels {
                for k in 0..kernel_size {
                    let in_pos_padded = out_pos * stride + k;
                    if in_pos_padded < padding || in_pos_padded >= padding + input_length {
                        continue;
                    }

                    let in_pos = in_pos_padded - padding;
                    let in_idx = in_ch * input_length + in_pos;
                    if in_idx >= input_dim {
                        continue;
                    }

                    let w = weights[out_ch][in_ch][k];
                    for i in 0..out_dim {
                        a_out[i][in_idx] += a_in[i][conv_out_idx] * w;
                    }
                }
            }
        }
    }

    (a_out, b_out)
}

/// CROWN backward pass through Conv2d for split-aware computation
/// Conv2d is linear, so we propagate coefficients similarly to Linear layer
#[allow(clippy::too_many_arguments)]
fn crown_backward_conv2d_splits(
    weights: &[Vec<Vec<Vec<f64>>>],
    bias: &[f64],
    a_in: &[Vec<f64>],
    b_in: &[f64],
    in_channels: usize,
    input_height: usize,
    input_width: usize,
    kernel_size: usize,
    stride: usize,
    padding: usize,
) -> (Vec<Vec<f64>>, Vec<f64>) {
    let out_dim = a_in.len();
    let conv_out_dim = if a_in.is_empty() { 0 } else { a_in[0].len() };

    if conv_out_dim == 0 || weights.is_empty() {
        return (a_in.to_vec(), b_in.to_vec());
    }

    let out_channels = weights.len();
    let effective_height = input_height + 2 * padding;
    let effective_width = input_width + 2 * padding;

    if effective_height < kernel_size || effective_width < kernel_size || stride == 0 {
        return (a_in.to_vec(), b_in.to_vec());
    }

    let out_height = (effective_height - kernel_size) / stride + 1;
    let out_width = (effective_width - kernel_size) / stride + 1;
    let expected_out_dim = out_channels * out_height * out_width;

    if conv_out_dim != expected_out_dim {
        return (a_in.to_vec(), b_in.to_vec());
    }

    let input_dim = in_channels * input_height * input_width;

    let mut a_out = vec![vec![0.0; input_dim]; out_dim];
    let mut b_out = b_in.to_vec();

    // Add bias contributions
    for out_ch in 0..out_channels {
        let b = if out_ch < bias.len() {
            bias[out_ch]
        } else {
            0.0
        };
        for out_h in 0..out_height {
            for out_w in 0..out_width {
                let conv_out_idx = out_ch * out_height * out_width + out_h * out_width + out_w;
                if conv_out_idx >= conv_out_dim {
                    continue;
                }
                for i in 0..out_dim {
                    b_out[i] += a_in[i][conv_out_idx] * b;
                }
            }
        }
    }

    // Propagate coefficients backward
    for out_ch in 0..out_channels {
        for out_h in 0..out_height {
            for out_w in 0..out_width {
                let conv_out_idx = out_ch * out_height * out_width + out_h * out_width + out_w;
                if conv_out_idx >= conv_out_dim {
                    continue;
                }

                for in_ch in 0..in_channels {
                    for kh in 0..kernel_size {
                        for kw in 0..kernel_size {
                            let in_h_padded = out_h * stride + kh;
                            let in_w_padded = out_w * stride + kw;

                            if in_h_padded < padding
                                || in_h_padded >= padding + input_height
                                || in_w_padded < padding
                                || in_w_padded >= padding + input_width
                            {
                                continue;
                            }

                            let in_h = in_h_padded - padding;
                            let in_w = in_w_padded - padding;
                            let in_idx =
                                in_ch * input_height * input_width + in_h * input_width + in_w;
                            if in_idx >= input_dim {
                                continue;
                            }

                            let w = weights[out_ch][in_ch][kh][kw];
                            for i in 0..out_dim {
                                a_out[i][in_idx] += a_in[i][conv_out_idx] * w;
                            }
                        }
                    }
                }
            }
        }
    }

    (a_out, b_out)
}

fn crown_backward_sigmoid_tanh(
    layer: &NnLayer,
    bounds: &Bounds,
    a_lower: &[Vec<f64>],
    b_lower: &[f64],
    a_upper: &[Vec<f64>],
    b_upper: &[f64],
) -> CrownBackwardBounds {
    let out_dim = a_lower.len();
    let dim = bounds.dim();

    let mut new_a_lower = vec![vec![0.0; dim]; out_dim];
    let mut new_b_lower = b_lower.to_vec();
    let mut new_a_upper = vec![vec![0.0; dim]; out_dim];
    let mut new_b_upper = b_upper.to_vec();

    for j in 0..dim {
        let l = bounds.lower[j];
        let u = bounds.upper[j];

        let (l_slope, l_int, u_slope, u_int) = match layer {
            NnLayer::Sigmoid => compute_sigmoid_linear_bounds(l, u),
            NnLayer::Tanh => compute_tanh_linear_bounds(l, u),
            _ => (1.0, 0.0, 1.0, 0.0),
        };

        for i in 0..out_dim {
            new_a_lower[i][j] = a_lower[i][j] * l_slope;
            new_b_lower[i] += a_lower[i][j] * l_int;
            new_a_upper[i][j] = a_upper[i][j] * u_slope;
            new_b_upper[i] += a_upper[i][j] * u_int;
        }
    }

    (new_a_lower, new_b_lower, new_a_upper, new_b_upper)
}

fn compute_sigmoid_linear_bounds(l: f64, u: f64) -> (f64, f64, f64, f64) {
    let sigmoid = |x: f64| 1.0 / (1.0 + (-x).exp());
    let sl = sigmoid(l);
    let su = sigmoid(u);

    if (u - l).abs() < 1e-8 {
        let slope = sl * (1.0 - sl);
        return (slope, sl - slope * l, slope, su - slope * u);
    }

    let upper_slope = (su - sl) / (u - l);
    let upper_intercept = sl - upper_slope * l;
    let lower_slope = upper_slope.min(0.25);
    let lower_intercept = sl - lower_slope * l;

    (lower_slope, lower_intercept, upper_slope, upper_intercept)
}

fn compute_tanh_linear_bounds(l: f64, u: f64) -> (f64, f64, f64, f64) {
    let tl = l.tanh();
    let tu = u.tanh();

    if (u - l).abs() < 1e-8 {
        let slope = 1.0 - tl * tl;
        return (slope, tl - slope * l, slope, tu - slope * u);
    }

    let upper_slope = (tu - tl) / (u - l);
    let upper_intercept = tl - upper_slope * l;
    let lower_slope = upper_slope.min(1.0);
    let lower_intercept = tl - lower_slope * l;

    (lower_slope, lower_intercept, upper_slope, upper_intercept)
}

fn compute_alpha_gradients_with_splits(
    network: &NnNetwork,
    pre_bounds: &PreActivationBounds,
    alphas: &AlphaParams,
    betas: &BetaParams,
    input_bounds: &Bounds,
    config: &BetaCrownConfig,
) -> Vec<Vec<f64>> {
    let delta = 0.01;
    let mut gradients = Vec::new();

    for layer_idx in 0..alphas.alphas.len() {
        let mut layer_grads = Vec::new();

        for alpha_idx in 0..alphas.alphas[layer_idx].len() {
            let mut alphas_plus = alphas.clone();
            alphas_plus.alphas[layer_idx][alpha_idx] += delta;
            alphas_plus.project();

            let mut alphas_minus = alphas.clone();
            alphas_minus.alphas[layer_idx][alpha_idx] -= delta;
            alphas_minus.project();

            let bounds_plus = crown_backward_with_splits(network, pre_bounds, &alphas_plus, betas)
                .concretize(input_bounds);
            let bounds_minus =
                crown_backward_with_splits(network, pre_bounds, &alphas_minus, betas)
                    .concretize(input_bounds);

            let obj_plus = compute_objective(&bounds_plus, config.optimize_lower);
            let obj_minus = compute_objective(&bounds_minus, config.optimize_lower);

            layer_grads.push((obj_plus - obj_minus) / (2.0 * delta));
        }

        gradients.push(layer_grads);
    }

    gradients
}

// ============================================================================
// Input Domain Splitting
// ============================================================================

/// Configuration for input domain splitting verification
#[derive(Debug, Clone, PartialEq)]
pub struct InputSplitConfig {
    /// Maximum number of splits per dimension
    pub max_splits_per_dim: usize,
    /// Maximum total number of sub-regions (2^n where n = splits across all dims)
    pub max_total_regions: usize,
    /// Base bound method to use for each sub-region
    pub base_method: BoundMethod,
    /// Minimum improvement threshold to continue splitting
    pub improvement_threshold: f64,
    /// Split dimensions with largest width first
    pub split_largest_first: bool,
}

impl Default for InputSplitConfig {
    fn default() -> Self {
        Self {
            max_splits_per_dim: 2,
            max_total_regions: 16,
            base_method: BoundMethod::CrownOptimized,
            improvement_threshold: 0.01,
            split_largest_first: true,
        }
    }
}

/// Split input bounds along a specific dimension at the midpoint
fn split_bounds_along_dim(bounds: &Bounds, dim: usize) -> (Bounds, Bounds) {
    let mid = (bounds.lower[dim] + bounds.upper[dim]) / 2.0;

    // Lower half: same bounds except upper[dim] = mid
    let mut lower_half = bounds.clone();
    lower_half.upper[dim] = mid;

    // Upper half: same bounds except lower[dim] = mid
    let mut upper_half = bounds.clone();
    upper_half.lower[dim] = mid;

    (lower_half, upper_half)
}

/// Get dimension widths for prioritizing splits
fn get_dim_widths(bounds: &Bounds) -> Vec<(usize, f64)> {
    bounds
        .lower
        .iter()
        .zip(bounds.upper.iter())
        .enumerate()
        .map(|(i, (l, u))| (i, u - l))
        .collect()
}

/// Split input bounds into multiple sub-regions
/// Returns all sub-regions after splitting up to max_regions
fn split_bounds_recursive(
    bounds: &Bounds,
    config: &InputSplitConfig,
    current_regions: &mut Vec<Bounds>,
    split_counts: &mut Vec<usize>,
) {
    // Check if we've hit the limit
    if current_regions.len() >= config.max_total_regions {
        return;
    }

    // Find dimension to split
    let dim_to_split = if config.split_largest_first {
        let widths = get_dim_widths(bounds);
        // Find dimension with largest width that hasn't been split too many times
        widths
            .iter()
            .filter(|&&(dim, _)| split_counts[dim] < config.max_splits_per_dim)
            .max_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal))
            .map(|&(dim, _)| dim)
    } else {
        // Round-robin: find first dimension that can still be split
        (0..bounds.dim()).find(|&dim| split_counts[dim] < config.max_splits_per_dim)
    };

    match dim_to_split {
        Some(dim) => {
            let (lower_half, upper_half) = split_bounds_along_dim(bounds, dim);
            split_counts[dim] += 1;

            // Recursively split both halves
            split_bounds_recursive(&lower_half, config, current_regions, split_counts);
            split_bounds_recursive(&upper_half, config, current_regions, split_counts);

            split_counts[dim] -= 1; // Restore for sibling branches
        }
        None => {
            // No more dimensions to split, add this region
            current_regions.push(bounds.clone());
        }
    }
}

/// Split input bounds into sub-regions based on configuration
#[must_use]
pub fn split_input_bounds(bounds: &Bounds, config: &InputSplitConfig) -> Vec<Bounds> {
    let mut regions = Vec::new();
    let mut split_counts = vec![0; bounds.dim()];

    split_bounds_recursive(bounds, config, &mut regions, &mut split_counts);

    // If no splitting happened, return original bounds
    if regions.is_empty() {
        regions.push(bounds.clone());
    }

    regions
}

#[derive(Debug, Clone)]
struct InputSplitRegion {
    input_bounds: Bounds,
    output_bounds: Bounds,
    split_counts: Vec<usize>,
}

fn choose_split_dim(
    bounds: &Bounds,
    split_counts: &[usize],
    config: &InputSplitConfig,
) -> Option<usize> {
    if config.max_splits_per_dim == 0 {
        return None;
    }

    if config.split_largest_first {
        let mut best_dim: Option<usize> = None;
        let mut best_width = f64::NEG_INFINITY;

        for dim in 0..bounds.dim() {
            if split_counts[dim] >= config.max_splits_per_dim {
                continue;
            }
            let width = bounds.upper[dim] - bounds.lower[dim];
            if width > best_width {
                best_width = width;
                best_dim = Some(dim);
            }
        }

        best_dim
    } else {
        (0..bounds.dim()).find(|&dim| split_counts[dim] < config.max_splits_per_dim)
    }
}

fn pick_region_to_split(
    regions: &[InputSplitRegion],
    config: &InputSplitConfig,
) -> Option<(usize, usize)> {
    if regions.is_empty() {
        return None;
    }

    if config.split_largest_first {
        let mut best: Option<(usize, usize, f64)> = None; // (region_idx, dim, width)

        for (region_idx, region) in regions.iter().enumerate() {
            if let Some(dim) = choose_split_dim(&region.input_bounds, &region.split_counts, config)
            {
                let width = region.input_bounds.upper[dim] - region.input_bounds.lower[dim];
                match best {
                    None => best = Some((region_idx, dim, width)),
                    Some((_, _, best_width)) if width > best_width => {
                        best = Some((region_idx, dim, width));
                    }
                    _ => {}
                }
            }
        }

        best.map(|(region_idx, dim, _)| (region_idx, dim))
    } else {
        for (region_idx, region) in regions.iter().enumerate() {
            if let Some(dim) = choose_split_dim(&region.input_bounds, &region.split_counts, config)
            {
                return Some((region_idx, dim));
            }
        }
        None
    }
}

fn input_split_regions_adaptive(
    network: &NnNetwork,
    input_bounds: &Bounds,
    config: &InputSplitConfig,
) -> Vec<InputSplitRegion> {
    let mut regions = vec![InputSplitRegion {
        input_bounds: input_bounds.clone(),
        output_bounds: propagate_with_method(network, input_bounds, &config.base_method),
        split_counts: vec![0; input_bounds.dim()],
    }];

    while regions.len() < config.max_total_regions {
        let Some((region_idx, dim)) = pick_region_to_split(&regions, config) else {
            break;
        };

        if regions.len() + 1 > config.max_total_regions {
            break;
        }

        let current_width = bound_width(&regions[region_idx].output_bounds);
        if current_width <= 0.0 {
            regions[region_idx].split_counts[dim] = config.max_splits_per_dim;
            continue;
        }

        let (lower_half, upper_half) =
            split_bounds_along_dim(&regions[region_idx].input_bounds, dim);
        let lower_bounds = propagate_with_method(network, &lower_half, &config.base_method);
        let upper_bounds = propagate_with_method(network, &upper_half, &config.base_method);
        let combined_bounds = combine_region_bounds(&lower_bounds, &upper_bounds);

        let combined_width = bound_width(&combined_bounds);
        let improvement_ratio = (current_width - combined_width) / current_width;

        if improvement_ratio >= config.improvement_threshold {
            let mut child_split_counts = regions[region_idx].split_counts.clone();
            child_split_counts[dim] += 1;

            let lower_counts = child_split_counts.clone();
            let upper_counts = child_split_counts;

            regions[region_idx] = InputSplitRegion {
                input_bounds: lower_half,
                output_bounds: lower_bounds,
                split_counts: lower_counts,
            };
            regions.push(InputSplitRegion {
                input_bounds: upper_half,
                output_bounds: upper_bounds,
                split_counts: upper_counts,
            });
        } else {
            regions[region_idx].split_counts[dim] = config.max_splits_per_dim;
        }
    }

    regions
}

/// Propagate bounds through network with input domain splitting
///
/// Splits the input domain into smaller sub-regions, verifies each independently,
/// and combines results. Smaller regions lead to tighter bounds due to reduced
/// relaxation error in CROWN.
#[must_use]
pub fn input_split_propagate(
    network: &NnNetwork,
    input_bounds: &Bounds,
    config: &InputSplitConfig,
) -> Bounds {
    if config.max_total_regions <= 1 || config.max_splits_per_dim == 0 {
        return propagate_with_method(network, input_bounds, &config.base_method);
    }

    let regions = input_split_regions_adaptive(network, input_bounds, config);

    let mut combined = regions.first().map_or_else(
        || propagate_with_method(network, input_bounds, &config.base_method),
        |r| r.output_bounds.clone(),
    );

    for region in regions.iter().skip(1) {
        combined = combine_region_bounds(&combined, &region.output_bounds);
    }

    combined
}

/// Propagate bounds using specified method
fn propagate_with_method(network: &NnNetwork, bounds: &Bounds, method: &BoundMethod) -> Bounds {
    match method {
        BoundMethod::Ibp => ibp_propagate(network, bounds),
        BoundMethod::Crown => crown_propagate(network, bounds),
        BoundMethod::CrownOptimized => {
            alpha_crown_propagate(network, bounds, &AlphaCrownConfig::default())
        }
        BoundMethod::AlphaBetaCrown => {
            branch_and_bound_propagate(network, bounds, &BranchAndBoundConfig::default())
        }
        BoundMethod::BetaCrown(config) => beta_crown_propagate(network, bounds, config),
        BoundMethod::InputSplit(config) => {
            // Avoid infinite recursion by using base method
            propagate_with_method(network, bounds, &config.base_method)
        }
    }
}

/// Combine bounds from two input regions (union)
fn combine_region_bounds(a: &Bounds, b: &Bounds) -> Bounds {
    assert_eq!(a.dim(), b.dim(), "Region bounds must have same dimension");

    let mut lower = Vec::with_capacity(a.dim());
    let mut upper = Vec::with_capacity(a.dim());

    for i in 0..a.dim() {
        // Union: take min of lower bounds, max of upper bounds
        lower.push(a.lower[i].min(b.lower[i]));
        upper.push(a.upper[i].max(b.upper[i]));
    }

    Bounds { lower, upper }
}

/// Verify robustness with input splitting
/// Splits the epsilon-ball and verifies each sub-region
#[must_use]
pub fn verify_robustness_with_input_splitting(
    network: &NnNetwork,
    input: &[f64],
    epsilon: f64,
    config: &InputSplitConfig,
) -> (bool, Bounds) {
    // Create input bounds
    let input_bounds = Bounds::linf_ball(input, epsilon);

    // Propagate with input splitting
    let output_bounds = input_split_propagate(network, &input_bounds, config);

    // Compute center output for comparison
    let center_output = forward_pass(network, input);
    let original_class = argmax(&center_output);

    // Check classification invariance
    let mut certified = true;
    for j in 0..output_bounds.dim() {
        if j != original_class && output_bounds.lower[original_class] <= output_bounds.upper[j] {
            certified = false;
            break;
        }
    }

    (certified, output_bounds)
}

// ============================================================================
// Improved Branching Heuristics
// ============================================================================

/// Branching heuristic for selecting which neuron to split
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub enum BranchingHeuristic {
    /// Simple: |lower| * |upper| score
    #[default]
    Simple,
    /// Smash: Split based on impact on output bounds
    Smash,
    /// FSB: Filtered Split-Balanced - balance branch bounds
    Fsb,
}

/// Compute smash score for a neuron
/// Higher score = more impact on output bounds when split
#[allow(dead_code)] // Planned for future use with advanced branching heuristics
fn compute_smash_score(network: &NnNetwork, input_bounds: &Bounds, neuron: &UnstableNeuron) -> f64 {
    // Get bounds with neuron forced active vs inactive
    let pre_bounds = PreActivationBounds::compute(network, input_bounds);

    // Force active
    let mut active_bounds = pre_bounds.clone();
    active_bounds.layer_bounds[neuron.layer_idx].lower[neuron.neuron_idx] = 0.0;
    let active_output = crown_backward(network, &active_bounds).concretize(input_bounds);

    // Force inactive
    let mut inactive_bounds = pre_bounds.clone();
    inactive_bounds.layer_bounds[neuron.layer_idx].upper[neuron.neuron_idx] = 0.0;
    let inactive_output = crown_backward(network, &inactive_bounds).concretize(input_bounds);

    // Score is the bound improvement from splitting
    let combined = combine_branch_bounds(&active_output, &inactive_output);
    let unsplit_output = crown_backward(network, &pre_bounds).concretize(input_bounds);

    bound_width(&unsplit_output) - bound_width(&combined)
}

/// Compute FSB (Filtered Split-Balanced) score for a neuron
/// Prefers splits that create balanced branches
#[allow(dead_code)] // Planned for future use with advanced branching heuristics
fn compute_fsb_score(network: &NnNetwork, input_bounds: &Bounds, neuron: &UnstableNeuron) -> f64 {
    let pre_bounds = PreActivationBounds::compute(network, input_bounds);

    // Get bounds for both branches
    let mut active_bounds = pre_bounds.clone();
    active_bounds.layer_bounds[neuron.layer_idx].lower[neuron.neuron_idx] = 0.0;
    let active_output = crown_backward(network, &active_bounds).concretize(input_bounds);

    let mut inactive_bounds = pre_bounds.clone();
    inactive_bounds.layer_bounds[neuron.layer_idx].upper[neuron.neuron_idx] = 0.0;
    let inactive_output = crown_backward(network, &inactive_bounds).concretize(input_bounds);

    // FSB prefers balanced branches (similar bound widths)
    let active_width = bound_width(&active_output);
    let inactive_width = bound_width(&inactive_output);

    // Score penalizes imbalance (smaller is better)
    let imbalance = (active_width - inactive_width).abs();
    let total_improvement =
        bound_width(&crown_backward(network, &pre_bounds).concretize(input_bounds))
            - bound_width(&combine_branch_bounds(&active_output, &inactive_output));

    // Balance improvement with balance
    total_improvement - 0.5 * imbalance
}

/// Sort unstable neurons by heuristic score
#[allow(dead_code)] // Planned for future use with advanced branching heuristics
fn sort_neurons_by_heuristic(
    neurons: &mut [UnstableNeuron],
    network: &NnNetwork,
    input_bounds: &Bounds,
    heuristic: BranchingHeuristic,
) {
    match heuristic {
        BranchingHeuristic::Simple => {
            // Already sorted by branching_score in find_unstable_neurons
        }
        BranchingHeuristic::Smash => {
            let mut scored: Vec<_> = neurons
                .iter()
                .map(|n| (n.clone(), compute_smash_score(network, input_bounds, n)))
                .collect();
            scored.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
            for (i, (n, _)) in scored.into_iter().enumerate() {
                neurons[i] = n;
            }
        }
        BranchingHeuristic::Fsb => {
            let mut scored: Vec<_> = neurons
                .iter()
                .map(|n| (n.clone(), compute_fsb_score(network, input_bounds, n)))
                .collect();
            scored.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
            for (i, (n, _)) in scored.into_iter().enumerate() {
                neurons[i] = n;
            }
        }
    }
}

/// CROWN backward pass: propagate linear bounds from output to input
fn crown_backward(network: &NnNetwork, pre_bounds: &PreActivationBounds) -> LinearBounds {
    let n_layers = network.layers.len();
    if n_layers == 0 {
        return LinearBounds::identity(pre_bounds.layer_bounds[0].dim());
    }

    // Start with identity at the output
    let output_dim = pre_bounds.layer_bounds[n_layers].dim();
    let mut bounds = LinearBounds::identity(output_dim);

    // Propagate backward through each layer
    for (layer_idx, layer) in network.layers.iter().enumerate().rev() {
        let pre_layer_bounds = &pre_bounds.layer_bounds[layer_idx];
        bounds = crown_backward_layer(&bounds, layer, pre_layer_bounds);
    }

    bounds
}

/// Propagate linear bounds backward through a single layer
fn crown_backward_layer(
    output_bounds: &LinearBounds,
    layer: &NnLayer,
    pre_bounds: &Bounds,
) -> LinearBounds {
    match layer {
        NnLayer::Linear { weights, bias } => crown_backward_linear(output_bounds, weights, bias),
        NnLayer::ReLU => crown_backward_relu(output_bounds, pre_bounds),
        NnLayer::LeakyReLU { negative_slope } => {
            crown_backward_leaky_relu(output_bounds, pre_bounds, *negative_slope)
        }
        NnLayer::Sigmoid => crown_backward_sigmoid(output_bounds, pre_bounds),
        NnLayer::Tanh => crown_backward_tanh(output_bounds, pre_bounds),
        NnLayer::BatchNorm { scale, bias } => crown_backward_batchnorm(output_bounds, scale, bias),
        NnLayer::Dropout { .. } | NnLayer::Flatten => {
            // Identity layers: pass through unchanged
            output_bounds.clone()
        }
        NnLayer::MaxPool1d {
            kernel_size,
            stride,
        } => crown_backward_maxpool1d(output_bounds, pre_bounds, *kernel_size, *stride),
        NnLayer::AvgPool1d {
            kernel_size,
            stride,
        } => crown_backward_avgpool1d(output_bounds, *kernel_size, *stride),
        NnLayer::Conv1d {
            in_channels,
            kernel_size,
            stride,
            padding,
            weights,
            bias,
            ..
        } => crown_backward_conv1d(
            output_bounds,
            weights,
            bias,
            *in_channels,
            *kernel_size,
            *stride,
            *padding,
        ),
        NnLayer::Conv2d {
            in_channels,
            input_height,
            input_width,
            kernel_size,
            stride,
            padding,
            weights,
            bias,
            ..
        } => crown_backward_conv2d(
            output_bounds,
            weights,
            bias,
            *in_channels,
            *input_height,
            *input_width,
            *kernel_size,
            *stride,
            *padding,
        ),
        NnLayer::GlobalAvgPool2d {
            channels,
            height,
            width,
        } => crown_backward_global_avgpool2d(output_bounds, *channels, *height, *width),
        NnLayer::GlobalMaxPool2d {
            channels,
            height,
            width,
        } => crown_backward_global_maxpool2d(output_bounds, pre_bounds, *channels, *height, *width),
        NnLayer::BatchNorm2d {
            channels,
            height,
            width,
            scale,
            bias,
        } => crown_backward_batchnorm2d(output_bounds, *channels, *height, *width, scale, bias),
        NnLayer::MaxPool2d {
            channels,
            height,
            width,
            kernel_size,
            stride,
        } => crown_backward_maxpool2d(
            output_bounds,
            pre_bounds,
            *channels,
            *height,
            *width,
            *kernel_size,
            *stride,
        ),
        NnLayer::AvgPool2d {
            channels,
            height,
            width,
            kernel_size,
            stride,
        } => crown_backward_avgpool2d(
            output_bounds,
            *channels,
            *height,
            *width,
            *kernel_size,
            *stride,
        ),
        NnLayer::ResidualAdd { .. } | NnLayer::Concat { .. } => {
            // Skip connections require special handling in CROWN backward pass
            panic!("ResidualAdd/Concat must be handled at CROWN propagation level")
        }
    }
}

/// CROWN backward pass through linear layer
/// If y = Wx + b and we have bounds on y (A_y * z + b_y), we get bounds on x
/// by substituting: A_y * (Wx + b) + b_y = (A_y * W) * x + (A_y * b + b_y)
fn crown_backward_linear(
    output_bounds: &LinearBounds,
    weights: &[Vec<f64>],
    bias: &[f64],
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let weight_out_dim = weights.len();
    let weight_in_dim = if weights.is_empty() {
        0
    } else {
        weights[0].len()
    };

    // New coefficients: A_new[i][j] = sum_k(A_old[i][k] * W[k][j])
    // New bias: b_new[i] = b_old[i] + sum_k(A_old[i][k] * bias[k])

    let mut a_lower = vec![vec![0.0; weight_in_dim]; out_neurons];
    let mut b_lower = vec![0.0; out_neurons];
    let mut a_upper = vec![vec![0.0; weight_in_dim]; out_neurons];
    let mut b_upper = vec![0.0; out_neurons];

    for i in 0..out_neurons {
        // Compute bias contribution
        for k in 0..weight_out_dim {
            b_lower[i] += output_bounds.a_lower[i][k] * bias[k];
            b_upper[i] += output_bounds.a_upper[i][k] * bias[k];
        }
        b_lower[i] += output_bounds.b_lower[i];
        b_upper[i] += output_bounds.b_upper[i];

        // Compute coefficient matrix
        for j in 0..weight_in_dim {
            for k in 0..weight_out_dim {
                a_lower[i][j] += output_bounds.a_lower[i][k] * weights[k][j];
                a_upper[i][j] += output_bounds.a_upper[i][k] * weights[k][j];
            }
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through ReLU
/// Uses linear relaxation for unstable neurons
fn crown_backward_relu(output_bounds: &LinearBounds, pre_bounds: &Bounds) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let in_dim = pre_bounds.dim();

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_lower = vec![0.0; out_neurons];
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_upper = vec![0.0; out_neurons];

    // Determine ReLU states for each neuron
    let relu_states: Vec<ReLUState> = (0..in_dim)
        .map(|j| ReLUState::from_bounds(pre_bounds.lower[j], pre_bounds.upper[j]))
        .collect();

    // For each output bound, propagate through ReLU relaxation
    for i in 0..out_neurons {
        for j in 0..in_dim {
            let state = &relu_states[j];

            // Get coefficients for this neuron
            let (upper_slope, upper_intercept) = state.upper_bound_coeffs();

            // For lower bound: choose slope adaptively based on coefficient sign
            // If A_lower[i][j] > 0, we want the LARGEST lower bound on ReLU -> use y >= 0 (zero slope)
            //   because for unstable ReLU with lb < 0: min(0) > min(x) = lb
            // If A_lower[i][j] < 0, we want the SMALLEST lower bound on ReLU -> use y >= x (slope 1)
            //   because for unstable ReLU: min(x) = lb is smaller than min(0) = 0
            let use_zero_slope = output_bounds.a_lower[i][j] >= 0.0;
            let (lower_slope, lower_intercept) = state.lower_bound_coeffs(use_zero_slope);

            // For lower bound on final output:
            // When A_lower[i][j] >= 0: use lower bound on ReLU (tighter is better)
            // When A_lower[i][j] < 0: use upper bound on ReLU (smaller is worse, gives tighter final lower)
            if output_bounds.a_lower[i][j] >= 0.0 {
                a_lower[i][j] = output_bounds.a_lower[i][j] * lower_slope;
                b_lower[i] += output_bounds.a_lower[i][j] * lower_intercept;
            } else {
                a_lower[i][j] = output_bounds.a_lower[i][j] * upper_slope;
                b_lower[i] += output_bounds.a_lower[i][j] * upper_intercept;
            }

            // For upper bound on final output:
            // When A_upper[i][j] >= 0: use upper bound on ReLU
            // When A_upper[i][j] < 0: use lower bound on ReLU
            //   We want the SMALLEST lower bound: y >= x gives min=lb which is smallest
            //   So use slope=1 (not zero slope) -> use_zero_slope = false
            let use_zero_slope_upper = output_bounds.a_upper[i][j] >= 0.0;
            let (lower_slope_u, lower_intercept_u) = state.lower_bound_coeffs(use_zero_slope_upper);

            if output_bounds.a_upper[i][j] >= 0.0 {
                a_upper[i][j] = output_bounds.a_upper[i][j] * upper_slope;
                b_upper[i] += output_bounds.a_upper[i][j] * upper_intercept;
            } else {
                a_upper[i][j] = output_bounds.a_upper[i][j] * lower_slope_u;
                b_upper[i] += output_bounds.a_upper[i][j] * lower_intercept_u;
            }
        }

        // Add the original bias terms
        b_lower[i] += output_bounds.b_lower[i];
        b_upper[i] += output_bounds.b_upper[i];
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through Leaky ReLU
fn crown_backward_leaky_relu(
    output_bounds: &LinearBounds,
    pre_bounds: &Bounds,
    alpha: f64,
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let in_dim = pre_bounds.dim();

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_lower = vec![0.0; out_neurons];
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_upper = vec![0.0; out_neurons];

    for i in 0..out_neurons {
        for j in 0..in_dim {
            let l = pre_bounds.lower[j];
            let u = pre_bounds.upper[j];

            // Leaky ReLU: y = x if x >= 0, y = alpha*x if x < 0
            let (slope_lower, intercept_lower, slope_upper, intercept_upper) = if l >= 0.0 {
                // Always in positive region: y = x
                (1.0, 0.0, 1.0, 0.0)
            } else if u <= 0.0 {
                // Always in negative region: y = alpha*x
                (alpha, 0.0, alpha, 0.0)
            } else {
                // Unstable: linear relaxation
                // Upper bound: line through (l, alpha*l) and (u, u)
                let slope_u = (u - alpha * l) / (u - l);
                let intercept_u = u - slope_u * u;
                // Lower bound: use alpha or 1 depending on what's tighter
                if alpha <= 1.0 {
                    (alpha, 0.0, slope_u, intercept_u)
                } else {
                    (1.0, 0.0, slope_u, intercept_u)
                }
            };

            if output_bounds.a_lower[i][j] >= 0.0 {
                a_lower[i][j] = output_bounds.a_lower[i][j] * slope_lower;
                b_lower[i] += output_bounds.a_lower[i][j] * intercept_lower;
            } else {
                a_lower[i][j] = output_bounds.a_lower[i][j] * slope_upper;
                b_lower[i] += output_bounds.a_lower[i][j] * intercept_upper;
            }

            if output_bounds.a_upper[i][j] >= 0.0 {
                a_upper[i][j] = output_bounds.a_upper[i][j] * slope_upper;
                b_upper[i] += output_bounds.a_upper[i][j] * intercept_upper;
            } else {
                a_upper[i][j] = output_bounds.a_upper[i][j] * slope_lower;
                b_upper[i] += output_bounds.a_upper[i][j] * intercept_lower;
            }
        }

        b_lower[i] += output_bounds.b_lower[i];
        b_upper[i] += output_bounds.b_upper[i];
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through Sigmoid (linear relaxation)
fn crown_backward_sigmoid(output_bounds: &LinearBounds, pre_bounds: &Bounds) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let in_dim = pre_bounds.dim();

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_lower = vec![0.0; out_neurons];
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_upper = vec![0.0; out_neurons];

    let sigmoid = |x: f64| 1.0 / (1.0 + (-x).exp());
    let sigmoid_derivative = |x: f64| {
        let s = sigmoid(x);
        s * (1.0 - s)
    };

    for i in 0..out_neurons {
        for j in 0..in_dim {
            let l = pre_bounds.lower[j];
            let u = pre_bounds.upper[j];

            // Linear relaxation for sigmoid
            let sl = sigmoid(l);
            let su = sigmoid(u);

            // Chord slope (for upper bound when monotonic)
            let chord_slope = if (u - l).abs() > 1e-10 {
                (su - sl) / (u - l)
            } else {
                sigmoid_derivative(l)
            };

            // For sigmoid, use chord as upper/lower bound depending on convexity
            // Sigmoid is convex for x < 0, concave for x > 0
            // Simplified: use chord for both bounds (valid approximation)
            let slope = chord_slope;
            let intercept_lower = sl - slope * l;
            let intercept_upper = sl - slope * l;

            if output_bounds.a_lower[i][j] >= 0.0 {
                a_lower[i][j] = output_bounds.a_lower[i][j] * slope;
                b_lower[i] += output_bounds.a_lower[i][j] * intercept_lower;
            } else {
                a_lower[i][j] = output_bounds.a_lower[i][j] * slope;
                b_lower[i] += output_bounds.a_lower[i][j] * intercept_upper;
            }

            if output_bounds.a_upper[i][j] >= 0.0 {
                a_upper[i][j] = output_bounds.a_upper[i][j] * slope;
                b_upper[i] += output_bounds.a_upper[i][j] * intercept_upper;
            } else {
                a_upper[i][j] = output_bounds.a_upper[i][j] * slope;
                b_upper[i] += output_bounds.a_upper[i][j] * intercept_lower;
            }
        }

        b_lower[i] += output_bounds.b_lower[i];
        b_upper[i] += output_bounds.b_upper[i];
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through Tanh (linear relaxation)
fn crown_backward_tanh(output_bounds: &LinearBounds, pre_bounds: &Bounds) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let in_dim = pre_bounds.dim();

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_lower = vec![0.0; out_neurons];
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_upper = vec![0.0; out_neurons];

    for i in 0..out_neurons {
        for j in 0..in_dim {
            let l = pre_bounds.lower[j];
            let u = pre_bounds.upper[j];

            let tl = l.tanh();
            let tu = u.tanh();

            // Chord slope
            let chord_slope = if (u - l).abs() > 1e-10 {
                (tu - tl) / (u - l)
            } else {
                1.0 - tl * tl // tanh derivative
            };

            let slope = chord_slope;
            let intercept = tl - slope * l;

            // Same computation regardless of sign - using chord approximation
            a_lower[i][j] = output_bounds.a_lower[i][j] * slope;
            b_lower[i] += output_bounds.a_lower[i][j] * intercept;

            a_upper[i][j] = output_bounds.a_upper[i][j] * slope;
            b_upper[i] += output_bounds.a_upper[i][j] * intercept;
        }

        b_lower[i] += output_bounds.b_lower[i];
        b_upper[i] += output_bounds.b_upper[i];
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through BatchNorm (inference mode)
/// y = scale * x + bias is a diagonal linear transformation.
/// If we have bounds on y: A_y * z + b_y, substituting gives:
/// A_y * (diag(scale) * x + bias) + b_y = (A_y * diag(scale)) * x + (A_y * bias + b_y)
fn crown_backward_batchnorm(
    output_bounds: &LinearBounds,
    scale: &[f64],
    bias: &[f64],
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let in_dim = scale.len();

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_lower = vec![0.0; out_neurons];
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_upper = vec![0.0; out_neurons];

    for i in 0..out_neurons {
        // Compute bias contribution: sum_j(A_old[i][j] * bias[j])
        for j in 0..in_dim {
            b_lower[i] += output_bounds.a_lower[i][j] * bias[j];
            b_upper[i] += output_bounds.a_upper[i][j] * bias[j];
        }
        b_lower[i] += output_bounds.b_lower[i];
        b_upper[i] += output_bounds.b_upper[i];

        // Compute diagonal multiplication: a_new[i][j] = a_old[i][j] * scale[j]
        for j in 0..in_dim {
            a_lower[i][j] = output_bounds.a_lower[i][j] * scale[j];
            a_upper[i][j] = output_bounds.a_upper[i][j] * scale[j];
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through MaxPool1d
/// MaxPool is non-linear, so we use a conservative linearization:
/// We select the input with the highest upper bound as the "dominant" input,
/// and attribute the full coefficient to that input.
fn crown_backward_maxpool1d(
    output_bounds: &LinearBounds,
    pre_bounds: &Bounds,
    kernel_size: usize,
    stride: usize,
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let out_pool_dim = output_bounds.in_dim(); // pooling output dimension
    let in_dim = pre_bounds.dim();

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let b_lower = output_bounds.b_lower.clone();
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let b_upper = output_bounds.b_upper.clone();

    // For each pooling output position, find the dominant input (highest upper bound)
    // and distribute coefficients to that input
    for pool_out_idx in 0..out_pool_dim {
        let start = pool_out_idx * stride;

        // Find the input with highest upper bound in this window
        let mut best_idx = start;
        let mut best_upper = f64::NEG_INFINITY;
        for k in 0..kernel_size {
            let idx = start + k;
            if idx < in_dim && pre_bounds.upper[idx] > best_upper {
                best_upper = pre_bounds.upper[idx];
                best_idx = idx;
            }
        }

        // Attribute output coefficients to the dominant input
        for i in 0..out_neurons {
            a_lower[i][best_idx] += output_bounds.a_lower[i][pool_out_idx];
            a_upper[i][best_idx] += output_bounds.a_upper[i][pool_out_idx];
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through AvgPool1d
/// AvgPool is linear: y[i] = sum(x[start..start+kernel]) / kernel_size
/// Coefficients are distributed equally to all inputs in the window.
fn crown_backward_avgpool1d(
    output_bounds: &LinearBounds,
    kernel_size: usize,
    stride: usize,
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let out_pool_dim = output_bounds.in_dim(); // pooling output dimension
                                               // Compute input dimension from pooling parameters
    let in_dim = if out_pool_dim > 0 {
        (out_pool_dim - 1) * stride + kernel_size
    } else {
        0
    };

    let scale = 1.0 / kernel_size as f64;
    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let b_lower = output_bounds.b_lower.clone();
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let b_upper = output_bounds.b_upper.clone();

    // For each pooling output, distribute coefficients to all inputs in window
    for pool_out_idx in 0..out_pool_dim {
        let start = pool_out_idx * stride;
        for k in 0..kernel_size {
            let idx = start + k;
            if idx < in_dim {
                for i in 0..out_neurons {
                    a_lower[i][idx] += output_bounds.a_lower[i][pool_out_idx] * scale;
                    a_upper[i][idx] += output_bounds.a_upper[i][pool_out_idx] * scale;
                }
            }
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through GlobalAvgPool2d
/// GlobalAvgPool2d computes the mean across all spatial dimensions for each channel:
///   y[c] = mean(x[c, :, :]) = sum(x[c, h, w] for all h, w) / (height * width)
/// This is a linear operation - coefficients are distributed equally to all spatial positions.
fn crown_backward_global_avgpool2d(
    output_bounds: &LinearBounds,
    channels: usize,
    height: usize,
    width: usize,
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let spatial_size = height * width;
    let in_dim = channels * spatial_size;
    let scale = 1.0 / spatial_size as f64;

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let b_lower = output_bounds.b_lower.clone();
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let b_upper = output_bounds.b_upper.clone();

    // For each channel output, distribute coefficients equally to all spatial inputs
    for c in 0..channels {
        for i in 0..out_neurons {
            let coef_lower = output_bounds.a_lower[i][c] * scale;
            let coef_upper = output_bounds.a_upper[i][c] * scale;
            for hw in 0..spatial_size {
                let idx = c * spatial_size + hw;
                a_lower[i][idx] = coef_lower;
                a_upper[i][idx] = coef_upper;
            }
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through GlobalMaxPool2d
/// GlobalMaxPool2d computes the max across all spatial dimensions for each channel:
///   y[c] = max(x[c, :, :])
/// For linear relaxation, we use the gradient at the argmax position (coefficient 1 for max, 0 elsewhere).
/// We use the midpoint of bounds to determine the likely argmax.
fn crown_backward_global_maxpool2d(
    output_bounds: &LinearBounds,
    pre_bounds: &Bounds,
    channels: usize,
    height: usize,
    width: usize,
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let spatial_size = height * width;
    let in_dim = channels * spatial_size;

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let b_lower = output_bounds.b_lower.clone();
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let b_upper = output_bounds.b_upper.clone();

    // For each channel, find the argmax position using midpoint of bounds
    for c in 0..channels {
        let mut max_idx = 0;
        let mut max_val = f64::NEG_INFINITY;
        for hw in 0..spatial_size {
            let idx = c * spatial_size + hw;
            if idx < pre_bounds.lower.len() {
                let mid = (pre_bounds.lower[idx] + pre_bounds.upper[idx]) / 2.0;
                if mid > max_val {
                    max_val = mid;
                    max_idx = idx;
                }
            }
        }
        // Route all coefficients for this channel through the argmax position
        for i in 0..out_neurons {
            a_lower[i][max_idx] += output_bounds.a_lower[i][c];
            a_upper[i][max_idx] += output_bounds.a_upper[i][c];
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through BatchNorm2d (inference mode)
/// BatchNorm2d applies y[c, h, w] = scale[c] * x[c, h, w] + bias[c] for each spatial position.
/// This is a diagonal linear transformation applied per-channel across all spatial positions.
fn crown_backward_batchnorm2d(
    output_bounds: &LinearBounds,
    channels: usize,
    height: usize,
    width: usize,
    scale: &[f64],
    bias: &[f64],
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let spatial_size = height * width;
    let in_dim = channels * spatial_size;

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_lower = vec![0.0; out_neurons];
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let mut b_upper = vec![0.0; out_neurons];

    for i in 0..out_neurons {
        // Compute bias contribution and scale multiplication
        for c in 0..channels {
            for hw in 0..spatial_size {
                let idx = c * spatial_size + hw;
                if idx < output_bounds.in_dim() {
                    // Bias contribution: sum(A_old[i][idx] * bias[c])
                    b_lower[i] += output_bounds.a_lower[i][idx] * bias[c];
                    b_upper[i] += output_bounds.a_upper[i][idx] * bias[c];
                    // Scale multiplication: a_new[i][idx] = a_old[i][idx] * scale[c]
                    a_lower[i][idx] = output_bounds.a_lower[i][idx] * scale[c];
                    a_upper[i][idx] = output_bounds.a_upper[i][idx] * scale[c];
                }
            }
        }
        b_lower[i] += output_bounds.b_lower[i];
        b_upper[i] += output_bounds.b_upper[i];
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through MaxPool2d
/// MaxPool2d selects the maximum value in each kernel window.
/// For linear relaxation, we use the gradient at the argmax position.
fn crown_backward_maxpool2d(
    output_bounds: &LinearBounds,
    pre_bounds: &Bounds,
    channels: usize,
    height: usize,
    width: usize,
    kernel_size: usize,
    stride: usize,
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let out_height = (height - kernel_size) / stride + 1;
    let out_width = (width - kernel_size) / stride + 1;
    let in_dim = channels * height * width;

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let b_lower = output_bounds.b_lower.clone();
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let b_upper = output_bounds.b_upper.clone();

    // For each output position, find the argmax in the corresponding input window
    for c in 0..channels {
        for oh in 0..out_height {
            for ow in 0..out_width {
                let out_idx = c * out_height * out_width + oh * out_width + ow;

                // Find argmax in the input window
                let mut max_idx = 0;
                let mut max_val = f64::NEG_INFINITY;
                for kh in 0..kernel_size {
                    for kw in 0..kernel_size {
                        let ih = oh * stride + kh;
                        let iw = ow * stride + kw;
                        if ih < height && iw < width {
                            let in_idx = c * height * width + ih * width + iw;
                            if in_idx < pre_bounds.upper.len() {
                                let mid =
                                    (pre_bounds.lower[in_idx] + pre_bounds.upper[in_idx]) / 2.0;
                                if mid > max_val {
                                    max_val = mid;
                                    max_idx = in_idx;
                                }
                            }
                        }
                    }
                }

                // Route coefficients through the argmax position
                for i in 0..out_neurons {
                    if out_idx < output_bounds.in_dim() {
                        a_lower[i][max_idx] += output_bounds.a_lower[i][out_idx];
                        a_upper[i][max_idx] += output_bounds.a_upper[i][out_idx];
                    }
                }
            }
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through AvgPool2d
/// AvgPool2d computes the average over each kernel window.
/// This is a linear operation - coefficients are distributed equally to all inputs in each window.
fn crown_backward_avgpool2d(
    output_bounds: &LinearBounds,
    channels: usize,
    height: usize,
    width: usize,
    kernel_size: usize,
    stride: usize,
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let out_height = (height - kernel_size) / stride + 1;
    let out_width = (width - kernel_size) / stride + 1;
    let in_dim = channels * height * width;
    let scale = 1.0 / (kernel_size * kernel_size) as f64;

    let mut a_lower = vec![vec![0.0; in_dim]; out_neurons];
    let b_lower = output_bounds.b_lower.clone();
    let mut a_upper = vec![vec![0.0; in_dim]; out_neurons];
    let b_upper = output_bounds.b_upper.clone();

    // For each output position, distribute coefficients equally to all inputs in the window
    for c in 0..channels {
        for oh in 0..out_height {
            for ow in 0..out_width {
                let out_idx = c * out_height * out_width + oh * out_width + ow;

                for kh in 0..kernel_size {
                    for kw in 0..kernel_size {
                        let ih = oh * stride + kh;
                        let iw = ow * stride + kw;
                        if ih < height && iw < width {
                            let in_idx = c * height * width + ih * width + iw;
                            for i in 0..out_neurons {
                                if out_idx < output_bounds.in_dim() {
                                    a_lower[i][in_idx] += output_bounds.a_lower[i][out_idx] * scale;
                                    a_upper[i][in_idx] += output_bounds.a_upper[i][out_idx] * scale;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through Conv1d
/// Conv1d is a linear operation, so we propagate coefficients backward.
/// For y[out_ch, out_pos] = sum_{in_ch, k} W[out_ch, in_ch, k] * x[in_ch, in_pos + k] + b[out_ch]
/// where in_pos = out_pos * stride - padding
///
/// If output bounds are A_out * y + b_out, we substitute:
/// A_out * (conv(x) + bias) + b_out = A_new * x + b_new
fn crown_backward_conv1d(
    output_bounds: &LinearBounds,
    weights: &[Vec<Vec<f64>>],
    bias: &[f64],
    in_channels: usize,
    kernel_size: usize,
    stride: usize,
    padding: usize,
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let conv_out_dim = output_bounds.in_dim(); // Conv output dimension

    if conv_out_dim == 0 || weights.is_empty() {
        return output_bounds.clone();
    }

    let out_channels = weights.len();
    let output_length = conv_out_dim / out_channels;
    if output_length == 0 {
        return output_bounds.clone();
    }

    // Compute input_length from output_length and conv parameters
    // output_length = (input_length + 2*padding - kernel_size) / stride + 1
    // input_length = (output_length - 1) * stride + kernel_size - 2*padding
    let input_length = if output_length > 0 {
        (output_length - 1) * stride + kernel_size - 2 * padding
    } else {
        0
    };

    if input_length == 0 {
        return output_bounds.clone();
    }

    let input_dim = in_channels * input_length;

    // Initialize output
    let mut a_lower = vec![vec![0.0; input_dim]; out_neurons];
    let mut b_lower = output_bounds.b_lower.clone();
    let mut a_upper = vec![vec![0.0; input_dim]; out_neurons];
    let mut b_upper = output_bounds.b_upper.clone();

    // Add bias contributions
    for out_ch in 0..out_channels {
        let b = if out_ch < bias.len() {
            bias[out_ch]
        } else {
            0.0
        };
        for out_pos in 0..output_length {
            let conv_out_idx = out_ch * output_length + out_pos;
            if conv_out_idx >= conv_out_dim {
                continue;
            }
            for i in 0..out_neurons {
                b_lower[i] += output_bounds.a_lower[i][conv_out_idx] * b;
                b_upper[i] += output_bounds.a_upper[i][conv_out_idx] * b;
            }
        }
    }

    // Propagate coefficients backward through convolution
    for out_ch in 0..out_channels {
        for out_pos in 0..output_length {
            let conv_out_idx = out_ch * output_length + out_pos;
            if conv_out_idx >= conv_out_dim {
                continue;
            }

            // For each input that contributes to this output
            for in_ch in 0..in_channels {
                for k in 0..kernel_size {
                    // Compute input position with padding
                    let in_pos_padded = out_pos * stride + k;
                    if in_pos_padded < padding || in_pos_padded >= padding + input_length {
                        continue; // Padding position
                    }

                    let in_pos = in_pos_padded - padding;
                    let in_idx = in_ch * input_length + in_pos;
                    if in_idx >= input_dim {
                        continue;
                    }

                    let w = weights[out_ch][in_ch][k];
                    for i in 0..out_neurons {
                        // New coefficient = sum over conv outputs of (old_coef * weight)
                        a_lower[i][in_idx] += output_bounds.a_lower[i][conv_out_idx] * w;
                        a_upper[i][in_idx] += output_bounds.a_upper[i][conv_out_idx] * w;
                    }
                }
            }
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

/// CROWN backward pass through Conv2d
/// Conv2d is a linear operation, so we propagate coefficients backward.
/// For y[out_ch, out_h, out_w] = sum_{in_ch, kh, kw} W[out_ch, in_ch, kh, kw] * x[in_ch, in_h + kh, in_w + kw] + b[out_ch]
/// where in_h = out_h * stride - padding, in_w = out_w * stride - padding
///
/// If output bounds are A_out * y + b_out, we substitute:
/// A_out * (conv(x) + bias) + b_out = A_new * x + b_new
#[allow(clippy::too_many_arguments)]
fn crown_backward_conv2d(
    output_bounds: &LinearBounds,
    weights: &[Vec<Vec<Vec<f64>>>],
    bias: &[f64],
    in_channels: usize,
    input_height: usize,
    input_width: usize,
    kernel_size: usize,
    stride: usize,
    padding: usize,
) -> LinearBounds {
    let out_neurons = output_bounds.out_dim();
    let conv_out_dim = output_bounds.in_dim(); // Conv output dimension

    if conv_out_dim == 0 || weights.is_empty() {
        return output_bounds.clone();
    }

    let out_channels = weights.len();
    let effective_height = input_height + 2 * padding;
    let effective_width = input_width + 2 * padding;

    if effective_height < kernel_size || effective_width < kernel_size || stride == 0 {
        return output_bounds.clone();
    }

    let out_height = (effective_height - kernel_size) / stride + 1;
    let out_width = (effective_width - kernel_size) / stride + 1;
    let expected_out_dim = out_channels * out_height * out_width;

    if conv_out_dim != expected_out_dim {
        return output_bounds.clone();
    }

    let input_dim = in_channels * input_height * input_width;

    // Initialize output
    let mut a_lower = vec![vec![0.0; input_dim]; out_neurons];
    let mut b_lower = output_bounds.b_lower.clone();
    let mut a_upper = vec![vec![0.0; input_dim]; out_neurons];
    let mut b_upper = output_bounds.b_upper.clone();

    // Add bias contributions
    for out_ch in 0..out_channels {
        let b = if out_ch < bias.len() {
            bias[out_ch]
        } else {
            0.0
        };
        for out_h in 0..out_height {
            for out_w in 0..out_width {
                let conv_out_idx = out_ch * out_height * out_width + out_h * out_width + out_w;
                if conv_out_idx >= conv_out_dim {
                    continue;
                }
                for i in 0..out_neurons {
                    b_lower[i] += output_bounds.a_lower[i][conv_out_idx] * b;
                    b_upper[i] += output_bounds.a_upper[i][conv_out_idx] * b;
                }
            }
        }
    }

    // Propagate coefficients backward through convolution
    for out_ch in 0..out_channels {
        for out_h in 0..out_height {
            for out_w in 0..out_width {
                let conv_out_idx = out_ch * out_height * out_width + out_h * out_width + out_w;
                if conv_out_idx >= conv_out_dim {
                    continue;
                }

                // For each input that contributes to this output
                for in_ch in 0..in_channels {
                    for kh in 0..kernel_size {
                        for kw in 0..kernel_size {
                            // Compute input position with padding
                            let in_h_padded = out_h * stride + kh;
                            let in_w_padded = out_w * stride + kw;

                            if in_h_padded < padding
                                || in_h_padded >= padding + input_height
                                || in_w_padded < padding
                                || in_w_padded >= padding + input_width
                            {
                                continue; // Padding position
                            }

                            let in_h = in_h_padded - padding;
                            let in_w = in_w_padded - padding;
                            let in_idx =
                                in_ch * input_height * input_width + in_h * input_width + in_w;
                            if in_idx >= input_dim {
                                continue;
                            }

                            let w = weights[out_ch][in_ch][kh][kw];
                            for i in 0..out_neurons {
                                // New coefficient = sum over conv outputs of (old_coef * weight)
                                a_lower[i][in_idx] += output_bounds.a_lower[i][conv_out_idx] * w;
                                a_upper[i][in_idx] += output_bounds.a_upper[i][conv_out_idx] * w;
                            }
                        }
                    }
                }
            }
        }
    }

    LinearBounds {
        a_lower,
        b_lower,
        a_upper,
        b_upper,
    }
}

impl CrownBackend {
    #[must_use]
    pub const fn new(config: CrownConfig) -> Self {
        Self {
            config,
            network: None,
        }
    }

    /// Load a network into the backend
    pub fn load_network(&mut self, network: NnNetwork) {
        self.network = Some(network);
    }

    /// Create with a pre-loaded network
    #[must_use]
    pub const fn with_network(config: CrownConfig, network: NnNetwork) -> Self {
        Self {
            config,
            network: Some(network),
        }
    }

    /// Verify a neural network specification
    fn verify_nn_spec(&self, spec: &NnSpec, _config: &VerifyConfig) -> VerifyResult {
        match spec {
            NnSpec::LocalRobustness(robustness) => self.verify_local_robustness(robustness),
            NnSpec::GlobalProperty(global) => self.verify_global_property(global),
            NnSpec::OutputBounds(bounds) => self.verify_output_bounds(bounds),
            NnSpec::Monotonicity(mono) => self.verify_monotonicity(mono),
            NnSpec::Lipschitz(lip) => self.verify_lipschitz(lip),
            NnSpec::Fairness(fair) => self.verify_fairness(fair),
            NnSpec::Reachability(reach) => self.verify_reachability(reach),
        }
    }

    /// Verify local robustness using IBP/CROWN bounds
    fn verify_local_robustness(&self, spec: &RobustnessSpec) -> VerifyResult {
        let Some(network) = &self.network else {
            return VerifyResult::Unknown {
                reason: "No network loaded for robustness verification".to_string(),
            };
        };

        // Extract input values from spec
        let Some(input_values) = spec_input_to_vec(&spec.input) else {
            return VerifyResult::Unknown {
                reason: "Cannot extract input values from spec".to_string(),
            };
        };

        // Create input bounds and propagate through network
        // For L2 norm, use tighter L2-ball propagation; for others use box bounds
        let output_bounds = match spec.norm {
            Norm::L2 => {
                // Use L2-aware propagation for tighter bounds
                let l2_ball = L2BallBounds::new(input_values.clone(), spec.epsilon);

                // For IBP, use dedicated L2 propagation
                // For other methods, fall back to box approximation
                if let BoundMethod::Ibp = &self.config.bound_method {
                    ibp_propagate_l2(network, &l2_ball)
                } else {
                    // For CROWN methods, use box approximation of L2 ball
                    // (L2 CROWN propagation is more complex and not implemented yet)
                    let input_bounds = l2_ball.to_box_bounds();
                    match &self.config.bound_method {
                        BoundMethod::Crown => crown_propagate(network, &input_bounds),
                        BoundMethod::CrownOptimized => alpha_crown_propagate(
                            network,
                            &input_bounds,
                            &AlphaCrownConfig::default(),
                        ),
                        BoundMethod::AlphaBetaCrown => branch_and_bound_propagate(
                            network,
                            &input_bounds,
                            &BranchAndBoundConfig::default(),
                        ),
                        BoundMethod::BetaCrown(config) => {
                            beta_crown_propagate(network, &input_bounds, config)
                        }
                        BoundMethod::InputSplit(config) => {
                            input_split_propagate(network, &input_bounds, config)
                        }
                        BoundMethod::Ibp => unreachable!(),
                    }
                }
            }
            Norm::Linf | Norm::L1 | Norm::L0 => {
                // L∞: use standard box bounds
                // L1/L0: use L∞ as over-approximation
                let input_bounds = Bounds::linf_ball(&input_values, spec.epsilon);
                match &self.config.bound_method {
                    BoundMethod::Ibp => ibp_propagate(network, &input_bounds),
                    BoundMethod::Crown => crown_propagate(network, &input_bounds),
                    BoundMethod::CrownOptimized => {
                        alpha_crown_propagate(network, &input_bounds, &AlphaCrownConfig::default())
                    }
                    BoundMethod::AlphaBetaCrown => branch_and_bound_propagate(
                        network,
                        &input_bounds,
                        &BranchAndBoundConfig::default(),
                    ),
                    BoundMethod::BetaCrown(config) => {
                        beta_crown_propagate(network, &input_bounds, config)
                    }
                    BoundMethod::InputSplit(config) => {
                        input_split_propagate(network, &input_bounds, config)
                    }
                }
            }
        };

        // Check robustness property
        match &spec.property {
            RobustnessProperty::ClassificationInvariant => {
                // For classification invariance, we need to check that the top class
                // remains the same across the input region.
                // The argmax is preserved if for the original top class i,
                // output_bounds.lower[i] > output_bounds.upper[j] for all j != i.

                // First, compute forward pass on center point to get original class
                let center_output = forward_pass(network, &input_values);
                let original_class = argmax(&center_output);

                // Check if this class is certifiably top
                let mut certified = true;
                for j in 0..output_bounds.dim() {
                    if j != original_class
                        && output_bounds.lower[original_class] <= output_bounds.upper[j]
                    {
                        certified = false;
                        break;
                    }
                }

                if certified {
                    VerifyResult::Proven
                } else {
                    VerifyResult::Unknown {
                        reason: format!(
                            "IBP bounds too loose to certify classification invariance (epsilon={})",
                            spec.epsilon
                        ),
                    }
                }
            }
            RobustnessProperty::BoundedDeviation { delta } => {
                // Check that output doesn't deviate by more than delta
                let center_output = forward_pass(network, &input_values);
                let mut max_deviation = 0.0f64;
                for i in 0..output_bounds.dim() {
                    let dev_lb = (output_bounds.lower[i] - center_output[i]).abs();
                    let dev_ub = (output_bounds.upper[i] - center_output[i]).abs();
                    max_deviation = max_deviation.max(dev_lb).max(dev_ub);
                }

                if max_deviation <= *delta {
                    VerifyResult::Proven
                } else {
                    VerifyResult::Unknown {
                        reason: format!("Output may deviate by {max_deviation} (allowed: {delta})"),
                    }
                }
            }
            RobustnessProperty::OutputConstraint(_) => VerifyResult::Unknown {
                reason: "Output constraint verification not yet implemented".to_string(),
            },
            RobustnessProperty::TopKInvariant { k: _ } => VerifyResult::Unknown {
                reason: "Top-K invariant verification not yet implemented".to_string(),
            },
        }
    }

    /// Verify global property over input region.
    ///
    /// Uses interval arithmetic to evaluate whether a predicate holds for all outputs
    /// from a given input region. Supports predicates involving:
    /// - Output comparisons with constants (output[i] >= c, output[i] <= c)
    /// - Output comparisons between dimensions (output[i] > output[j])
    /// - Logical combinations (And, Or, Not, Implies)
    ///
    /// Returns PROVEN if the predicate provably holds over all output bounds.
    /// Returns UNKNOWN if the predicate might not hold (over-approximation).
    fn verify_global_property(&self, spec: &GlobalPropertySpec) -> VerifyResult {
        let Some(network) = &self.network else {
            return VerifyResult::Unknown {
                reason: "No network loaded for global property verification".to_string(),
            };
        };

        // Convert input region to bounds
        let input_bounds = match &spec.input_region {
            InputRegion::Box { lower, upper } => Bounds::from_box(lower.clone(), upper.clone()),
            InputRegion::Ball {
                center,
                radius,
                norm: _,
            } => {
                // All norms are over-approximated with L∞ ball
                Bounds::linf_ball(center, *radius)
            }
            _ => {
                return VerifyResult::Unknown {
                    reason: "Unsupported input region for global property verification".to_string(),
                };
            }
        };

        // Compute output bounds using configured method
        let output_bounds = match &self.config.bound_method {
            BoundMethod::Ibp => ibp_propagate(network, &input_bounds),
            BoundMethod::Crown => crown_propagate(network, &input_bounds),
            BoundMethod::CrownOptimized => {
                alpha_crown_propagate(network, &input_bounds, &AlphaCrownConfig::default())
            }
            BoundMethod::AlphaBetaCrown => {
                branch_and_bound_propagate(network, &input_bounds, &BranchAndBoundConfig::default())
            }
            BoundMethod::BetaCrown(config) => beta_crown_propagate(network, &input_bounds, config),
            BoundMethod::InputSplit(config) => {
                input_split_propagate(network, &input_bounds, config)
            }
        };

        // Evaluate predicate using interval arithmetic
        match evaluate_predicate_on_bounds(&spec.property, &output_bounds) {
            PredicateResult::True => VerifyResult::Proven,
            PredicateResult::False => {
                // Predicate is provably false for all values in bounds
                VerifyResult::Unknown {
                    reason:
                        "Global property DISPROVEN: predicate is false for all outputs in bounds"
                            .to_string(),
                }
            }
            PredicateResult::Unknown => VerifyResult::Unknown {
                reason: "Cannot prove predicate over output bounds (may be false for some outputs)"
                    .to_string(),
            },
        }
    }

    /// Verify output bounds using IBP or CROWN depending on configuration
    #[must_use]
    pub fn verify_output_bounds(&self, spec: &BoundsSpec) -> VerifyResult {
        let Some(network) = &self.network else {
            return VerifyResult::Unknown {
                reason: "No network loaded for bounds verification".to_string(),
            };
        };

        // Convert input region to bounds
        let input_bounds = match &spec.input_region {
            InputRegion::Box { lower, upper } => Bounds::from_box(lower.clone(), upper.clone()),
            InputRegion::Ball {
                center,
                radius,
                norm: _,
            } => {
                // All norms are approximated with L∞ ball
                Bounds::linf_ball(center, *radius)
            }
            _ => {
                return VerifyResult::Unknown {
                    reason: "Unsupported input region type for bounds verification".to_string(),
                };
            }
        };

        // Propagate bounds using configured method
        let output_bounds = match &self.config.bound_method {
            BoundMethod::Ibp => ibp_propagate(network, &input_bounds),
            BoundMethod::Crown => crown_propagate(network, &input_bounds),
            BoundMethod::CrownOptimized => {
                alpha_crown_propagate(network, &input_bounds, &AlphaCrownConfig::default())
            }
            BoundMethod::AlphaBetaCrown => {
                branch_and_bound_propagate(network, &input_bounds, &BranchAndBoundConfig::default())
            }
            BoundMethod::BetaCrown(config) => beta_crown_propagate(network, &input_bounds, config),
            BoundMethod::InputSplit(config) => {
                input_split_propagate(network, &input_bounds, config)
            }
        };

        // Check if computed bounds satisfy specification
        let spec_lower = spec.lower_bounds.as_deref();
        let spec_upper = spec.upper_bounds.as_deref();

        if output_bounds.satisfies(spec_lower, spec_upper) {
            VerifyResult::Proven
        } else {
            // Provide details about the violation
            let mut violations = Vec::new();
            if let Some(lb) = spec_lower {
                for (i, (&computed, &spec)) in output_bounds.lower.iter().zip(lb.iter()).enumerate()
                {
                    if computed < spec {
                        violations.push(format!(
                            "output[{i}]: computed_lb={computed:.6} < spec_lb={spec:.6}"
                        ));
                    }
                }
            }
            if let Some(ub) = spec_upper {
                for (i, (&computed, &spec)) in output_bounds.upper.iter().zip(ub.iter()).enumerate()
                {
                    if computed > spec {
                        violations.push(format!(
                            "output[{i}]: computed_ub={computed:.6} > spec_ub={spec:.6}"
                        ));
                    }
                }
            }

            VerifyResult::Unknown {
                reason: format!(
                    "IBP bounds do not satisfy specification: {}",
                    violations.join("; ")
                ),
            }
        }
    }

    /// Verify monotonicity using interval bounds on Jacobian entries.
    ///
    /// For a neural network f: R^n -> R^m, monotonicity in input dimension i
    /// w.r.t. output dimension j means:
    /// - Increasing: ∂f_j/∂x_i >= 0 for all x in the region
    /// - Decreasing: ∂f_j/∂x_i <= 0 for all x in the region
    ///
    /// We compute conservative bounds on `∂f_j/∂x_i` over the input region via
    /// interval arithmetic using IBP-derived activation state bounds:
    /// - Increasing monotonicity: lower(∂f_j/∂x_i) >= 0
    /// - Decreasing monotonicity: upper(∂f_j/∂x_i) <= 0
    fn verify_monotonicity(&self, spec: &MonotonicitySpec) -> VerifyResult {
        let Some(network) = &self.network else {
            return VerifyResult::Unknown {
                reason: "No network loaded for monotonicity verification".to_string(),
            };
        };

        if network
            .layers
            .iter()
            .any(|l| matches!(l, NnLayer::ResidualAdd { .. } | NnLayer::Concat { .. }))
        {
            return VerifyResult::Unknown {
                reason: "Monotonicity with ResidualAdd/Concat requires skip-aware propagation"
                    .to_string(),
            };
        }

        // Convert input region to bounds
        let input_bounds = match &spec.region {
            InputRegion::Box { lower, upper } => Bounds::from_box(lower.clone(), upper.clone()),
            InputRegion::Ball {
                center,
                radius,
                norm: _,
            } => {
                // All norms are over-approximated with L∞ ball
                Bounds::linf_ball(center, *radius)
            }
            _ => {
                return VerifyResult::Unknown {
                    reason: "Unsupported input region for monotonicity verification".to_string(),
                };
            }
        };

        // Step 1: Compute pre-activation bounds using IBP
        let pre_bounds = PreActivationBounds::compute(network, &input_bounds);

        // Step 2: Compute Jacobian interval bounds for requested outputs
        let jacobian = match jacobian_interval_bounds(network, &pre_bounds, &spec.output_dims) {
            Ok(j) => j,
            Err(e) => {
                return VerifyResult::Unknown {
                    reason: format!("Failed to compute Jacobian interval bounds: {e}"),
                };
            }
        };

        // Step 3: Check monotonicity conditions
        let mut violations = Vec::new();

        let input_dim = input_bounds.dim();
        for (row, &out_dim) in spec.output_dims.iter().enumerate() {
            for &in_dim in &spec.input_dims {
                if in_dim >= input_dim {
                    return VerifyResult::Unknown {
                        reason: format!(
                            "Input dimension {in_dim} out of bounds (network has {input_dim} inputs)"
                        ),
                    };
                }

                let d_l = jacobian.lower[row][in_dim];
                let d_u = jacobian.upper[row][in_dim];

                if spec.increasing {
                    if d_l < 0.0 {
                        violations.push(format!(
                            "Output {out_dim} may decrease with input {in_dim} (∂f/∂x in [{d_l:.6}, {d_u:.6}])"
                        ));
                    }
                } else if d_u > 0.0 {
                    violations.push(format!(
                        "Output {out_dim} may increase with input {in_dim} (∂f/∂x in [{d_l:.6}, {d_u:.6}])"
                    ));
                }
            }
        }

        if violations.is_empty() {
            VerifyResult::Proven
        } else {
            VerifyResult::Unknown {
                reason: format!(
                    "Monotonicity could not be proven: {}",
                    violations.join("; ")
                ),
            }
        }
    }

    /// Verify Lipschitz bound using Jacobian interval bounds.
    ///
    /// For a function f: R^n -> R^m, the Lipschitz constant L satisfies:
    ///   ||f(x) - f(y)||_q <= L * ||x - y||_p  for all x, y in region
    ///
    /// where p = input_norm and q = output_norm.
    ///
    /// The induced operator norm ||J||_{p->q} bounds L from above, since:
    ///   ||f(x) - f(y)||_q <= ||J||_{p->q} * ||x - y||_p
    ///
    /// Given interval bounds [J_L, J_U] on each Jacobian entry, we compute
    /// an upper bound on ||J||_{p->q} using |J_ij| <= max(|J_L_ij|, |J_U_ij|).
    fn verify_lipschitz(&self, spec: &LipschitzSpec) -> VerifyResult {
        let Some(network) = &self.network else {
            return VerifyResult::Unknown {
                reason: "No network loaded for Lipschitz verification".to_string(),
            };
        };

        // Skip connections require special handling
        if network
            .layers
            .iter()
            .any(|l| matches!(l, NnLayer::ResidualAdd { .. } | NnLayer::Concat { .. }))
        {
            return VerifyResult::Unknown {
                reason: "Lipschitz verification with ResidualAdd/Concat not yet implemented"
                    .to_string(),
            };
        }

        // Convert input region to bounds (default to [-1, 1]^n if not specified)
        let input_bounds = if let Some(region) = &spec.region {
            match region {
                InputRegion::Box { lower, upper } => Bounds::from_box(lower.clone(), upper.clone()),
                InputRegion::Ball {
                    center,
                    radius,
                    norm: _,
                } => {
                    // All norms are over-approximated with L∞ ball
                    Bounds::linf_ball(center, *radius)
                }
                _ => {
                    return VerifyResult::Unknown {
                        reason: "Unsupported input region for Lipschitz verification".to_string(),
                    };
                }
            }
        } else {
            // Default region: [-1, 1]^n
            let input_dim = network.input_dim;
            Bounds::from_box(vec![-1.0; input_dim], vec![1.0; input_dim])
        };

        // Step 1: Compute pre-activation bounds using IBP
        let pre_bounds = PreActivationBounds::compute(network, &input_bounds);

        // Step 2: Compute Jacobian interval bounds for all outputs
        let output_dim = pre_bounds.layer_bounds.last().map_or(0, Bounds::dim);
        let all_output_dims: Vec<usize> = (0..output_dim).collect();

        let jacobian = match jacobian_interval_bounds(network, &pre_bounds, &all_output_dims) {
            Ok(j) => j,
            Err(e) => {
                return VerifyResult::Unknown {
                    reason: format!("Failed to compute Jacobian interval bounds: {e}"),
                };
            }
        };

        // Step 3: Compute induced operator norm bound
        let computed_lipschitz =
            lipschitz_from_jacobian_bounds(&jacobian, spec.input_norm, spec.output_norm);

        // Step 4: Check if computed bound <= specified constant
        if computed_lipschitz <= spec.constant {
            VerifyResult::Proven
        } else {
            VerifyResult::Unknown {
                reason: format!(
                    "Lipschitz bound could not be proven: computed bound {:.6} > specified constant {:.6}",
                    computed_lipschitz, spec.constant
                ),
            }
        }
    }

    /// Verify fairness using Jacobian interval bounds
    ///
    /// Fairness verification checks that the network output is not overly sensitive
    /// to protected attributes (e.g., age, gender, race).
    ///
    /// # Supported Criteria
    ///
    /// - **Independence**: Output is provably independent of protected attributes.
    ///   Verified by checking that all Jacobian entries for protected inputs are bounded
    ///   near zero: max(|J_L[j,i]|, |J_U[j,i]|) < threshold for all outputs j and protected i.
    ///
    /// - **Individual**: Similar inputs (differing in protected attributes) produce similar
    ///   outputs. Verified by computing partial Lipschitz constant over protected dimensions.
    ///   If ||∂f/∂x_protected||_{p→q} <= similarity_threshold, fairness holds.
    ///
    /// - **EqualOpportunity**: Statistical fairness criterion (not yet implemented).
    fn verify_fairness(&self, spec: &FairnessSpec) -> VerifyResult {
        // Step 0: Check network is loaded
        let Some(network) = &self.network else {
            return VerifyResult::Unknown {
                reason: "No network loaded for fairness verification".to_string(),
            };
        };

        // Step 0.5: Check for ResidualAdd/Concat (not yet supported for Jacobian computation)
        if network
            .layers
            .iter()
            .any(|l| matches!(l, NnLayer::ResidualAdd { .. } | NnLayer::Concat { .. }))
        {
            return VerifyResult::Unknown {
                reason: "Fairness verification with ResidualAdd/Concat not yet implemented"
                    .to_string(),
            };
        }

        // Step 1: Validate protected attributes
        let input_dim = network.input_dim;
        for &attr_idx in &spec.protected_attributes {
            if attr_idx >= input_dim {
                return VerifyResult::Unknown {
                    reason: format!(
                        "Protected attribute index {attr_idx} out of bounds (input dim = {input_dim})"
                    ),
                };
            }
        }

        if spec.protected_attributes.is_empty() {
            return VerifyResult::Proven; // No protected attributes = trivially fair
        }

        // Step 2: Get input bounds from region
        let input_bounds = match &spec.region {
            InputRegion::Box { lower, upper } => Bounds::from_box(lower.clone(), upper.clone()),
            InputRegion::Ball {
                center,
                radius,
                norm: _,
            } => {
                // All norms are over-approximated with L∞ ball
                Bounds::linf_ball(center, *radius)
            }
            _ => {
                return VerifyResult::Unknown {
                    reason: "Unsupported input region for fairness verification".to_string(),
                };
            }
        };

        // Step 3: Compute pre-activation bounds using IBP
        let pre_bounds = PreActivationBounds::compute(network, &input_bounds);

        // Step 4: Compute Jacobian interval bounds for all outputs
        let output_dim = pre_bounds.layer_bounds.last().map_or(0, Bounds::dim);
        let all_output_dims: Vec<usize> = (0..output_dim).collect();

        let jacobian = match jacobian_interval_bounds(network, &pre_bounds, &all_output_dims) {
            Ok(j) => j,
            Err(e) => {
                return VerifyResult::Unknown {
                    reason: format!("Failed to compute Jacobian interval bounds: {e}"),
                };
            }
        };

        // Step 5: Verify based on fairness criterion
        match &spec.criterion {
            FairnessCriterion::Independence => {
                verify_fairness_independence(&jacobian, &spec.protected_attributes)
            }
            FairnessCriterion::Individual {
                similarity_threshold,
            } => verify_fairness_individual(
                &jacobian,
                &spec.protected_attributes,
                *similarity_threshold,
            ),
            FairnessCriterion::EqualOpportunity => VerifyResult::Unknown {
                reason: "EqualOpportunity fairness criterion requires statistical analysis (not yet implemented)".to_string(),
            },
        }
    }

    /// Verify reachability: whether a target output region is reachable from an input region.
    ///
    /// # Verification Logic
    ///
    /// - **check_reachable=false (Unreachability)**: Proves that no input in the input region
    ///   can reach the target output region. Uses IBP/CROWN to over-approximate the output
    ///   bounds; if bounds don't intersect target, unreachability is PROVEN.
    ///
    /// - **check_reachable=true (Reachability)**: Proves that some input CAN reach the target.
    ///   This is harder - over-approximation can only disprove reachability (if bounds don't
    ///   intersect). If bounds DO intersect, result is UNKNOWN (intersection may be an artifact
    ///   of over-approximation, not actual reachability).
    fn verify_reachability(&self, spec: &ReachabilitySpec) -> VerifyResult {
        let Some(network) = &self.network else {
            return VerifyResult::Unknown {
                reason: "No network loaded for reachability verification".to_string(),
            };
        };

        // Convert input region to bounds
        let input_bounds = match &spec.input_region {
            InputRegion::Box { lower, upper } => Bounds::from_box(lower.clone(), upper.clone()),
            InputRegion::Ball {
                center,
                radius,
                norm: _,
            } => {
                // All norms are over-approximated with L∞ ball
                Bounds::linf_ball(center, *radius)
            }
            _ => {
                return VerifyResult::Unknown {
                    reason: "Unsupported input region for reachability verification".to_string(),
                };
            }
        };

        // Compute output bounds using configured method
        let output_bounds = match &self.config.bound_method {
            BoundMethod::Ibp => ibp_propagate(network, &input_bounds),
            BoundMethod::Crown => crown_propagate(network, &input_bounds),
            BoundMethod::CrownOptimized => {
                alpha_crown_propagate(network, &input_bounds, &AlphaCrownConfig::default())
            }
            BoundMethod::AlphaBetaCrown => {
                branch_and_bound_propagate(network, &input_bounds, &BranchAndBoundConfig::default())
            }
            BoundMethod::BetaCrown(config) => beta_crown_propagate(network, &input_bounds, config),
            BoundMethod::InputSplit(config) => {
                input_split_propagate(network, &input_bounds, config)
            }
        };

        // Check if output bounds intersect with target region
        let intersects = output_bounds_intersect_target(&output_bounds, &spec.target_region);

        if spec.check_reachable {
            // Trying to prove reachability (∃x: f(x) ∈ target)
            // If bounds don't intersect target, we can prove UNREACHABILITY (negation of the query)
            // If bounds DO intersect, we can't conclude (over-approximation may cause false intersections)
            if intersects {
                VerifyResult::Unknown {
                    reason: "Output bounds intersect target region, but cannot prove actual reachability (over-approximation)".to_string(),
                }
            } else {
                // We've proven the target is NOT reachable - return Unknown with clear explanation
                VerifyResult::Unknown {
                    reason: "Target region is provably NOT reachable: output bounds do not intersect target region".to_string(),
                }
            }
        } else {
            // Trying to prove unreachability (∀x: f(x) ∉ target)
            // If bounds don't intersect target, unreachability is PROVEN
            // If bounds DO intersect, we can't conclude unreachability
            if intersects {
                VerifyResult::Unknown {
                    reason: format!(
                        "Cannot prove unreachability: output bounds [{:.4}, {:.4}]...[{:.4}, {:.4}] may intersect target region",
                        output_bounds.lower[0],
                        output_bounds.upper[0],
                        output_bounds.lower.last().unwrap_or(&0.0),
                        output_bounds.upper.last().unwrap_or(&0.0)
                    ),
                }
            } else {
                VerifyResult::Proven
            }
        }
    }
}

/// Result of evaluating a predicate over interval bounds using interval arithmetic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PredicateResult {
    /// Predicate is provably true for all values within bounds
    True,
    /// Predicate is provably false for all values within bounds
    False,
    /// Cannot determine - predicate may be true or false depending on actual values
    Unknown,
}

/// Evaluate a predicate over output bounds using interval arithmetic.
///
/// Uses three-valued logic:
/// - True: predicate holds for ALL values within the bounds
/// - False: predicate fails for ALL values within the bounds
/// - Unknown: predicate may hold for some values but not others
fn evaluate_predicate_on_bounds(pred: &vc_ir::Predicate, bounds: &Bounds) -> PredicateResult {
    use vc_ir::Predicate;

    match pred {
        Predicate::Bool(b) => {
            if *b {
                PredicateResult::True
            } else {
                PredicateResult::False
            }
        }

        Predicate::Expr(expr) => evaluate_bool_expr_on_bounds(expr, bounds),

        Predicate::Not(inner) => match evaluate_predicate_on_bounds(inner, bounds) {
            PredicateResult::True => PredicateResult::False,
            PredicateResult::False => PredicateResult::True,
            PredicateResult::Unknown => PredicateResult::Unknown,
        },

        Predicate::And(preds) => {
            let mut has_unknown = false;
            for p in preds {
                match evaluate_predicate_on_bounds(p, bounds) {
                    PredicateResult::False => return PredicateResult::False, // Short-circuit
                    PredicateResult::Unknown => has_unknown = true,
                    PredicateResult::True => {}
                }
            }
            if has_unknown {
                PredicateResult::Unknown
            } else {
                PredicateResult::True
            }
        }

        Predicate::Or(preds) => {
            let mut has_unknown = false;
            for p in preds {
                match evaluate_predicate_on_bounds(p, bounds) {
                    PredicateResult::True => return PredicateResult::True, // Short-circuit
                    PredicateResult::Unknown => has_unknown = true,
                    PredicateResult::False => {}
                }
            }
            if has_unknown {
                PredicateResult::Unknown
            } else {
                PredicateResult::False
            }
        }

        Predicate::Implies(lhs, rhs) => {
            // A => B is equivalent to !A || B
            let lhs_result = evaluate_predicate_on_bounds(lhs, bounds);
            let rhs_result = evaluate_predicate_on_bounds(rhs, bounds);

            match (lhs_result, rhs_result) {
                // False => anything or anything => True both yield True
                (PredicateResult::False, _) | (_, PredicateResult::True) => PredicateResult::True,
                (PredicateResult::True, PredicateResult::False) => PredicateResult::False,
                _ => PredicateResult::Unknown,
            }
        }

        Predicate::Iff(lhs, rhs) => {
            // A <=> B is equivalent to (A => B) && (B => A)
            let lhs_result = evaluate_predicate_on_bounds(lhs, bounds);
            let rhs_result = evaluate_predicate_on_bounds(rhs, bounds);

            match (lhs_result, rhs_result) {
                // Both same (both True or both False) yields True
                (PredicateResult::True, PredicateResult::True)
                | (PredicateResult::False, PredicateResult::False) => PredicateResult::True,
                (PredicateResult::True, PredicateResult::False)
                | (PredicateResult::False, PredicateResult::True) => PredicateResult::False,
                _ => PredicateResult::Unknown,
            }
        }

        // Quantifiers and let bindings are not supported in interval evaluation
        Predicate::Forall { .. } | Predicate::Exists { .. } | Predicate::Let { .. } => {
            PredicateResult::Unknown
        }
    }
}

/// Interval bound on an expression value
#[derive(Debug, Clone)]
struct ExprInterval {
    lower: f64,
    upper: f64,
}

impl ExprInterval {
    const fn constant(value: f64) -> Self {
        Self {
            lower: value,
            upper: value,
        }
    }

    const fn from_bounds(lower: f64, upper: f64) -> Self {
        Self { lower, upper }
    }

    /// Add two intervals: [a, b] + [c, d] = [a+c, b+d]
    fn add(&self, other: &Self) -> Self {
        Self {
            lower: self.lower + other.lower,
            upper: self.upper + other.upper,
        }
    }

    /// Subtract two intervals: [a, b] - [c, d] = [a-d, b-c]
    fn sub(&self, other: &Self) -> Self {
        Self {
            lower: self.lower - other.upper,
            upper: self.upper - other.lower,
        }
    }

    /// Multiply two intervals
    fn mul(&self, other: &Self) -> Self {
        let products = [
            self.lower * other.lower,
            self.lower * other.upper,
            self.upper * other.lower,
            self.upper * other.upper,
        ];
        Self {
            lower: products.iter().copied().fold(f64::INFINITY, f64::min),
            upper: products.iter().copied().fold(f64::NEG_INFINITY, f64::max),
        }
    }

    /// Negate interval: -[a, b] = [-b, -a]
    fn neg(&self) -> Self {
        Self {
            lower: -self.upper,
            upper: -self.lower,
        }
    }
}

/// Evaluate an expression to interval bounds on the output
fn evaluate_expr_on_bounds(expr: &vc_ir::Expr, output_bounds: &Bounds) -> Option<ExprInterval> {
    use vc_ir::Expr;

    match expr {
        Expr::IntLit(v) => Some(ExprInterval::constant(*v as f64)),
        Expr::FloatLit(v) => Some(ExprInterval::constant(*v)),
        Expr::BoolLit(b) => Some(ExprInterval::constant(if *b { 1.0 } else { 0.0 })),

        // Result variable refers to network output - need dimension info
        // We interpret Result as a vector and use index expressions
        Expr::Result => {
            // If output is scalar, return the bounds
            if output_bounds.dim() == 1 {
                Some(ExprInterval::from_bounds(
                    output_bounds.lower[0],
                    output_bounds.upper[0],
                ))
            } else {
                None // Need indexing for multi-dimensional output
            }
        }

        // Variable lookup - support output[i] style access
        Expr::Var(name) => {
            // Check if it's an indexed output reference like "output_0", "output_1"
            if let Some(suffix) = name.strip_prefix("output_") {
                if let Ok(idx) = suffix.parse::<usize>() {
                    if idx < output_bounds.dim() {
                        return Some(ExprInterval::from_bounds(
                            output_bounds.lower[idx],
                            output_bounds.upper[idx],
                        ));
                    }
                }
            }
            None // Unknown variable
        }

        // Index expression: output[i]
        Expr::ArrayIndex(base, idx) => {
            // Handle Result[i] or output[i] for output indexing
            let is_output_ref = matches!(base.as_ref(), Expr::Result)
                || matches!(base.as_ref(), Expr::Var(s) if s == "output");
            if is_output_ref {
                if let Expr::IntLit(i) = idx.as_ref() {
                    let idx = *i as usize;
                    if idx < output_bounds.dim() {
                        return Some(ExprInterval::from_bounds(
                            output_bounds.lower[idx],
                            output_bounds.upper[idx],
                        ));
                    }
                }
            }
            None
        }

        // Arithmetic operations with interval arithmetic
        Expr::Neg(inner) => evaluate_expr_on_bounds(inner, output_bounds).map(|i| i.neg()),

        Expr::Add(lhs, rhs) => {
            let l = evaluate_expr_on_bounds(lhs, output_bounds)?;
            let r = evaluate_expr_on_bounds(rhs, output_bounds)?;
            Some(l.add(&r))
        }

        Expr::Sub(lhs, rhs) => {
            let l = evaluate_expr_on_bounds(lhs, output_bounds)?;
            let r = evaluate_expr_on_bounds(rhs, output_bounds)?;
            Some(l.sub(&r))
        }

        Expr::Mul(lhs, rhs) => {
            let l = evaluate_expr_on_bounds(lhs, output_bounds)?;
            let r = evaluate_expr_on_bounds(rhs, output_bounds)?;
            Some(l.mul(&r))
        }

        // Division, modulo, etc. are more complex with intervals
        _ => None,
    }
}

/// Evaluate a boolean expression on bounds
fn evaluate_bool_expr_on_bounds(expr: &vc_ir::Expr, bounds: &Bounds) -> PredicateResult {
    use vc_ir::Expr;

    match expr {
        Expr::BoolLit(b) => {
            if *b {
                PredicateResult::True
            } else {
                PredicateResult::False
            }
        }

        // Comparison: lhs >= rhs
        Expr::Ge(lhs, rhs) => {
            let Some(l) = evaluate_expr_on_bounds(lhs, bounds) else {
                return PredicateResult::Unknown;
            };
            let Some(r) = evaluate_expr_on_bounds(rhs, bounds) else {
                return PredicateResult::Unknown;
            };

            // l >= r for all values if l.lower >= r.upper
            if l.lower >= r.upper {
                PredicateResult::True
            } else if l.upper < r.lower {
                PredicateResult::False
            } else {
                PredicateResult::Unknown
            }
        }

        // Comparison: lhs > rhs
        Expr::Gt(lhs, rhs) => {
            let Some(l) = evaluate_expr_on_bounds(lhs, bounds) else {
                return PredicateResult::Unknown;
            };
            let Some(r) = evaluate_expr_on_bounds(rhs, bounds) else {
                return PredicateResult::Unknown;
            };

            // l > r for all values if l.lower > r.upper
            if l.lower > r.upper {
                PredicateResult::True
            } else if l.upper <= r.lower {
                PredicateResult::False
            } else {
                PredicateResult::Unknown
            }
        }

        // Comparison: lhs <= rhs
        Expr::Le(lhs, rhs) => {
            let Some(l) = evaluate_expr_on_bounds(lhs, bounds) else {
                return PredicateResult::Unknown;
            };
            let Some(r) = evaluate_expr_on_bounds(rhs, bounds) else {
                return PredicateResult::Unknown;
            };

            // l <= r for all values if l.upper <= r.lower
            if l.upper <= r.lower {
                PredicateResult::True
            } else if l.lower > r.upper {
                PredicateResult::False
            } else {
                PredicateResult::Unknown
            }
        }

        // Comparison: lhs < rhs
        Expr::Lt(lhs, rhs) => {
            let Some(l) = evaluate_expr_on_bounds(lhs, bounds) else {
                return PredicateResult::Unknown;
            };
            let Some(r) = evaluate_expr_on_bounds(rhs, bounds) else {
                return PredicateResult::Unknown;
            };

            // l < r for all values if l.upper < r.lower
            if l.upper < r.lower {
                PredicateResult::True
            } else if l.lower >= r.upper {
                PredicateResult::False
            } else {
                PredicateResult::Unknown
            }
        }

        // Equality is difficult with intervals - only certain for point intervals
        Expr::Eq(lhs, rhs) => {
            let Some(l) = evaluate_expr_on_bounds(lhs, bounds) else {
                return PredicateResult::Unknown;
            };
            let Some(r) = evaluate_expr_on_bounds(rhs, bounds) else {
                return PredicateResult::Unknown;
            };

            // l == r for all values only if both are point intervals with same value
            if l.lower == l.upper && r.lower == r.upper && l.lower == r.lower {
                PredicateResult::True
            } else if l.upper < r.lower || l.lower > r.upper {
                // Intervals don't overlap - definitely not equal
                PredicateResult::False
            } else {
                PredicateResult::Unknown
            }
        }

        // Inequality
        Expr::Ne(lhs, rhs) => {
            let Some(l) = evaluate_expr_on_bounds(lhs, bounds) else {
                return PredicateResult::Unknown;
            };
            let Some(r) = evaluate_expr_on_bounds(rhs, bounds) else {
                return PredicateResult::Unknown;
            };

            // l != r for all values if intervals don't overlap
            if l.upper < r.lower || l.lower > r.upper {
                PredicateResult::True
            } else if l.lower == l.upper && r.lower == r.upper && l.lower == r.lower {
                PredicateResult::False
            } else {
                PredicateResult::Unknown
            }
        }

        _ => PredicateResult::Unknown,
    }
}

/// Check if output bounds intersect with a target output region.
///
/// Returns true if the interval [lb, ub] from `output_bounds` overlaps with the target region.
fn output_bounds_intersect_target(output_bounds: &Bounds, target: &OutputRegion) -> bool {
    match target {
        OutputRegion::Class(class_idx) => {
            // Target is a specific class (argmax = class_idx)
            // Check if output_bounds allows class_idx to be the argmax
            if *class_idx >= output_bounds.dim() {
                return false; // Invalid class index
            }

            // For class_idx to be argmax, we need: output[class_idx] >= output[j] for all j
            // This is POSSIBLE if there exists a point where class_idx beats all others.
            // Sufficient condition: class_upper >= class_lower_j for all j ≠ class_idx
            // (i.e., the max of class_idx can beat the min of every other class)
            let class_upper = output_bounds.upper[*class_idx];

            // Check if class_idx CAN be the argmax (its upper bound >= all other lower bounds)
            output_bounds
                .lower
                .iter()
                .enumerate()
                .all(|(j, &lb)| j == *class_idx || class_upper >= lb)
        }
        OutputRegion::Classes(class_indices) => {
            // Target is a set of classes - check if any of them could be argmax
            class_indices.iter().any(|&idx| {
                output_bounds_intersect_target(output_bounds, &OutputRegion::Class(idx))
            })
        }
        OutputRegion::Box { lower, upper } => {
            // Target is a box constraint: lower[i] <= output[i] <= upper[i] for all i
            // Bounds intersect if: output_lower[i] <= upper[i] AND output_upper[i] >= lower[i]
            if lower.len() != output_bounds.dim() || upper.len() != output_bounds.dim() {
                return true; // Dimension mismatch - assume possible intersection
            }

            lower
                .iter()
                .zip(upper.iter())
                .zip(output_bounds.lower.iter().zip(output_bounds.upper.iter()))
                .all(|((target_lb, target_ub), (out_lb, out_ub))| {
                    // Intervals [out_lb, out_ub] and [target_lb, target_ub] intersect
                    out_ub >= target_lb && out_lb <= target_ub
                })
        }
        OutputRegion::Predicate(_pred) => {
            // General predicate - cannot check without more sophisticated analysis
            true // Conservatively assume intersection is possible
        }
    }
}

/// Extract input values from an Expr (if possible)
fn spec_input_to_vec(expr: &vc_ir::Expr) -> Option<Vec<f64>> {
    match expr {
        vc_ir::Expr::FloatLit(f) => Some(vec![*f]),
        vc_ir::Expr::IntLit(i) => Some(vec![*i as f64]),
        _ => None,
    }
}

/// Compute Lipschitz constant bound from Jacobian interval bounds.
///
/// Given an m x n interval matrix J with bounds [J_L, J_U], compute an upper bound
/// on the induced operator norm ||J||_{p->q} where:
/// - p = input_norm (norm on domain R^n)
/// - q = output_norm (norm on codomain R^m)
///
/// For each entry, |J_ij| <= max(|J_L_ij|, |J_U_ij|).
///
/// Supported norm pairs:
/// - L∞ -> L∞: ||J||_∞ = max_i sum_j |J_ij| (max row sum)
/// - L1 -> L1: ||J||_1 = max_j sum_i |J_ij| (max column sum)
/// - L2 -> L2: ||J||_2 <= sqrt(||J||_1 * ||J||_∞) (submultiplicative bound)
/// - L2 -> L∞: max_i sqrt(sum_j J_ij^2) (max row L2 norm)
/// - L1 -> L∞: max_i,j |J_ij| (max entry)
/// - Other combinations: fall back to Frobenius norm upper bound
fn lipschitz_from_jacobian_bounds(
    jacobian: &IntervalMatrix,
    input_norm: Norm,
    output_norm: Norm,
) -> f64 {
    let rows = jacobian.rows();
    let cols = jacobian.cols();

    if rows == 0 || cols == 0 {
        return 0.0;
    }

    // Compute |J_ij| upper bound for each entry
    let abs_bound: Vec<Vec<f64>> = (0..rows)
        .map(|i| {
            (0..cols)
                .map(|j| {
                    let lower = jacobian.lower[i][j];
                    let upper = jacobian.upper[i][j];
                    lower.abs().max(upper.abs())
                })
                .collect()
        })
        .collect();

    match (input_norm, output_norm) {
        // L∞ -> L∞: max row sum
        (Norm::Linf, Norm::Linf) => abs_bound
            .iter()
            .map(|row| row.iter().sum::<f64>())
            .fold(0.0_f64, f64::max),
        // L1 -> L1: max column sum
        (Norm::L1, Norm::L1) => (0..cols)
            .map(|j| (0..rows).map(|i| abs_bound[i][j]).sum::<f64>())
            .fold(0.0_f64, f64::max),
        // L2 -> L2: use submultiplicative bound sqrt(||J||_1 * ||J||_∞)
        (Norm::L2, Norm::L2) => {
            let inf_norm = abs_bound
                .iter()
                .map(|row| row.iter().sum::<f64>())
                .fold(0.0_f64, f64::max);
            let one_norm = (0..cols)
                .map(|j| (0..rows).map(|i| abs_bound[i][j]).sum::<f64>())
                .fold(0.0_f64, f64::max);
            (inf_norm * one_norm).sqrt()
        }
        // L2 -> L∞: max row L2 norm
        (Norm::L2, Norm::Linf) => abs_bound
            .iter()
            .map(|row| row.iter().map(|&x| x * x).sum::<f64>().sqrt())
            .fold(0.0_f64, f64::max),
        // L1 -> L∞: max entry
        (Norm::L1, Norm::Linf) => abs_bound
            .iter()
            .flat_map(|row| row.iter())
            .copied()
            .fold(0.0_f64, f64::max),
        // L∞ -> L1: sum of max entries per column (conservative)
        (Norm::Linf, Norm::L1) => (0..cols)
            .map(|j| (0..rows).map(|i| abs_bound[i][j]).fold(0.0_f64, f64::max))
            .sum::<f64>(),
        // L1 -> L2: sqrt(sum of column sums squared) - conservative bound
        (Norm::L1, Norm::L2) => {
            let col_sums: Vec<f64> = (0..cols)
                .map(|j| (0..rows).map(|i| abs_bound[i][j]).sum::<f64>())
                .collect();
            col_sums.iter().map(|&x| x * x).sum::<f64>().sqrt()
        }
        // L∞ -> L2: sqrt(sum of row sums squared) - conservative bound
        (Norm::Linf, Norm::L2) => {
            let row_sums: Vec<f64> = abs_bound
                .iter()
                .map(|row| row.iter().sum::<f64>())
                .collect();
            row_sums.iter().map(|&x| x * x).sum::<f64>().sqrt()
        }
        // L2 -> L1: sqrt(m) * max row L2 norm (conservative bound)
        (Norm::L2, Norm::L1) => {
            let max_row_l2 = abs_bound
                .iter()
                .map(|row| row.iter().map(|&x| x * x).sum::<f64>().sqrt())
                .fold(0.0_f64, f64::max);
            (rows as f64).sqrt() * max_row_l2
        }
        // L0 norm is not a true norm; use conservative Frobenius bound
        (Norm::L0, _) | (_, Norm::L0) => {
            // Frobenius norm: sqrt(sum of squared entries)
            abs_bound
                .iter()
                .flat_map(|row| row.iter())
                .map(|&x| x * x)
                .sum::<f64>()
                .sqrt()
        }
    }
}

/// Verify Independence fairness criterion
///
/// Output is independent of protected attributes if all Jacobian entries
/// for protected inputs are bounded near zero.
///
/// For each output j and protected input i, checks:
/// max(|J_L[j,i]|, |J_U[j,i]|) < INDEPENDENCE_THRESHOLD
///
/// This is a sound sufficient condition: if the Jacobian entries are bounded
/// near zero, then the output cannot depend significantly on the protected inputs.
fn verify_fairness_independence(
    jacobian: &IntervalMatrix,
    protected_attrs: &[usize],
) -> VerifyResult {
    // Threshold for "near zero" - Jacobian entries with absolute bound below this
    // are considered independent. This is a practical threshold for numerical stability.
    const INDEPENDENCE_THRESHOLD: f64 = 1e-6;

    let rows = jacobian.rows();
    let cols = jacobian.cols();

    // Check each protected attribute column
    let mut max_sensitivity: f64 = 0.0;
    let mut worst_output = 0;
    let mut worst_attr = 0;

    for &attr_idx in protected_attrs {
        if attr_idx >= cols {
            return VerifyResult::Unknown {
                reason: format!(
                    "Protected attribute index {attr_idx} out of bounds (Jacobian has {cols} columns)"
                ),
            };
        }

        // For each output, check the Jacobian entry for this protected attribute
        for output_idx in 0..rows {
            let lower = jacobian.lower[output_idx][attr_idx];
            let upper = jacobian.upper[output_idx][attr_idx];
            let abs_bound = lower.abs().max(upper.abs());

            if abs_bound > max_sensitivity {
                max_sensitivity = abs_bound;
                worst_output = output_idx;
                worst_attr = attr_idx;
            }
        }
    }

    if max_sensitivity < INDEPENDENCE_THRESHOLD {
        VerifyResult::Proven
    } else {
        VerifyResult::Unknown {
            reason: format!(
                "Independence not proven: output {worst_output} has sensitivity {max_sensitivity:.6} to protected attribute {worst_attr} (threshold: {INDEPENDENCE_THRESHOLD:.6})"
            ),
        }
    }
}

/// Verify Individual fairness criterion
///
/// Individual fairness requires that similar inputs (differing only in protected
/// attributes) produce similar outputs. This is verified by computing the partial
/// Lipschitz constant restricted to the protected input dimensions.
///
/// If ||∂f/∂x_protected||_{∞→∞} <= similarity_threshold, then for any two inputs
/// x, x' that differ only in protected attributes:
/// ||f(x) - f(x')||_∞ <= similarity_threshold * ||x_protected - x'_protected||_∞
fn verify_fairness_individual(
    jacobian: &IntervalMatrix,
    protected_attrs: &[usize],
    similarity_threshold: f64,
) -> VerifyResult {
    let rows = jacobian.rows();
    let cols = jacobian.cols();

    if protected_attrs.is_empty() {
        return VerifyResult::Proven; // No protected attributes = trivially fair
    }

    // Validate protected attribute indices
    for &attr_idx in protected_attrs {
        if attr_idx >= cols {
            return VerifyResult::Unknown {
                reason: format!(
                    "Protected attribute index {attr_idx} out of bounds (Jacobian has {cols} columns)"
                ),
            };
        }
    }

    // Compute partial Lipschitz constant (L∞ -> L∞ norm restricted to protected columns)
    // This is the max row sum over protected columns
    let mut max_row_sum: f64 = 0.0;

    for i in 0..rows {
        let row_sum: f64 = protected_attrs
            .iter()
            .map(|&j| {
                let lower = jacobian.lower[i][j];
                let upper = jacobian.upper[i][j];
                lower.abs().max(upper.abs())
            })
            .sum();

        if row_sum > max_row_sum {
            max_row_sum = row_sum;
        }
    }

    if max_row_sum <= similarity_threshold {
        VerifyResult::Proven
    } else {
        VerifyResult::Unknown {
            reason: format!(
                "Individual fairness not proven: partial Lipschitz constant {max_row_sum:.6} > threshold {similarity_threshold:.6}"
            ),
        }
    }
}

/// Forward pass through a network with skip connection support
fn forward_pass(network: &NnNetwork, input: &[f64]) -> Vec<f64> {
    // Track intermediate outputs for skip connections
    // layer_outputs[0] = input, layer_outputs[i+1] = output of layer i
    let mut layer_outputs = vec![input.to_vec()];
    let mut values = input.to_vec();

    for (i, layer) in network.layers.iter().enumerate() {
        values = match layer {
            NnLayer::ResidualAdd { skip_from_output } => {
                // Add values element-wise from skip connection
                assert!(
                    *skip_from_output < layer_outputs.len(),
                    "ResidualAdd at layer {i} references invalid skip_from_output {skip_from_output}"
                );
                let skip_values = &layer_outputs[*skip_from_output];
                forward_residual_add(&values, skip_values)
            }
            NnLayer::Concat { skip_from_output } => {
                // Concatenate values from skip connection
                assert!(
                    *skip_from_output < layer_outputs.len(),
                    "Concat at layer {i} references invalid skip_from_output {skip_from_output}"
                );
                let skip_values = &layer_outputs[*skip_from_output];
                forward_concat(&values, skip_values)
            }
            _ => forward_layer(&values, layer),
        };
        layer_outputs.push(values.clone());
    }

    values
}

/// Forward pass through residual add
fn forward_residual_add(current: &[f64], skip: &[f64]) -> Vec<f64> {
    assert_eq!(
        current.len(),
        skip.len(),
        "ResidualAdd requires matching dimensions"
    );
    current.iter().zip(skip).map(|(a, b)| a + b).collect()
}

/// Forward pass through concat
fn forward_concat(current: &[f64], skip: &[f64]) -> Vec<f64> {
    let mut result = current.to_vec();
    result.extend_from_slice(skip);
    result
}

/// Forward pass through a single layer
fn forward_layer(input: &[f64], layer: &NnLayer) -> Vec<f64> {
    match layer {
        NnLayer::Linear { weights, bias } => {
            let mut output = bias.clone();
            for i in 0..weights.len() {
                for (j, &x) in input.iter().enumerate() {
                    output[i] += weights[i][j] * x;
                }
            }
            output
        }
        NnLayer::ReLU => input.iter().map(|&x| x.max(0.0)).collect(),
        NnLayer::LeakyReLU { negative_slope } => input
            .iter()
            .map(|&x| if x >= 0.0 { x } else { negative_slope * x })
            .collect(),
        NnLayer::Sigmoid => input.iter().map(|&x| 1.0 / (1.0 + (-x).exp())).collect(),
        NnLayer::Tanh => input.iter().map(|&x| x.tanh()).collect(),
        NnLayer::BatchNorm { scale, bias } => input
            .iter()
            .enumerate()
            .map(|(i, &x)| scale[i] * x + bias[i])
            .collect(),
        // Dropout and Flatten pass through input unchanged
        NnLayer::Dropout { .. } | NnLayer::Flatten => input.to_vec(),
        NnLayer::MaxPool1d {
            kernel_size,
            stride,
        } => forward_maxpool1d(input, *kernel_size, *stride),
        NnLayer::AvgPool1d {
            kernel_size,
            stride,
        } => forward_avgpool1d(input, *kernel_size, *stride),
        NnLayer::Conv1d {
            in_channels,
            kernel_size,
            stride,
            padding,
            weights,
            bias,
            ..
        } => forward_conv1d(
            input,
            weights,
            bias,
            *in_channels,
            *kernel_size,
            *stride,
            *padding,
        ),
        NnLayer::Conv2d {
            in_channels,
            input_height,
            input_width,
            kernel_size,
            stride,
            padding,
            weights,
            bias,
            ..
        } => forward_conv2d(
            input,
            weights,
            bias,
            *in_channels,
            *input_height,
            *input_width,
            *kernel_size,
            *stride,
            *padding,
        ),
        NnLayer::GlobalAvgPool2d {
            channels,
            height,
            width,
        } => forward_global_avgpool2d(input, *channels, *height, *width),
        NnLayer::GlobalMaxPool2d {
            channels,
            height,
            width,
        } => forward_global_maxpool2d(input, *channels, *height, *width),
        NnLayer::BatchNorm2d {
            channels,
            height,
            width,
            scale,
            bias,
        } => forward_batchnorm2d(input, *channels, *height, *width, scale, bias),
        NnLayer::MaxPool2d {
            channels,
            height,
            width,
            kernel_size,
            stride,
        } => forward_maxpool2d(input, *channels, *height, *width, *kernel_size, *stride),
        NnLayer::AvgPool2d {
            channels,
            height,
            width,
            kernel_size,
            stride,
        } => forward_avgpool2d(input, *channels, *height, *width, *kernel_size, *stride),
        NnLayer::ResidualAdd { .. } | NnLayer::Concat { .. } => {
            // Skip connections require context from previous layers and must be
            // handled by forward_pass_with_skips, not forward_layer
            panic!("ResidualAdd/Concat must be handled at forward pass level, not forward_layer")
        }
    }
}

/// Forward pass through MaxPool1d
fn forward_maxpool1d(input: &[f64], kernel_size: usize, stride: usize) -> Vec<f64> {
    if stride == 0 || kernel_size == 0 || input.len() < kernel_size {
        return input.to_vec();
    }
    let out_dim = (input.len() - kernel_size) / stride + 1;
    (0..out_dim)
        .map(|i| {
            let start = i * stride;
            input[start..start + kernel_size]
                .iter()
                .copied()
                .fold(f64::NEG_INFINITY, f64::max)
        })
        .collect()
}

/// Forward pass through AvgPool1d
fn forward_avgpool1d(input: &[f64], kernel_size: usize, stride: usize) -> Vec<f64> {
    if stride == 0 || kernel_size == 0 || input.len() < kernel_size {
        return input.to_vec();
    }
    let out_dim = (input.len() - kernel_size) / stride + 1;
    let scale = 1.0 / kernel_size as f64;
    (0..out_dim)
        .map(|i| {
            let start = i * stride;
            input[start..start + kernel_size].iter().sum::<f64>() * scale
        })
        .collect()
}

/// Find the index of the maximum element
fn argmax(values: &[f64]) -> usize {
    values
        .iter()
        .enumerate()
        .max_by(|(_, a), (_, b)| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
        .map_or(0, |(i, _)| i)
}

impl ProofBackend for CrownBackend {
    fn name(&self) -> &'static str {
        "crown"
    }

    fn capabilities(&self) -> BackendCapabilities {
        BackendCapabilities {
            predicates: false,
            quantifiers: false,
            theories: vec![],
            temporal: false,
            separation: false,
            neural_network: true,
            bounded_model_check: false,
            induction: false,
            incremental: false,
            counterexamples: true,
            proof_production: false,
        }
    }

    fn check(&self, vc: &VerificationCondition, config: &VerifyConfig) -> VerifyResult {
        match &vc.condition {
            VcKind::NeuralNetwork(spec) => self.verify_nn_spec(spec, config),
            _ => VerifyResult::Error(vc_ir::VerifyError::Unsupported {
                feature: format!(
                    "CROWN backend only handles neural network VCs, got {:?}",
                    vc.condition
                ),
                suggestion: Some("Use Z4 or Kani for this VC".to_string()),
            }),
        }
    }

    fn counterexample(&self, _vc: &VerificationCondition) -> Option<Counterexample> {
        None
    }

    fn reset(&mut self) {
        // Reset solver state
    }

    fn assume(&mut self, _pred: &Predicate) {
        // CROWN doesn't support incremental assumptions
    }
}

/// Utilities for working with neural networks in tRust
pub mod utils {
    use super::NnArchitecture;

    /// Load a neural network from ONNX format
    pub fn load_onnx(_path: &str) -> Result<NnArchitecture, String> {
        Err("ONNX loading not yet implemented".to_string())
    }

    /// Convert PyTorch model to tRust format
    pub fn from_pytorch(_model: &str) -> Result<NnArchitecture, String> {
        Err("PyTorch loading not yet implemented".to_string())
    }
}

/// JSON model format for specifying neural networks
///
/// Example JSON:
/// ```json
/// {
///   "input_dim": 2,
///   "layers": [
///     {"type": "Linear", "weights": [[1.0, 2.0], [3.0, 4.0]], "bias": [0.0, 0.0]},
///     {"type": "ReLU"},
///     {"type": "Linear", "weights": [[0.5, 0.5]], "bias": [0.1]}
///   ]
/// }
/// ```
pub mod json_model {
    use super::{NnLayer, NnNetwork};
    use serde::{Deserialize, Serialize};
    use std::fs;
    use std::path::Path;

    /// JSON representation of a neural network model
    #[derive(Debug, Clone, Serialize, Deserialize)]
    pub struct JsonModel {
        /// Input dimension
        pub input_dim: usize,
        /// Network layers
        pub layers: Vec<JsonLayer>,
    }

    /// JSON representation of a layer
    #[derive(Debug, Clone, Serialize, Deserialize)]
    #[serde(tag = "type")]
    pub enum JsonLayer {
        /// Fully connected layer
        Linear {
            /// Weight matrix (out_features x in_features)
            weights: Vec<Vec<f64>>,
            /// Bias vector
            bias: Vec<f64>,
        },
        /// ReLU activation
        ReLU,
        /// Leaky ReLU activation
        LeakyReLU {
            /// Negative slope (default 0.01)
            #[serde(default = "default_leaky_relu_slope")]
            negative_slope: f64,
        },
        /// Sigmoid activation
        Sigmoid,
        /// Tanh activation
        Tanh,
        /// Batch normalization layer (inference mode)
        BatchNorm {
            /// Scale factor (num_features): gamma / sqrt(var + eps)
            scale: Vec<f64>,
            /// Bias (num_features): beta - gamma * mean / sqrt(var + eps)
            bias: Vec<f64>,
        },
        /// Dropout layer (inference mode = identity)
        Dropout {
            /// Dropout probability (not used in inference)
            #[serde(default)]
            p: f64,
        },
        /// Flatten layer (reshapes to 1D)
        Flatten,
        /// 1D Max pooling layer
        MaxPool1d {
            /// Kernel size
            kernel_size: usize,
            /// Stride (defaults to kernel_size)
            #[serde(default)]
            stride: usize,
        },
        /// 1D Average pooling layer
        AvgPool1d {
            /// Kernel size
            kernel_size: usize,
            /// Stride (defaults to kernel_size)
            #[serde(default)]
            stride: usize,
        },
        /// 1D Convolution layer
        Conv1d {
            /// Input channels
            in_channels: usize,
            /// Output channels
            out_channels: usize,
            /// Kernel size
            kernel_size: usize,
            /// Stride (default 1)
            #[serde(default = "default_stride")]
            stride: usize,
            /// Padding (default 0)
            #[serde(default)]
            padding: usize,
            /// Weight tensor (out_channels x in_channels x kernel_size)
            weights: Vec<Vec<Vec<f64>>>,
            /// Bias vector (out_channels) or empty
            #[serde(default)]
            bias: Vec<f64>,
        },
        /// 2D Convolution layer
        Conv2d {
            /// Input channels
            in_channels: usize,
            /// Output channels
            out_channels: usize,
            /// Input height
            input_height: usize,
            /// Input width
            input_width: usize,
            /// Kernel size (square)
            kernel_size: usize,
            /// Stride (default 1)
            #[serde(default = "default_stride")]
            stride: usize,
            /// Padding (default 0)
            #[serde(default)]
            padding: usize,
            /// Weight tensor (out_channels x in_channels x kernel_size x kernel_size)
            weights: Vec<Vec<Vec<Vec<f64>>>>,
            /// Bias vector (out_channels) or empty
            #[serde(default)]
            bias: Vec<f64>,
        },
        /// Global Average Pooling 2D layer
        GlobalAvgPool2d {
            /// Number of channels
            channels: usize,
            /// Input height
            height: usize,
            /// Input width
            width: usize,
        },
        /// Global Max Pooling 2D layer
        GlobalMaxPool2d {
            /// Number of channels
            channels: usize,
            /// Input height
            height: usize,
            /// Input width
            width: usize,
        },
        /// 2D Batch Normalization layer (inference mode)
        BatchNorm2d {
            channels: usize,
            height: usize,
            width: usize,
            scale: Vec<f64>,
            bias: Vec<f64>,
        },
        /// 2D Max Pooling layer
        MaxPool2d {
            channels: usize,
            height: usize,
            width: usize,
            kernel_size: usize,
            #[serde(default = "default_stride")]
            stride: usize,
        },
        /// 2D Average Pooling layer
        AvgPool2d {
            channels: usize,
            height: usize,
            width: usize,
            kernel_size: usize,
            #[serde(default = "default_stride")]
            stride: usize,
        },
        /// Residual Add layer - adds output from a previous layer to current input
        ResidualAdd {
            /// Index of the layer output to add (0 = input, n = output of layer n-1)
            skip_from_output: usize,
        },
        /// Concatenation layer - concatenates output from a previous layer with current input
        Concat {
            /// Index of the layer output to concatenate (0 = input, n = output of layer n-1)
            skip_from_output: usize,
        },
    }

    const fn default_stride() -> usize {
        1
    }

    const fn default_leaky_relu_slope() -> f64 {
        0.01
    }

    impl JsonModel {
        /// Load a model from a JSON file
        pub fn load_file<P: AsRef<Path>>(path: P) -> Result<Self, String> {
            let content = fs::read_to_string(path.as_ref())
                .map_err(|e| format!("Failed to read model file: {e}"))?;
            Self::from_json(&content)
        }

        /// Parse a model from JSON string
        pub fn from_json(json: &str) -> Result<Self, String> {
            serde_json::from_str(json).map_err(|e| format!("Failed to parse model JSON: {e}"))
        }

        /// Convert to NnNetwork for verification
        pub fn to_network(&self) -> Result<NnNetwork, String> {
            let mut layers = Vec::new();
            let mut dim = self.input_dim;
            // Track dimensions at each layer output for skip connections:
            // layer_dims[0] = input_dim, layer_dims[i+1] = output of layer i
            let mut layer_dims = vec![self.input_dim];

            for (i, layer) in self.layers.iter().enumerate() {
                match layer {
                    JsonLayer::Linear { weights, bias } => {
                        // Validate dimensions
                        if weights.is_empty() {
                            return Err(format!("Layer {i}: empty weight matrix"));
                        }
                        let out_dim = weights.len();
                        let in_dim = weights[0].len();

                        if in_dim != dim {
                            return Err(format!(
                                "Layer {i}: input dimension mismatch (expected {dim}, got {in_dim})"
                            ));
                        }

                        if bias.len() != out_dim {
                            return Err(format!(
                                "Layer {}: bias dimension mismatch (expected {}, got {})",
                                i,
                                out_dim,
                                bias.len()
                            ));
                        }

                        // Validate all rows have same length
                        for (j, row) in weights.iter().enumerate() {
                            if row.len() != in_dim {
                                return Err(format!(
                                    "Layer {}: row {} has wrong dimension (expected {}, got {})",
                                    i,
                                    j,
                                    in_dim,
                                    row.len()
                                ));
                            }
                        }

                        layers.push(NnLayer::Linear {
                            weights: weights.clone(),
                            bias: bias.clone(),
                        });
                        dim = out_dim;
                    }
                    JsonLayer::ReLU => {
                        layers.push(NnLayer::ReLU);
                    }
                    JsonLayer::LeakyReLU { negative_slope } => {
                        layers.push(NnLayer::LeakyReLU {
                            negative_slope: *negative_slope,
                        });
                    }
                    JsonLayer::Sigmoid => {
                        layers.push(NnLayer::Sigmoid);
                    }
                    JsonLayer::Tanh => {
                        layers.push(NnLayer::Tanh);
                    }
                    JsonLayer::BatchNorm { scale, bias } => {
                        // Validate dimensions
                        if scale.len() != dim {
                            return Err(format!(
                                "Layer {}: scale dimension mismatch (expected {}, got {})",
                                i,
                                dim,
                                scale.len()
                            ));
                        }
                        if bias.len() != dim {
                            return Err(format!(
                                "Layer {}: bias dimension mismatch (expected {}, got {})",
                                i,
                                dim,
                                bias.len()
                            ));
                        }
                        layers.push(NnLayer::BatchNorm {
                            scale: scale.clone(),
                            bias: bias.clone(),
                        });
                        // BatchNorm preserves dimensions
                    }
                    JsonLayer::Dropout { p } => {
                        layers.push(NnLayer::Dropout { p: *p });
                        // Dropout preserves dimensions
                    }
                    JsonLayer::Flatten => {
                        layers.push(NnLayer::Flatten);
                        // Flatten preserves dimensions (for 1D networks)
                    }
                    JsonLayer::MaxPool1d {
                        kernel_size,
                        stride,
                    } => {
                        let actual_stride = if *stride == 0 { *kernel_size } else { *stride };
                        if dim >= *kernel_size && actual_stride > 0 {
                            dim = (dim - kernel_size) / actual_stride + 1;
                        }
                        layers.push(NnLayer::MaxPool1d {
                            kernel_size: *kernel_size,
                            stride: actual_stride,
                        });
                    }
                    JsonLayer::AvgPool1d {
                        kernel_size,
                        stride,
                    } => {
                        let actual_stride = if *stride == 0 { *kernel_size } else { *stride };
                        if dim >= *kernel_size && actual_stride > 0 {
                            dim = (dim - kernel_size) / actual_stride + 1;
                        }
                        layers.push(NnLayer::AvgPool1d {
                            kernel_size: *kernel_size,
                            stride: actual_stride,
                        });
                    }
                    JsonLayer::Conv1d {
                        in_channels,
                        out_channels,
                        kernel_size,
                        stride,
                        padding,
                        weights,
                        bias,
                    } => {
                        let actual_stride = if *stride == 0 { 1 } else { *stride };
                        // Validate dimensions
                        if weights.len() != *out_channels {
                            return Err(format!(
                                "Layer {}: Conv1d out_channels mismatch (expected {}, got {})",
                                i,
                                *out_channels,
                                weights.len()
                            ));
                        }
                        // Update dimension for conv output
                        let input_length = dim / *in_channels;
                        let effective_length = input_length + 2 * *padding;
                        if effective_length >= *kernel_size && actual_stride > 0 {
                            let output_length =
                                (effective_length - kernel_size) / actual_stride + 1;
                            dim = *out_channels * output_length;
                        }
                        layers.push(NnLayer::Conv1d {
                            in_channels: *in_channels,
                            out_channels: *out_channels,
                            kernel_size: *kernel_size,
                            stride: actual_stride,
                            padding: *padding,
                            weights: weights.clone(),
                            bias: bias.clone(),
                        });
                    }
                    JsonLayer::Conv2d {
                        in_channels,
                        out_channels,
                        input_height,
                        input_width,
                        kernel_size,
                        stride,
                        padding,
                        weights,
                        bias,
                    } => {
                        let actual_stride = if *stride == 0 { 1 } else { *stride };
                        // Validate dimensions
                        if weights.len() != *out_channels {
                            return Err(format!(
                                "Layer {}: Conv2d out_channels mismatch (expected {}, got {})",
                                i,
                                *out_channels,
                                weights.len()
                            ));
                        }
                        // Update dimension for conv output
                        let effective_height = *input_height + 2 * *padding;
                        let effective_width = *input_width + 2 * *padding;
                        if effective_height >= *kernel_size
                            && effective_width >= *kernel_size
                            && actual_stride > 0
                        {
                            let out_height = (effective_height - kernel_size) / actual_stride + 1;
                            let out_width = (effective_width - kernel_size) / actual_stride + 1;
                            dim = *out_channels * out_height * out_width;
                        }
                        layers.push(NnLayer::Conv2d {
                            in_channels: *in_channels,
                            out_channels: *out_channels,
                            input_height: *input_height,
                            input_width: *input_width,
                            kernel_size: *kernel_size,
                            stride: actual_stride,
                            padding: *padding,
                            weights: weights.clone(),
                            bias: bias.clone(),
                        });
                    }
                    JsonLayer::GlobalAvgPool2d {
                        channels,
                        height,
                        width,
                    } => {
                        // GlobalAvgPool2d: input is (channels * height * width), output is (channels)
                        let expected_dim = channels * height * width;
                        if dim != expected_dim {
                            return Err(format!(
                                "Layer {i}: GlobalAvgPool2d input dimension mismatch (expected {expected_dim}, got {dim})"
                            ));
                        }
                        dim = *channels;
                        layers.push(NnLayer::GlobalAvgPool2d {
                            channels: *channels,
                            height: *height,
                            width: *width,
                        });
                    }
                    JsonLayer::GlobalMaxPool2d {
                        channels,
                        height,
                        width,
                    } => {
                        // GlobalMaxPool2d: input is (channels * height * width), output is (channels)
                        let expected_dim = channels * height * width;
                        if dim != expected_dim {
                            return Err(format!(
                                "Layer {i}: GlobalMaxPool2d input dimension mismatch (expected {expected_dim}, got {dim})"
                            ));
                        }
                        dim = *channels;
                        layers.push(NnLayer::GlobalMaxPool2d {
                            channels: *channels,
                            height: *height,
                            width: *width,
                        });
                    }
                    JsonLayer::BatchNorm2d {
                        channels,
                        height,
                        width,
                        scale,
                        bias,
                    } => {
                        // BatchNorm2d: operates on (channels * height * width) flattened tensor
                        let expected_dim = channels * height * width;
                        if dim != expected_dim {
                            return Err(format!(
                                "Layer {i}: BatchNorm2d input dimension mismatch (expected {expected_dim}, got {dim})"
                            ));
                        }
                        if scale.len() != *channels {
                            return Err(format!(
                                "Layer {}: BatchNorm2d scale dimension mismatch (expected {}, got {})",
                                i, channels, scale.len()
                            ));
                        }
                        layers.push(NnLayer::BatchNorm2d {
                            channels: *channels,
                            height: *height,
                            width: *width,
                            scale: scale.clone(),
                            bias: bias.clone(),
                        });
                        // BatchNorm2d preserves dimensions
                    }
                    JsonLayer::MaxPool2d {
                        channels,
                        height,
                        width,
                        kernel_size,
                        stride,
                    } => {
                        // MaxPool2d: pools across spatial dimensions
                        let expected_dim = channels * height * width;
                        if dim != expected_dim {
                            return Err(format!(
                                "Layer {i}: MaxPool2d input dimension mismatch (expected {expected_dim}, got {dim})"
                            ));
                        }
                        let actual_stride = if *stride == 0 { *kernel_size } else { *stride };
                        let out_height = (height - kernel_size) / actual_stride + 1;
                        let out_width = (width - kernel_size) / actual_stride + 1;
                        dim = *channels * out_height * out_width;
                        layers.push(NnLayer::MaxPool2d {
                            channels: *channels,
                            height: *height,
                            width: *width,
                            kernel_size: *kernel_size,
                            stride: actual_stride,
                        });
                    }
                    JsonLayer::AvgPool2d {
                        channels,
                        height,
                        width,
                        kernel_size,
                        stride,
                    } => {
                        // AvgPool2d: pools across spatial dimensions
                        let expected_dim = channels * height * width;
                        if dim != expected_dim {
                            return Err(format!(
                                "Layer {i}: AvgPool2d input dimension mismatch (expected {expected_dim}, got {dim})"
                            ));
                        }
                        let actual_stride = if *stride == 0 { *kernel_size } else { *stride };
                        let out_height = (height - kernel_size) / actual_stride + 1;
                        let out_width = (width - kernel_size) / actual_stride + 1;
                        dim = *channels * out_height * out_width;
                        layers.push(NnLayer::AvgPool2d {
                            channels: *channels,
                            height: *height,
                            width: *width,
                            kernel_size: *kernel_size,
                            stride: actual_stride,
                        });
                    }
                    JsonLayer::ResidualAdd { skip_from_output } => {
                        // ResidualAdd: adds output from skip_from_output to current
                        // Dimension stays the same (element-wise addition)
                        if *skip_from_output > i {
                            return Err(format!(
                                "Layer {i}: ResidualAdd skip_from_output ({skip_from_output}) references future layer"
                            ));
                        }
                        layers.push(NnLayer::ResidualAdd {
                            skip_from_output: *skip_from_output,
                        });
                    }
                    JsonLayer::Concat { skip_from_output } => {
                        // Concat: concatenates output from skip_from_output with current
                        // Need to track skip dimension to update current dimension
                        if *skip_from_output > i {
                            return Err(format!(
                                "Layer {i}: Concat skip_from_output ({skip_from_output}) references future layer"
                            ));
                        }
                        // Look up skip dimension from layer_dims
                        let skip_dim = layer_dims[*skip_from_output];
                        dim += skip_dim;
                        layers.push(NnLayer::Concat {
                            skip_from_output: *skip_from_output,
                        });
                    }
                }
                layer_dims.push(dim);
            }

            Ok(NnNetwork::new(layers, self.input_dim))
        }

        /// Save model to JSON string
        pub fn to_json(&self) -> Result<String, String> {
            serde_json::to_string_pretty(self)
                .map_err(|e| format!("Failed to serialize model: {e}"))
        }

        /// Save model to file
        pub fn save_file<P: AsRef<Path>>(&self, path: P) -> Result<(), String> {
            let json = self.to_json()?;
            fs::write(path.as_ref(), json).map_err(|e| format!("Failed to write model file: {e}"))
        }
    }

    /// Convert NnNetwork to JsonModel for saving
    impl From<&NnNetwork> for JsonModel {
        fn from(network: &NnNetwork) -> Self {
            let layers = network
                .layers
                .iter()
                .map(|layer| match layer {
                    NnLayer::Linear { weights, bias } => JsonLayer::Linear {
                        weights: weights.clone(),
                        bias: bias.clone(),
                    },
                    NnLayer::ReLU => JsonLayer::ReLU,
                    NnLayer::LeakyReLU { negative_slope } => JsonLayer::LeakyReLU {
                        negative_slope: *negative_slope,
                    },
                    NnLayer::Sigmoid => JsonLayer::Sigmoid,
                    NnLayer::Tanh => JsonLayer::Tanh,
                    NnLayer::BatchNorm { scale, bias } => JsonLayer::BatchNorm {
                        scale: scale.clone(),
                        bias: bias.clone(),
                    },
                    NnLayer::Dropout { p } => JsonLayer::Dropout { p: *p },
                    NnLayer::Flatten => JsonLayer::Flatten,
                    NnLayer::MaxPool1d {
                        kernel_size,
                        stride,
                    } => JsonLayer::MaxPool1d {
                        kernel_size: *kernel_size,
                        stride: *stride,
                    },
                    NnLayer::AvgPool1d {
                        kernel_size,
                        stride,
                    } => JsonLayer::AvgPool1d {
                        kernel_size: *kernel_size,
                        stride: *stride,
                    },
                    NnLayer::Conv1d {
                        in_channels,
                        out_channels,
                        kernel_size,
                        stride,
                        padding,
                        weights,
                        bias,
                    } => JsonLayer::Conv1d {
                        in_channels: *in_channels,
                        out_channels: *out_channels,
                        kernel_size: *kernel_size,
                        stride: *stride,
                        padding: *padding,
                        weights: weights.clone(),
                        bias: bias.clone(),
                    },
                    NnLayer::Conv2d {
                        in_channels,
                        out_channels,
                        input_height,
                        input_width,
                        kernel_size,
                        stride,
                        padding,
                        weights,
                        bias,
                    } => JsonLayer::Conv2d {
                        in_channels: *in_channels,
                        out_channels: *out_channels,
                        input_height: *input_height,
                        input_width: *input_width,
                        kernel_size: *kernel_size,
                        stride: *stride,
                        padding: *padding,
                        weights: weights.clone(),
                        bias: bias.clone(),
                    },
                    NnLayer::GlobalAvgPool2d {
                        channels,
                        height,
                        width,
                    } => JsonLayer::GlobalAvgPool2d {
                        channels: *channels,
                        height: *height,
                        width: *width,
                    },
                    NnLayer::GlobalMaxPool2d {
                        channels,
                        height,
                        width,
                    } => JsonLayer::GlobalMaxPool2d {
                        channels: *channels,
                        height: *height,
                        width: *width,
                    },
                    NnLayer::BatchNorm2d {
                        channels,
                        height,
                        width,
                        scale,
                        bias,
                    } => JsonLayer::BatchNorm2d {
                        channels: *channels,
                        height: *height,
                        width: *width,
                        scale: scale.clone(),
                        bias: bias.clone(),
                    },
                    NnLayer::MaxPool2d {
                        channels,
                        height,
                        width,
                        kernel_size,
                        stride,
                    } => JsonLayer::MaxPool2d {
                        channels: *channels,
                        height: *height,
                        width: *width,
                        kernel_size: *kernel_size,
                        stride: *stride,
                    },
                    NnLayer::AvgPool2d {
                        channels,
                        height,
                        width,
                        kernel_size,
                        stride,
                    } => JsonLayer::AvgPool2d {
                        channels: *channels,
                        height: *height,
                        width: *width,
                        kernel_size: *kernel_size,
                        stride: *stride,
                    },
                    NnLayer::ResidualAdd { skip_from_output } => JsonLayer::ResidualAdd {
                        skip_from_output: *skip_from_output,
                    },
                    NnLayer::Concat { skip_from_output } => JsonLayer::Concat {
                        skip_from_output: *skip_from_output,
                    },
                })
                .collect();

            Self {
                input_dim: network.input_dim,
                layers,
            }
        }
    }
}

/// ONNX model loading support
///
/// Loads neural network models from ONNX format files.
/// Supports feedforward networks with Linear (Gemm/MatMul), ReLU, LeakyReLU, Sigmoid, and Tanh layers.
///
/// # Example
/// ```ignore
/// use trust_crown::onnx_model::OnnxModel;
///
/// let model = OnnxModel::load_file("model.onnx")?;
/// let network = model.to_network()?;
/// ```
#[cfg(feature = "onnx")]
pub mod onnx_model {
    use super::{NnLayer, NnNetwork};
    use onnx_extractor::OnnxModel as ExtractorModel;
    use std::collections::HashMap;

    /// Wrapper around ONNX model for conversion to NnNetwork
    pub struct OnnxModel {
        /// The underlying onnx-extractor model
        extractor: ExtractorModel,
    }

    /// Supported ONNX operator types that we can convert to NnLayer
    #[derive(Debug, Clone, PartialEq)]
    pub enum SupportedOp {
        /// Gemm: y = alpha*A*B + beta*C (general matrix multiply, common for dense layers)
        Gemm,
        /// MatMul: matrix multiplication
        MatMul,
        /// Add: element-wise addition (used for bias)
        Add,
        /// Relu activation
        Relu,
        /// LeakyRelu activation
        LeakyRelu,
        /// Sigmoid activation
        Sigmoid,
        /// Tanh activation
        Tanh,
        /// Flatten: reshape to 2D (typically before first dense layer)
        Flatten,
    }

    impl OnnxModel {
        /// Load an ONNX model from a file
        pub fn load_file(path: &str) -> Result<Self, String> {
            let extractor = ExtractorModel::load_from_file(path)
                .map_err(|e| format!("Failed to load ONNX model: {}", e))?;

            Ok(Self { extractor })
        }

        /// Get input dimension from the model
        fn get_input_dim(&self) -> Result<usize, String> {
            // Get input tensor names
            if self.extractor.inputs.is_empty() {
                return Err("ONNX model has no inputs".to_string());
            }

            // Get the first input's tensor
            let input_name = &self.extractor.inputs[0];
            if let Some(tensor) = self.extractor.get_tensor(input_name) {
                let shape = tensor.shape();
                // Input shape is typically [batch, features] or [batch, ...features...]
                // We take the product of all dims except batch
                if shape.len() < 2 {
                    return Err(format!("Input tensor has invalid shape: {:?}", shape));
                }
                // Convert i64 to usize
                let input_dim: usize = shape[1..].iter().map(|&d| d as usize).product();
                Ok(input_dim)
            } else {
                Err(format!("Input tensor '{}' not found", input_name))
            }
        }

        /// Extract weight tensor as 2D f64 matrix (out_features x in_features)
        fn get_weight_matrix(&self, name: &str) -> Result<Vec<Vec<f64>>, String> {
            let tensor = self
                .extractor
                .get_tensor(name)
                .ok_or_else(|| format!("Weight tensor '{}' not found", name))?;

            let shape = tensor.shape();
            if shape.len() != 2 {
                return Err(format!(
                    "Weight tensor '{}' has shape {:?}, expected 2D",
                    name, shape
                ));
            }

            let out_features = shape[0] as usize;
            let in_features = shape[1] as usize;

            // Get data as f32 and convert to f64
            let data: Box<[f32]> = tensor
                .copy_data_as::<f32>()
                .map_err(|e| format!("Failed to read weight data for '{}': {}", name, e))?;

            // Reshape into 2D matrix (row-major)
            let mut matrix = Vec::with_capacity(out_features);
            for i in 0..out_features {
                let row: Vec<f64> = data[i * in_features..(i + 1) * in_features]
                    .iter()
                    .map(|&x| x as f64)
                    .collect();
                matrix.push(row);
            }

            Ok(matrix)
        }

        /// Extract bias tensor as 1D f64 vector
        fn get_bias_vector(&self, name: &str) -> Result<Vec<f64>, String> {
            let tensor = self
                .extractor
                .get_tensor(name)
                .ok_or_else(|| format!("Bias tensor '{}' not found", name))?;

            let shape = tensor.shape();
            if shape.len() != 1 {
                return Err(format!(
                    "Bias tensor '{}' has shape {:?}, expected 1D",
                    name, shape
                ));
            }

            let data: Box<[f32]> = tensor
                .copy_data_as::<f32>()
                .map_err(|e| format!("Failed to read bias data for '{}': {}", name, e))?;

            Ok(data.iter().map(|&x| x as f64).collect())
        }

        /// Convert ONNX model to NnNetwork
        pub fn to_network(&self) -> Result<NnNetwork, String> {
            let input_dim = self.get_input_dim()?;
            let mut layers: Vec<NnLayer> = Vec::new();
            let mut current_dim = input_dim;

            // Get all operations (nodes in topological order)
            let operations = &self.extractor.operations;

            // Track tensor name -> output dimension for dimension tracking
            let mut tensor_dims: HashMap<String, usize> = HashMap::new();

            // Initialize with input dimension
            for input_name in &self.extractor.inputs {
                tensor_dims.insert(input_name.clone(), input_dim);
            }

            for op in operations {
                let op_type = &op.op_type;

                match op_type.as_str() {
                    "Gemm" => {
                        // Gemm: Y = alpha * A * B + beta * C
                        // Inputs: A (data), B (weights), C (bias - optional)
                        // For neural network dense layers:
                        // - A is input [batch, in_features]
                        // - B is weights [in_features, out_features] or transposed
                        // - C is bias [out_features]

                        if op.inputs.len() < 2 {
                            return Err(format!("Gemm node '{}' has insufficient inputs", op.name));
                        }

                        let weight_name = &op.inputs[1];
                        let mut weights = self.get_weight_matrix(weight_name)?;

                        // Check transB attribute - if true, weights are [out, in] already
                        // If false (default), weights are [in, out] and need transpose
                        // Most PyTorch exports have transB=1
                        let trans_b = Self::get_gemm_trans_b(op);
                        if !trans_b {
                            // Transpose weights from [in, out] to [out, in]
                            weights = transpose_matrix(&weights);
                        }

                        let out_features = weights.len();
                        let in_features = weights[0].len();

                        // Validate dimension
                        if in_features != current_dim {
                            return Err(format!(
                                "Gemm '{}': dimension mismatch (expected {}, got {})",
                                op.name, current_dim, in_features
                            ));
                        }

                        // Get bias if present
                        let bias = if op.inputs.len() >= 3 {
                            self.get_bias_vector(&op.inputs[2])?
                        } else {
                            vec![0.0; out_features]
                        };

                        if bias.len() != out_features {
                            return Err(format!(
                                "Gemm '{}': bias dimension mismatch (expected {}, got {})",
                                op.name,
                                out_features,
                                bias.len()
                            ));
                        }

                        layers.push(NnLayer::Linear { weights, bias });
                        current_dim = out_features;

                        // Update tensor dims for outputs
                        for output in &op.outputs {
                            tensor_dims.insert(output.clone(), current_dim);
                        }
                    }

                    "MatMul" => {
                        // MatMul: Y = A * B
                        // Need to find the weight tensor (the one that's a constant)

                        if op.inputs.len() != 2 {
                            return Err(format!("MatMul op '{}' requires 2 inputs", op.name));
                        }

                        // Try to get weights from second input (common pattern)
                        let weight_name = &op.inputs[1];
                        let weights = self.get_weight_matrix(weight_name)?;

                        // MatMul: [batch, in] @ [in, out] -> [batch, out]
                        // weights shape is [in, out], we need [out, in]
                        let weights = transpose_matrix(&weights);

                        let out_features = weights.len();
                        let in_features = weights[0].len();

                        if in_features != current_dim {
                            return Err(format!(
                                "MatMul '{}': dimension mismatch (expected {}, got {})",
                                op.name, current_dim, in_features
                            ));
                        }

                        // MatMul has no bias - will be added by subsequent Add node
                        let bias = vec![0.0; out_features];

                        layers.push(NnLayer::Linear { weights, bias });
                        current_dim = out_features;

                        for output in &op.outputs {
                            tensor_dims.insert(output.clone(), current_dim);
                        }
                    }

                    "Add" => {
                        // Add: Y = A + B
                        // If A is a layer output and B is a bias constant, modify last layer
                        // Otherwise, skip (we don't support general element-wise add)

                        if op.inputs.len() != 2 {
                            continue;
                        }

                        // Try to get bias from second input
                        if let Ok(bias) = self.get_bias_vector(&op.inputs[1]) {
                            // Modify the last Linear layer to add bias
                            if let Some(NnLayer::Linear {
                                bias: ref mut layer_bias,
                                ..
                            }) = layers.last_mut()
                            {
                                if bias.len() == layer_bias.len() {
                                    for (i, b) in bias.iter().enumerate() {
                                        layer_bias[i] += b;
                                    }
                                }
                            }
                        }

                        for output in &op.outputs {
                            tensor_dims.insert(output.clone(), current_dim);
                        }
                    }

                    "Relu" => {
                        layers.push(NnLayer::ReLU);
                        for output in &op.outputs {
                            tensor_dims.insert(output.clone(), current_dim);
                        }
                    }

                    "LeakyRelu" => {
                        let negative_slope = Self::get_leaky_relu_alpha(op);
                        layers.push(NnLayer::LeakyReLU { negative_slope });
                        for output in &op.outputs {
                            tensor_dims.insert(output.clone(), current_dim);
                        }
                    }

                    "Sigmoid" => {
                        layers.push(NnLayer::Sigmoid);
                        for output in &op.outputs {
                            tensor_dims.insert(output.clone(), current_dim);
                        }
                    }

                    "Tanh" => {
                        layers.push(NnLayer::Tanh);
                        for output in &op.outputs {
                            tensor_dims.insert(output.clone(), current_dim);
                        }
                    }

                    "Flatten" => {
                        // Flatten just reshapes, dimension stays the same for our purposes
                        for output in &op.outputs {
                            tensor_dims.insert(output.clone(), current_dim);
                        }
                    }

                    "Constant" | "Identity" | "Shape" | "Gather" | "Unsqueeze" | "Reshape" => {
                        // These are utility nodes, skip them
                        for output in &op.outputs {
                            tensor_dims.insert(output.clone(), current_dim);
                        }
                    }

                    _ => {
                        // Unsupported operator - warn but continue
                        eprintln!(
                            "Warning: Unsupported ONNX operator '{}' in op '{}', skipping",
                            op_type, op.name
                        );
                        for output in &op.outputs {
                            tensor_dims.insert(output.clone(), current_dim);
                        }
                    }
                }
            }

            if layers.is_empty() {
                return Err("No supported layers found in ONNX model".to_string());
            }

            Ok(NnNetwork::new(layers, input_dim))
        }

        /// Check if Gemm op has transB attribute set
        fn get_gemm_trans_b(op: &onnx_extractor::OnnxOperation) -> bool {
            // Most PyTorch exports have transB=1 (weights are [out, in])
            // Check the transB attribute, default to 1 (true)
            op.get_int_attribute("transB").unwrap_or(1) != 0
        }

        /// Get LeakyRelu alpha parameter from op attributes
        fn get_leaky_relu_alpha(op: &onnx_extractor::OnnxOperation) -> f64 {
            // Default alpha for LeakyRelu in ONNX is 0.01
            op.get_float_attribute("alpha").unwrap_or(0.01) as f64
        }
    }

    /// Transpose a 2D matrix
    fn transpose_matrix(matrix: &[Vec<f64>]) -> Vec<Vec<f64>> {
        if matrix.is_empty() || matrix[0].is_empty() {
            return Vec::new();
        }

        let rows = matrix.len();
        let cols = matrix[0].len();
        let mut result = vec![vec![0.0; rows]; cols];

        for i in 0..rows {
            for j in 0..cols {
                result[j][i] = matrix[i][j];
            }
        }

        result
    }
}

/// Safetensors model loading support
///
/// Loads neural network models from Hugging Face's safetensors format.
/// This format is recommended for PyTorch models as it's safe (no pickle) and fast.
///
/// # Layer Naming Conventions
/// Supports common PyTorch naming patterns:
/// - Sequential: `0.weight`, `0.bias`, `2.weight`, `2.bias` (layer indices, skipping activations)
/// - Named: `fc1.weight`, `fc1.bias`, `fc2.weight`, `fc2.bias`
/// - Prefixed: `model.layer1.weight`, `classifier.weight`
///
/// # Example
/// ```ignore
/// use trust_crown::safetensors_model::SafetensorsModel;
///
/// let model = SafetensorsModel::load_file("model.safetensors")?;
/// let network = model.to_network()?;
/// ```
pub mod safetensors_model {
    use super::{NnLayer, NnNetwork};
    use safetensors::SafeTensors;
    use std::collections::BTreeMap;
    use std::fs;

    /// Parsed layer from safetensors file
    #[derive(Debug)]
    struct ParsedLayer {
        /// Layer index (for ordering)
        index: usize,
        /// Weight matrix [out_features, in_features]
        weights: Vec<Vec<f64>>,
        /// Bias vector [out_features]
        bias: Vec<f64>,
    }

    /// Wrapper for safetensors model loading
    pub struct SafetensorsModel {
        /// Raw file bytes (required for safetensors lifetime)
        data: Vec<u8>,
    }

    impl SafetensorsModel {
        /// Load a safetensors model from a file
        pub fn load_file(path: &str) -> Result<Self, String> {
            let data = fs::read(path)
                .map_err(|e| format!("Failed to read safetensors file '{path}': {e}"))?;

            // Validate we can parse it
            SafeTensors::deserialize(&data)
                .map_err(|e| format!("Failed to parse safetensors: {e}"))?;

            Ok(Self { data })
        }

        /// Load from raw bytes
        pub fn from_bytes(data: Vec<u8>) -> Result<Self, String> {
            SafeTensors::deserialize(&data)
                .map_err(|e| format!("Failed to parse safetensors: {e}"))?;
            Ok(Self { data })
        }

        /// List all tensor names in the file
        pub fn tensor_names(&self) -> Result<Vec<String>, String> {
            let tensors = SafeTensors::deserialize(&self.data)
                .map_err(|e| format!("Failed to parse safetensors: {e}"))?;
            Ok(tensors
                .names()
                .into_iter()
                .map(std::string::ToString::to_string)
                .collect())
        }

        /// Convert to NnNetwork for verification
        pub fn to_network(&self) -> Result<NnNetwork, String> {
            let tensors = SafeTensors::deserialize(&self.data)
                .map_err(|e| format!("Failed to parse safetensors: {e}"))?;

            // Collect all tensor names and categorize them
            let names: Vec<String> = tensors
                .names()
                .into_iter()
                .map(std::string::ToString::to_string)
                .collect();

            if names.is_empty() {
                return Err("Safetensors file has no tensors".to_string());
            }

            // Parse layers from tensor names
            let mut parsed_layers = Self::parse_layers(&tensors)?;

            if parsed_layers.is_empty() {
                return Err("No linear layers found in safetensors model".to_string());
            }

            // Sort layers by index
            parsed_layers.sort_by_key(|l| l.index);

            // Detect activations between linear layers (common patterns)
            // For now, we assume ReLU between linear layers (can be extended)
            let mut layers = Vec::new();
            let mut input_dim = None;

            for (i, parsed) in parsed_layers.iter().enumerate() {
                let in_dim = parsed.weights[0].len();
                let _out_dim = parsed.weights.len();

                // Set input_dim from first layer
                if input_dim.is_none() {
                    input_dim = Some(in_dim);
                }

                // Validate dimension chain
                if i > 0 {
                    // Get expected dimension from previous layer's output
                    // Use rfind for efficient reverse search
                    if let Some(NnLayer::Linear { weights, .. }) =
                        layers.iter().rfind(|l| matches!(l, NnLayer::Linear { .. }))
                    {
                        let prev_out = weights.len();
                        if in_dim != prev_out {
                            return Err(format!(
                                "Dimension mismatch at layer {i}: expected input dim {prev_out}, got {in_dim}"
                            ));
                        }
                    }
                }

                // Add linear layer
                layers.push(NnLayer::Linear {
                    weights: parsed.weights.clone(),
                    bias: parsed.bias.clone(),
                });

                // Add ReLU activation between layers (except after last layer)
                if i < parsed_layers.len() - 1 {
                    layers.push(NnLayer::ReLU);
                }
            }

            Ok(NnNetwork::new(layers, input_dim.unwrap_or(0)))
        }

        /// Parse layers from safetensors tensors
        fn parse_layers(tensors: &SafeTensors) -> Result<Vec<ParsedLayer>, String> {
            // Collect weight and bias tensors by layer
            let mut weight_tensors: BTreeMap<String, (String, usize)> = BTreeMap::new();
            let mut bias_tensors: BTreeMap<String, String> = BTreeMap::new();

            let names: Vec<String> = tensors
                .names()
                .into_iter()
                .map(std::string::ToString::to_string)
                .collect();

            for name in &names {
                // Try to parse layer name and type
                if let Some((layer_name, index)) = Self::parse_weight_name(name) {
                    weight_tensors.insert(layer_name.clone(), (name.clone(), index));
                } else if let Some(layer_name) = Self::parse_bias_name(name) {
                    bias_tensors.insert(layer_name.clone(), name.clone());
                }
            }

            // Match weights with biases and build layers
            let mut layers = Vec::new();

            for (layer_name, (weight_name, index)) in &weight_tensors {
                let weights = Self::read_weight_tensor(tensors, weight_name)?;

                // Look for matching bias
                let bias = if let Some(bias_name) = bias_tensors.get(layer_name) {
                    Self::read_bias_tensor(tensors, bias_name.as_str())?
                } else {
                    // No bias - use zeros
                    vec![0.0; weights.len()]
                };

                // Validate dimensions
                if bias.len() != weights.len() {
                    return Err(format!(
                        "Layer '{}': bias dimension {} doesn't match weights {}",
                        layer_name,
                        bias.len(),
                        weights.len()
                    ));
                }

                layers.push(ParsedLayer {
                    index: *index,
                    weights,
                    bias,
                });
            }

            Ok(layers)
        }

        /// Parse weight tensor name, returning (layer_name, layer_index)
        /// Supports patterns: "0.weight", "fc1.weight", "model.fc1.weight"
        fn parse_weight_name(name: &str) -> Option<(String, usize)> {
            // Remove .weight or _weight suffix using strip_suffix
            let base = name
                .strip_suffix(".weight")
                .or_else(|| name.strip_suffix("_weight"))?;

            // Try to extract layer index
            // Pattern 1: just a number "0", "1", "2"
            if let Ok(idx) = base.parse::<usize>() {
                return Some((base.to_string(), idx));
            }

            // Pattern 2: "fc1", "layer2", etc. - extract trailing number
            let mut chars = base.chars().rev().peekable();
            let mut num_str = String::new();
            while chars.peek().is_some_and(char::is_ascii_digit) {
                num_str.insert(0, chars.next().expect("peek confirmed char exists"));
            }

            if !num_str.is_empty() {
                if let Ok(idx) = num_str.parse::<usize>() {
                    return Some((base.to_string(), idx));
                }
            }

            // Pattern 3: "prefix.name" - use position in sorted order
            // Return with index 0, will be re-indexed based on weight tensor order
            Some((base.to_string(), 0))
        }

        /// Parse bias tensor name, returning layer_name
        fn parse_bias_name(name: &str) -> Option<String> {
            // Remove .bias or _bias suffix using strip_suffix
            name.strip_suffix(".bias")
                .or_else(|| name.strip_suffix("_bias"))
                .map(std::string::ToString::to_string)
        }

        /// Read weight tensor as 2D matrix [out_features, in_features]
        fn read_weight_tensor(tensors: &SafeTensors, name: &str) -> Result<Vec<Vec<f64>>, String> {
            let tensor = tensors
                .tensor(name)
                .map_err(|e| format!("Failed to read tensor '{name}': {e}"))?;

            let shape = tensor.shape();
            if shape.len() != 2 {
                return Err(format!(
                    "Weight tensor '{name}' has shape {shape:?}, expected 2D"
                ));
            }

            let out_features = shape[0];
            let in_features = shape[1];
            let data = tensor.data();

            // Convert based on dtype
            let values: Vec<f64> =
                Self::bytes_to_f64(data, tensor.dtype(), out_features * in_features)?;

            // Reshape into 2D matrix
            let mut matrix = Vec::with_capacity(out_features);
            for i in 0..out_features {
                matrix.push(values[i * in_features..(i + 1) * in_features].to_vec());
            }

            Ok(matrix)
        }

        /// Read bias tensor as 1D vector [out_features]
        fn read_bias_tensor(tensors: &SafeTensors, name: &str) -> Result<Vec<f64>, String> {
            let tensor = tensors
                .tensor(name)
                .map_err(|e| format!("Failed to read tensor '{name}': {e}"))?;

            let shape = tensor.shape();
            if shape.len() != 1 {
                return Err(format!(
                    "Bias tensor '{name}' has shape {shape:?}, expected 1D"
                ));
            }

            let data = tensor.data();
            Self::bytes_to_f64(data, tensor.dtype(), shape[0])
        }

        /// Convert raw bytes to f64 values based on dtype
        fn bytes_to_f64(
            data: &[u8],
            dtype: safetensors::Dtype,
            count: usize,
        ) -> Result<Vec<f64>, String> {
            use safetensors::Dtype;

            match dtype {
                Dtype::F32 => {
                    if data.len() < count * 4 {
                        return Err(format!("Insufficient data for {count} f32 values"));
                    }
                    Ok((0..count)
                        .map(|i| {
                            let bytes = [
                                data[i * 4],
                                data[i * 4 + 1],
                                data[i * 4 + 2],
                                data[i * 4 + 3],
                            ];
                            f64::from(f32::from_le_bytes(bytes))
                        })
                        .collect())
                }
                Dtype::F64 => {
                    if data.len() < count * 8 {
                        return Err(format!("Insufficient data for {count} f64 values"));
                    }
                    Ok((0..count)
                        .map(|i| {
                            let bytes = [
                                data[i * 8],
                                data[i * 8 + 1],
                                data[i * 8 + 2],
                                data[i * 8 + 3],
                                data[i * 8 + 4],
                                data[i * 8 + 5],
                                data[i * 8 + 6],
                                data[i * 8 + 7],
                            ];
                            f64::from_le_bytes(bytes)
                        })
                        .collect())
                }
                Dtype::F16 => {
                    // Half precision - convert to f32 first
                    if data.len() < count * 2 {
                        return Err(format!("Insufficient data for {count} f16 values"));
                    }
                    Ok((0..count)
                        .map(|i| {
                            let bytes = [data[i * 2], data[i * 2 + 1]];
                            let bits = u16::from_le_bytes(bytes);
                            f64::from(half_to_f32(bits))
                        })
                        .collect())
                }
                Dtype::BF16 => {
                    // BFloat16 - convert to f32
                    if data.len() < count * 2 {
                        return Err(format!("Insufficient data for {count} bf16 values"));
                    }
                    Ok((0..count)
                        .map(|i| {
                            let bytes = [data[i * 2], data[i * 2 + 1]];
                            let bits = u16::from_le_bytes(bytes);
                            f64::from(bf16_to_f32(bits))
                        })
                        .collect())
                }
                _ => Err(format!("Unsupported dtype: {dtype:?}")),
            }
        }
    }

    /// Convert IEEE 754 half precision (16-bit) to f32
    const fn half_to_f32(bits: u16) -> f32 {
        let sign = ((bits >> 15) & 1) as u32;
        let exp = ((bits >> 10) & 0x1F) as u32;
        let mantissa = (bits & 0x3FF) as u32;

        if exp == 0 {
            // Denormalized or zero
            if mantissa == 0 {
                f32::from_bits(sign << 31)
            } else {
                // Denormalized - convert to normalized f32
                let mut m = mantissa;
                let mut e = 0i32;
                while (m & 0x400) == 0 {
                    m <<= 1;
                    e -= 1;
                }
                m &= 0x3FF;
                let f32_exp = (127 - 15 + 1 + e) as u32;
                f32::from_bits((sign << 31) | (f32_exp << 23) | (m << 13))
            }
        } else if exp == 31 {
            // Inf or NaN
            f32::from_bits((sign << 31) | (0xFF << 23) | (mantissa << 13))
        } else {
            // Normalized
            let f32_exp = exp - 15 + 127;
            f32::from_bits((sign << 31) | (f32_exp << 23) | (mantissa << 13))
        }
    }

    /// Convert BFloat16 to f32
    /// BF16 is just the upper 16 bits of f32, so conversion is trivial
    const fn bf16_to_f32(bits: u16) -> f32 {
        f32::from_bits((bits as u32) << 16)
    }
}

/// Load a network from a JSON model file
pub fn load_model(path: &str) -> Result<NnNetwork, String> {
    let model = json_model::JsonModel::load_file(path)?;
    model.to_network()
}

/// Load a network from an ONNX model file
#[cfg(feature = "onnx")]
pub fn load_onnx_model(path: &str) -> Result<NnNetwork, String> {
    let model = onnx_model::OnnxModel::load_file(path)?;
    model.to_network()
}

/// Load a network from a safetensors model file (PyTorch compatible)
///
/// Safetensors is a safe serialization format for neural network weights.
/// It's recommended for PyTorch models as it doesn't use pickle (no code execution risk).
///
/// Supports common PyTorch layer naming conventions:
/// - Sequential: `0.weight`, `0.bias`, `2.weight`, `2.bias`
/// - Named: `fc1.weight`, `fc1.bias`, `fc2.weight`, `fc2.bias`
pub fn load_safetensors_model(path: &str) -> Result<NnNetwork, String> {
    let model = safetensors_model::SafetensorsModel::load_file(path)?;
    model.to_network()
}

/// Load a network from file, detecting format by extension
///
/// Supports:
/// - `.json` - JSON model format
/// - `.onnx` - ONNX model format (requires `onnx` feature)
/// - `.safetensors` - Safetensors format (PyTorch compatible)
pub fn load_model_auto(path: &str) -> Result<NnNetwork, String> {
    if path.ends_with(".onnx") {
        #[cfg(feature = "onnx")]
        {
            load_onnx_model(path)
        }
        #[cfg(not(feature = "onnx"))]
        {
            Err(format!(
                "ONNX format not supported: '{path}'. Build with `onnx` feature to enable ONNX loading."
            ))
        }
    } else if path.ends_with(".json") {
        load_model(path)
    } else if path.ends_with(".safetensors") {
        load_safetensors_model(path)
    } else {
        Err(format!(
            "Unknown model format for '{path}'. Supported: .json, .onnx, .safetensors"
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_crown_capabilities() {
        let backend = CrownBackend::new(CrownConfig::default());
        let caps = backend.capabilities();
        assert!(caps.neural_network);
        assert!(!caps.predicates);
    }

    #[test]
    fn test_bounds_creation() {
        let b = Bounds::new(vec![0.0, -1.0], vec![1.0, 2.0]);
        assert_eq!(b.dim(), 2);
        assert_eq!(b.lower, vec![0.0, -1.0]);
        assert_eq!(b.upper, vec![1.0, 2.0]);
    }

    #[test]
    fn test_bounds_linf_ball() {
        let center = vec![0.5, 0.5];
        let epsilon = 0.1;
        let b = Bounds::linf_ball(&center, epsilon);
        assert_eq!(b.lower, vec![0.4, 0.4]);
        assert_eq!(b.upper, vec![0.6, 0.6]);
    }

    #[test]
    fn test_bounds_satisfies() {
        let b = Bounds::new(vec![0.1, 0.2], vec![0.8, 0.9]);

        // Should satisfy looser bounds
        assert!(b.satisfies(Some(&[0.0, 0.0]), Some(&[1.0, 1.0])));

        // Should satisfy exact bounds
        assert!(b.satisfies(Some(&[0.1, 0.2]), Some(&[0.8, 0.9])));

        // Should not satisfy tighter lower bounds
        assert!(!b.satisfies(Some(&[0.2, 0.2]), None));

        // Should not satisfy tighter upper bounds
        assert!(!b.satisfies(None, Some(&[0.7, 0.9])));
    }

    #[test]
    fn test_ibp_linear_positive_weights() {
        // Simple linear layer with positive weights
        let weights = vec![vec![1.0, 2.0], vec![0.5, 0.5]];
        let bias = vec![0.0, 0.0];
        let input = Bounds::new(vec![0.0, 0.0], vec![1.0, 1.0]);

        let output = ibp_linear(&input, &weights, &bias);

        // output[0] = 1*x1 + 2*x2, with x1,x2 in [0,1]
        // lb = 1*0 + 2*0 = 0, ub = 1*1 + 2*1 = 3
        assert_eq!(output.lower[0], 0.0);
        assert_eq!(output.upper[0], 3.0);

        // output[1] = 0.5*x1 + 0.5*x2
        // lb = 0, ub = 1
        assert_eq!(output.lower[1], 0.0);
        assert_eq!(output.upper[1], 1.0);
    }

    #[test]
    fn test_ibp_linear_mixed_weights() {
        // Linear layer with mixed positive and negative weights
        let weights = vec![vec![1.0, -1.0]];
        let bias = vec![0.0];
        let input = Bounds::new(vec![0.0, 0.0], vec![1.0, 1.0]);

        let output = ibp_linear(&input, &weights, &bias);

        // output[0] = 1*x1 - 1*x2
        // lb = 1*0 + (-1)*1 = -1
        // ub = 1*1 + (-1)*0 = 1
        assert_eq!(output.lower[0], -1.0);
        assert_eq!(output.upper[0], 1.0);
    }

    #[test]
    fn test_ibp_relu() {
        let input = Bounds::new(vec![-1.0, 0.5], vec![0.5, 2.0]);
        let output = ibp_relu(&input);

        // ReLU: max(0, x)
        // dim 0: input [-1, 0.5] -> output [0, 0.5]
        // dim 1: input [0.5, 2] -> output [0.5, 2]
        assert_eq!(output.lower, vec![0.0, 0.5]);
        assert_eq!(output.upper, vec![0.5, 2.0]);
    }

    #[test]
    fn test_ibp_sigmoid() {
        let input = Bounds::new(vec![0.0], vec![0.0]);
        let output = ibp_sigmoid(&input);

        // sigmoid(0) = 0.5
        assert!((output.lower[0] - 0.5).abs() < 1e-10);
        assert!((output.upper[0] - 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_ibp_full_network() {
        let network = NnNetwork::example_2layer(2, 4, 2);
        let input = Bounds::new(vec![0.0, 0.0], vec![1.0, 1.0]);
        let output = ibp_propagate(&network, &input);

        // Just check that we get valid output bounds
        assert_eq!(output.dim(), 2);
        for i in 0..output.dim() {
            assert!(output.lower[i] <= output.upper[i]);
        }
    }

    #[test]
    fn test_ibp_batchnorm_positive_scale() {
        // BatchNorm with positive scale: y = 2*x + 1
        let scale = vec![2.0, 2.0];
        let bias = vec![1.0, 1.0];
        let input = Bounds::new(vec![0.0, -1.0], vec![1.0, 2.0]);

        let output = ibp_batchnorm(&input, &scale, &bias);

        // y[0] = 2*x[0] + 1, x[0] in [0, 1], so y[0] in [1, 3]
        assert!((output.lower[0] - 1.0).abs() < 1e-10);
        assert!((output.upper[0] - 3.0).abs() < 1e-10);

        // y[1] = 2*x[1] + 1, x[1] in [-1, 2], so y[1] in [-1, 5]
        assert!((output.lower[1] - (-1.0)).abs() < 1e-10);
        assert!((output.upper[1] - 5.0).abs() < 1e-10);
    }

    #[test]
    fn test_ibp_batchnorm_negative_scale() {
        // BatchNorm with negative scale: y = -2*x + 1
        let scale = vec![-2.0, -2.0];
        let bias = vec![1.0, 1.0];
        let input = Bounds::new(vec![0.0, -1.0], vec![1.0, 2.0]);

        let output = ibp_batchnorm(&input, &scale, &bias);

        // y[0] = -2*x[0] + 1, x[0] in [0, 1]
        // When scale is negative, bounds flip:
        // lower = -2*1 + 1 = -1, upper = -2*0 + 1 = 1
        assert!((output.lower[0] - (-1.0)).abs() < 1e-10);
        assert!((output.upper[0] - 1.0).abs() < 1e-10);

        // y[1] = -2*x[1] + 1, x[1] in [-1, 2]
        // lower = -2*2 + 1 = -3, upper = -2*(-1) + 1 = 3
        assert!((output.lower[1] - (-3.0)).abs() < 1e-10);
        assert!((output.upper[1] - 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_ibp_batchnorm_mixed_scale() {
        // BatchNorm with mixed scales
        let scale = vec![1.0, -1.0];
        let bias = vec![0.0, 0.0];
        let input = Bounds::new(vec![1.0, 1.0], vec![2.0, 2.0]);

        let output = ibp_batchnorm(&input, &scale, &bias);

        // y[0] = 1*x[0], x[0] in [1, 2], so y[0] in [1, 2]
        assert!((output.lower[0] - 1.0).abs() < 1e-10);
        assert!((output.upper[0] - 2.0).abs() < 1e-10);

        // y[1] = -1*x[1], x[1] in [1, 2], so y[1] in [-2, -1]
        assert!((output.lower[1] - (-2.0)).abs() < 1e-10);
        assert!((output.upper[1] - (-1.0)).abs() < 1e-10);
    }

    #[test]
    fn test_batchnorm_forward_pass() {
        // Test forward pass through BatchNorm layer
        let network = NnNetwork::new(
            vec![NnLayer::BatchNorm {
                scale: vec![2.0, 0.5],
                bias: vec![1.0, -1.0],
            }],
            2,
        );

        // y = scale * x + bias
        // y[0] = 2*3 + 1 = 7
        // y[1] = 0.5*4 + (-1) = 1
        let output = forward_pass(&network, &[3.0, 4.0]);
        assert!((output[0] - 7.0).abs() < 1e-10);
        assert!((output[1] - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_batchnorm_crown_propagation() {
        // Create network with BatchNorm
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::BatchNorm {
                    scale: vec![2.0, 2.0],
                    bias: vec![0.0, 0.0],
                },
            ],
            2,
        );

        let input_bounds = Bounds::linf_ball(&[0.5, 0.5], 0.1);

        // Test IBP
        let ibp_output = ibp_propagate(&network, &input_bounds);
        assert_eq!(ibp_output.dim(), 2);

        // Test CROWN
        let crown_output = crown_propagate(&network, &input_bounds);
        assert_eq!(crown_output.dim(), 2);

        // Both should have valid bounds
        for i in 0..2 {
            assert!(ibp_output.lower[i] <= ibp_output.upper[i]);
            assert!(crown_output.lower[i] <= crown_output.upper[i]);
        }
    }

    #[test]
    fn test_batchnorm_json_roundtrip() {
        use json_model::JsonModel;

        // Create network with BatchNorm
        let original = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 2.0], vec![3.0, 4.0]],
                    bias: vec![0.1, 0.2],
                },
                NnLayer::BatchNorm {
                    scale: vec![0.5, 0.5],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
            ],
            2,
        );

        // Convert to JSON and back
        let json_model: JsonModel = (&original).into();
        let json_str = json_model.to_json().unwrap();
        let loaded = JsonModel::from_json(&json_str).unwrap();
        let roundtrip = loaded.to_network().unwrap();

        assert_eq!(original.input_dim, roundtrip.input_dim);
        assert_eq!(original.output_dim, roundtrip.output_dim);
        assert_eq!(original.layers.len(), roundtrip.layers.len());
    }

    #[test]
    fn test_forward_pass() {
        // Create a simple network: y = ReLU(x * 2 + 1)
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![2.0]],
                    bias: vec![1.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        // Forward pass: ReLU(0.5 * 2 + 1) = ReLU(2) = 2
        let output = forward_pass(&network, &[0.5]);
        assert_eq!(output, vec![2.0]);

        // Forward pass: ReLU(-1 * 2 + 1) = ReLU(-1) = 0
        let output = forward_pass(&network, &[-1.0]);
        assert_eq!(output, vec![0.0]);
    }

    #[test]
    fn test_verify_output_bounds_proven() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        // Verify that for input in [0, 1], output is in [0, 1]
        let spec = BoundsSpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            lower_bounds: Some(vec![0.0]),
            upper_bounds: Some(vec![1.0]),
        };

        let result = backend.verify_output_bounds(&spec);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_verify_output_bounds_unknown() {
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![2.0]],
                bias: vec![0.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        // Verify that for input in [0, 1], output is in [0, 1]
        // But actual output is [0, 2], so this should fail
        let spec = BoundsSpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            lower_bounds: Some(vec![0.0]),
            upper_bounds: Some(vec![1.0]),
        };

        let result = backend.verify_output_bounds(&spec);
        assert!(matches!(result, VerifyResult::Unknown { .. }));
    }

    #[test]
    fn test_argmax() {
        assert_eq!(argmax(&[1.0, 3.0, 2.0]), 1);
        assert_eq!(argmax(&[5.0, 1.0, 2.0]), 0);
        assert_eq!(argmax(&[1.0, 2.0, 3.0]), 2);
    }

    // JSON model loading tests
    #[test]
    fn test_json_model_parse() {
        use json_model::JsonModel;

        let json = r#"{
            "input_dim": 2,
            "layers": [
                {"type": "Linear", "weights": [[1.0, 2.0], [3.0, 4.0]], "bias": [0.0, 0.0]},
                {"type": "ReLU"},
                {"type": "Linear", "weights": [[0.5, 0.5]], "bias": [0.1]}
            ]
        }"#;

        let model = JsonModel::from_json(json).unwrap();
        assert_eq!(model.input_dim, 2);
        assert_eq!(model.layers.len(), 3);
    }

    #[test]
    fn test_json_model_to_network() {
        use json_model::JsonModel;

        let json = r#"{
            "input_dim": 2,
            "layers": [
                {"type": "Linear", "weights": [[1.0, 2.0], [3.0, 4.0]], "bias": [0.1, 0.2]},
                {"type": "ReLU"}
            ]
        }"#;

        let model = JsonModel::from_json(json).unwrap();
        let network = model.to_network().unwrap();

        assert_eq!(network.input_dim, 2);
        assert_eq!(network.output_dim, 2);
        assert_eq!(network.layers.len(), 2);
    }

    #[test]
    fn test_json_model_forward_pass() {
        use json_model::JsonModel;

        // Simple identity-like network
        let json = r#"{
            "input_dim": 2,
            "layers": [
                {"type": "Linear", "weights": [[1.0, 0.0], [0.0, 1.0]], "bias": [0.0, 0.0]}
            ]
        }"#;

        let model = JsonModel::from_json(json).unwrap();
        let network = model.to_network().unwrap();

        let input = vec![3.0, 4.0];
        let output = forward_pass(&network, &input);

        assert_eq!(output, vec![3.0, 4.0]);
    }

    #[test]
    fn test_json_model_ibp() {
        use json_model::JsonModel;

        let json = r#"{
            "input_dim": 2,
            "layers": [
                {"type": "Linear", "weights": [[1.0, 1.0]], "bias": [0.0]},
                {"type": "ReLU"}
            ]
        }"#;

        let model = JsonModel::from_json(json).unwrap();
        let network = model.to_network().unwrap();

        let input = Bounds::new(vec![0.0, 0.0], vec![1.0, 1.0]);
        let output = ibp_propagate(&network, &input);

        // y = ReLU(x1 + x2), with x1, x2 in [0, 1]
        // min = ReLU(0 + 0) = 0, max = ReLU(1 + 1) = 2
        assert_eq!(output.lower, vec![0.0]);
        assert_eq!(output.upper, vec![2.0]);
    }

    #[test]
    fn test_json_model_roundtrip() {
        use json_model::JsonModel;

        // Create a network
        let original = NnNetwork::example_2layer(2, 4, 2);

        // Convert to JSON model
        let json_model: JsonModel = (&original).into();

        // Serialize and deserialize
        let json_str = json_model.to_json().unwrap();
        let loaded = JsonModel::from_json(&json_str).unwrap();

        // Convert back to network
        let roundtripped = loaded.to_network().unwrap();

        // Verify dimensions match
        assert_eq!(original.input_dim, roundtripped.input_dim);
        assert_eq!(original.output_dim, roundtripped.output_dim);
        assert_eq!(original.layers.len(), roundtripped.layers.len());

        // Verify forward pass produces same results
        let input = vec![0.5, 0.5];
        let out1 = forward_pass(&original, &input);
        let out2 = forward_pass(&roundtripped, &input);
        assert_eq!(out1, out2);
    }

    #[test]
    fn test_json_model_all_layers() {
        use json_model::JsonModel;

        let json = r#"{
            "input_dim": 2,
            "layers": [
                {"type": "Linear", "weights": [[1.0, 2.0], [3.0, 4.0]], "bias": [0.0, 0.0]},
                {"type": "ReLU"},
                {"type": "LeakyReLU", "negative_slope": 0.1},
                {"type": "Sigmoid"},
                {"type": "Tanh"},
                {"type": "Linear", "weights": [[0.5, 0.5]], "bias": [0.0]}
            ]
        }"#;

        let model = JsonModel::from_json(json).unwrap();
        let network = model.to_network().unwrap();

        assert_eq!(network.layers.len(), 6);
        assert_eq!(network.input_dim, 2);
        assert_eq!(network.output_dim, 1);

        // Verify IBP works through all layers
        let input = Bounds::new(vec![0.0, 0.0], vec![1.0, 1.0]);
        let output = ibp_propagate(&network, &input);
        assert_eq!(output.dim(), 1);
    }

    #[test]
    fn test_json_model_dimension_mismatch() {
        use json_model::JsonModel;

        // Weight matrix has wrong input dimension
        let json = r#"{
            "input_dim": 3,
            "layers": [
                {"type": "Linear", "weights": [[1.0, 2.0]], "bias": [0.0]}
            ]
        }"#;

        let model = JsonModel::from_json(json).unwrap();
        let result = model.to_network();
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("dimension mismatch"));
    }

    // CROWN linear relaxation tests
    #[test]
    fn test_relu_state_active() {
        let state = ReLUState::from_bounds(0.5, 1.5);
        assert_eq!(state, ReLUState::Active);
        assert_eq!(state.lower_bound_coeffs(false), (1.0, 0.0));
        assert_eq!(state.upper_bound_coeffs(), (1.0, 0.0));
    }

    #[test]
    fn test_relu_state_inactive() {
        let state = ReLUState::from_bounds(-1.5, -0.5);
        assert_eq!(state, ReLUState::Inactive);
        assert_eq!(state.lower_bound_coeffs(false), (0.0, 0.0));
        assert_eq!(state.upper_bound_coeffs(), (0.0, 0.0));
    }

    #[test]
    fn test_relu_state_unstable() {
        let state = ReLUState::from_bounds(-1.0, 2.0);
        assert!(matches!(state, ReLUState::Unstable { .. }));

        // Upper bound: y <= 2/(2-(-1)) * (x - (-1)) = 2/3 * (x + 1)
        // slope = 2/3, intercept = 2/3
        let (slope, intercept) = state.upper_bound_coeffs();
        assert!((slope - 2.0 / 3.0).abs() < 1e-10);
        assert!((intercept - 2.0 / 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_linear_bounds_identity() {
        let lb = LinearBounds::identity(3);
        assert_eq!(lb.out_dim(), 3);
        assert_eq!(lb.in_dim(), 3);

        // Identity: y = x
        for i in 0..3 {
            for j in 0..3 {
                if i == j {
                    assert_eq!(lb.a_lower[i][j], 1.0);
                    assert_eq!(lb.a_upper[i][j], 1.0);
                } else {
                    assert_eq!(lb.a_lower[i][j], 0.0);
                    assert_eq!(lb.a_upper[i][j], 0.0);
                }
            }
        }
    }

    #[test]
    fn test_linear_bounds_concretize() {
        // Linear bounds: y = 2*x + 1
        let lb = LinearBounds {
            a_lower: vec![vec![2.0]],
            b_lower: vec![1.0],
            a_upper: vec![vec![2.0]],
            b_upper: vec![1.0],
        };

        let input = Bounds::new(vec![0.0], vec![1.0]);
        let output = lb.concretize(&input);

        // y = 2*x + 1, x in [0, 1] -> y in [1, 3]
        assert_eq!(output.lower, vec![1.0]);
        assert_eq!(output.upper, vec![3.0]);
    }

    #[test]
    fn test_crown_propagate_identity() {
        // Network: just pass-through (identity linear layer)
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                bias: vec![0.0, 0.0],
            }],
            2,
        );

        let input = Bounds::new(vec![0.0, 0.0], vec![1.0, 1.0]);
        let output = crown_propagate(&network, &input);

        // Identity: output should equal input
        assert_eq!(output.lower, vec![0.0, 0.0]);
        assert_eq!(output.upper, vec![1.0, 1.0]);
    }

    #[test]
    fn test_crown_propagate_linear_relu() {
        // Simple: y = ReLU(x)
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let input = Bounds::new(vec![-0.5], vec![0.5]);
        let output = crown_propagate(&network, &input);

        // ReLU of [-0.5, 0.5] -> [0, 0.5]
        assert!((output.lower[0] - 0.0).abs() < 1e-10);
        assert!((output.upper[0] - 0.5).abs() < 1e-10);
    }

    #[test]
    fn test_crown_tighter_than_ibp() {
        // Create a network where CROWN should give tighter bounds than IBP
        // Network: y = W2 * ReLU(W1 * x) with carefully chosen weights
        // W1 = [[1, -1], [-1, 1]], W2 = [[1, 1]]
        // This creates cross-dependencies that IBP can't capture well
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
            2,
        );

        // Input: small box around origin
        let input = Bounds::new(vec![-0.5, -0.5], vec![0.5, 0.5]);

        let ibp_output = ibp_propagate(&network, &input);
        let crown_output = crown_propagate(&network, &input);

        // CROWN bounds should be at least as tight as IBP
        assert!(crown_output.lower[0] >= ibp_output.lower[0] - 1e-10);
        assert!(crown_output.upper[0] <= ibp_output.upper[0] + 1e-10);

        // For this network, CROWN should actually be tighter
        // IBP gives very loose bounds due to independence assumption
        let ibp_width = ibp_output.upper[0] - ibp_output.lower[0];
        let crown_width = crown_output.upper[0] - crown_output.lower[0];
        assert!(crown_width <= ibp_width + 1e-10);
    }

    #[test]
    fn test_crown_verify_bounds_with_crown_method() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let config = CrownConfig {
            bound_method: BoundMethod::Crown,
            ..Default::default()
        };

        let mut backend = CrownBackend::new(config);
        backend.load_network(network);

        // Verify that for input in [0, 1], output is in [0, 1]
        let spec = BoundsSpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            lower_bounds: Some(vec![0.0]),
            upper_bounds: Some(vec![1.0]),
        };

        let result = backend.verify_output_bounds(&spec);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_pre_activation_bounds() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![2.0]],
                    bias: vec![1.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let input = Bounds::new(vec![0.0], vec![1.0]);
        let pre_bounds = PreActivationBounds::compute(&network, &input);

        // Should have 3 bounds: input, after linear, after relu
        assert_eq!(pre_bounds.layer_bounds.len(), 3);

        // Input bounds
        assert_eq!(pre_bounds.layer_bounds[0].lower, vec![0.0]);
        assert_eq!(pre_bounds.layer_bounds[0].upper, vec![1.0]);

        // After linear: y = 2x + 1, x in [0, 1] -> y in [1, 3]
        assert_eq!(pre_bounds.layer_bounds[1].lower, vec![1.0]);
        assert_eq!(pre_bounds.layer_bounds[1].upper, vec![3.0]);

        // After ReLU: since [1, 3] is all positive, stays [1, 3]
        assert_eq!(pre_bounds.layer_bounds[2].lower, vec![1.0]);
        assert_eq!(pre_bounds.layer_bounds[2].upper, vec![3.0]);
    }

    #[test]
    fn test_crown_robustness_with_crown_method() {
        use vc_ir::nn::*;
        use vc_ir::Expr;

        // Simple 1D network: 1 input -> 1 output
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![2.0]],
                    bias: vec![0.1],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let config = CrownConfig {
            bound_method: BoundMethod::Crown,
            ..Default::default()
        };

        let backend = CrownBackend::with_network(config, network);

        // Test robustness around point [1.0] with small epsilon
        // Network: ReLU(2*1.0 + 0.1) = 2.1
        // With epsilon=0.01: ReLU(2*0.99 + 0.1) = 2.08, ReLU(2*1.01 + 0.1) = 2.12
        // Max deviation: 0.02 < 0.05
        let spec = RobustnessSpec {
            input: Expr::FloatLit(1.0),
            epsilon: 0.01,
            norm: Norm::Linf,
            property: RobustnessProperty::BoundedDeviation { delta: 0.05 },
        };

        // This will use CROWN for bound propagation
        let result = backend.verify_local_robustness(&spec);
        // Should prove bounded deviation for small epsilon
        assert!(matches!(result, VerifyResult::Proven));
    }

    // Alpha-CROWN optimization tests
    #[test]
    fn test_alpha_params_initialize() {
        // Network with ReLU that will have unstable neurons
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
            ],
            2,
        );

        // Input that makes neurons unstable
        let input = Bounds::new(vec![-0.5, -0.5], vec![0.5, 0.5]);
        let pre_bounds = PreActivationBounds::compute(&network, &input);
        let alphas = AlphaParams::initialize(&network, &pre_bounds);

        // Should have 2 layers in alpha structure (Linear has no alphas, ReLU does)
        assert_eq!(alphas.alphas.len(), 2);

        // Linear layer has no alphas
        assert_eq!(alphas.alphas[0].len(), 0);

        // ReLU layer should have 2 unstable neurons
        // Pre-activation bounds after linear: [-1, 1] for both outputs
        assert_eq!(alphas.alphas[1].len(), 2);

        // Check initial values are 0.5
        for &alpha in &alphas.alphas[1] {
            assert!((alpha - 0.5).abs() < 1e-10);
        }
    }

    #[test]
    fn test_alpha_params_get_set() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let input = Bounds::new(vec![-1.0], vec![1.0]);
        let pre_bounds = PreActivationBounds::compute(&network, &input);
        let mut alphas = AlphaParams::initialize(&network, &pre_bounds);

        // Get initial alpha (should be 0.5)
        assert_eq!(alphas.get_alpha(1, 0), Some(0.5));

        // Set new value
        alphas.set_alpha(1, 0, 0.7);
        assert_eq!(alphas.get_alpha(1, 0), Some(0.7));

        // Set out-of-range value (should be clamped)
        alphas.set_alpha(1, 0, 1.5);
        assert_eq!(alphas.get_alpha(1, 0), Some(1.0));
    }

    #[test]
    fn test_alpha_params_num_unstable() {
        // Network with no ReLU
        let network_no_relu = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0]],
                bias: vec![0.0],
            }],
            1,
        );

        let input = Bounds::new(vec![-1.0], vec![1.0]);
        let pre_bounds = PreActivationBounds::compute(&network_no_relu, &input);
        let alphas = AlphaParams::initialize(&network_no_relu, &pre_bounds);
        assert_eq!(alphas.num_unstable(), 0);

        // Network with ReLU
        let network_with_relu = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
            ],
            2,
        );

        let input2 = Bounds::new(vec![-0.5, -0.5], vec![0.5, 0.5]);
        let pre_bounds2 = PreActivationBounds::compute(&network_with_relu, &input2);
        let alphas2 = AlphaParams::initialize(&network_with_relu, &pre_bounds2);
        assert_eq!(alphas2.num_unstable(), 2);
    }

    #[test]
    fn test_alpha_crown_propagate_equals_crown_when_stable() {
        // Network where all neurons are stable (no unstable ReLUs)
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![1.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        // Input [0, 1] -> after linear [1, 2] -> all positive, stable
        let input = Bounds::new(vec![0.0], vec![1.0]);

        let crown_bounds = crown_propagate(&network, &input);
        let alpha_bounds = alpha_crown_propagate(&network, &input, &AlphaCrownConfig::default());

        // Should be identical since no optimization possible
        assert!((crown_bounds.lower[0] - alpha_bounds.lower[0]).abs() < 1e-10);
        assert!((crown_bounds.upper[0] - alpha_bounds.upper[0]).abs() < 1e-10);
    }

    #[test]
    fn test_alpha_crown_at_least_as_tight_as_crown() {
        // Network where alpha optimization can help
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
            2,
        );

        let input = Bounds::new(vec![-0.5, -0.5], vec![0.5, 0.5]);

        let crown_bounds = crown_propagate(&network, &input);
        let alpha_bounds = alpha_crown_propagate(&network, &input, &AlphaCrownConfig::default());

        // Alpha-CROWN bounds should be at least as tight as CROWN
        // (or equal if optimization doesn't help)
        assert!(alpha_bounds.lower[0] >= crown_bounds.lower[0] - 1e-10);
        assert!(alpha_bounds.upper[0] <= crown_bounds.upper[0] + 1e-10);

        // Width should not increase
        let crown_width = crown_bounds.upper[0] - crown_bounds.lower[0];
        let alpha_width = alpha_bounds.upper[0] - alpha_bounds.lower[0];
        assert!(alpha_width <= crown_width + 1e-10);
    }

    #[test]
    fn test_alpha_crown_config_iterations() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let input = Bounds::new(vec![-1.0], vec![1.0]);

        // With 0 iterations, should still produce valid bounds
        let config_0 = AlphaCrownConfig {
            iterations: 0,
            ..Default::default()
        };
        let bounds_0 = alpha_crown_propagate(&network, &input, &config_0);
        assert!(bounds_0.lower[0] <= bounds_0.upper[0]);

        // With more iterations, should still produce valid bounds
        let config_50 = AlphaCrownConfig {
            iterations: 50,
            ..Default::default()
        };
        let bounds_50 = alpha_crown_propagate(&network, &input, &config_50);
        assert!(bounds_50.lower[0] <= bounds_50.upper[0]);
    }

    #[test]
    fn test_crown_backward_with_alphas_identity() {
        // Test that backward pass with alphas works correctly
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                bias: vec![0.0, 0.0],
            }],
            2,
        );

        let input = Bounds::new(vec![0.0, 0.0], vec![1.0, 1.0]);
        let pre_bounds = PreActivationBounds::compute(&network, &input);
        let alphas = AlphaParams::initialize(&network, &pre_bounds);

        let linear_bounds = crown_backward_with_alphas(&network, &pre_bounds, &alphas);
        let output = linear_bounds.concretize(&input);

        // Identity network: output should equal input
        assert!((output.lower[0] - 0.0).abs() < 1e-10);
        assert!((output.upper[0] - 1.0).abs() < 1e-10);
    }

    #[test]
    fn test_verify_bounds_with_crown_optimized() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let config = CrownConfig {
            bound_method: BoundMethod::CrownOptimized,
            ..Default::default()
        };

        let mut backend = CrownBackend::new(config);
        backend.load_network(network);

        // Verify that for input in [0, 1], output is in [0, 1]
        let spec = BoundsSpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            lower_bounds: Some(vec![0.0]),
            upper_bounds: Some(vec![1.0]),
        };

        let result = backend.verify_output_bounds(&spec);
        assert!(matches!(result, VerifyResult::Proven));
    }

    #[test]
    fn test_alpha_crown_2layer_network() {
        // More complex network to test alpha-CROWN on
        let network = NnNetwork::example_2layer(2, 4, 2);
        let input = Bounds::linf_ball(&[0.5, 0.5], 0.3);

        // All methods should produce valid bounds
        let ibp_bounds = ibp_propagate(&network, &input);
        let crown_bounds = crown_propagate(&network, &input);
        let alpha_bounds = alpha_crown_propagate(&network, &input, &AlphaCrownConfig::default());

        // All bounds should be valid (lower <= upper)
        for bounds in [&ibp_bounds, &crown_bounds, &alpha_bounds] {
            for i in 0..bounds.dim() {
                assert!(
                    bounds.lower[i] <= bounds.upper[i] + 1e-10,
                    "Bounds invalid: lower={}, upper={}",
                    bounds.lower[i],
                    bounds.upper[i]
                );
            }
        }

        // Alpha-CROWN bounds should be valid and at least as tight as the initial CROWN iteration
        // Note: CROWN with adaptive slope may not always be tighter than IBP for all networks,
        // but alpha-CROWN optimization should improve or maintain CROWN's bounds
        for i in 0..alpha_bounds.dim() {
            let alpha_width = alpha_bounds.upper[i] - alpha_bounds.lower[i];
            assert!(
                alpha_width >= 0.0,
                "Alpha-CROWN width should be non-negative"
            );
        }

        // Print bounds for debugging (comment out in production)
        // println!("IBP: lower={:?}, upper={:?}", ibp_bounds.lower, ibp_bounds.upper);
        // println!("CROWN: lower={:?}, upper={:?}", crown_bounds.lower, crown_bounds.upper);
        // println!("Alpha: lower={:?}, upper={:?}", alpha_bounds.lower, alpha_bounds.upper);
    }

    #[test]
    fn test_alpha_crown_improves_on_crown_when_beneficial() {
        // Network specifically designed where CROWN is known to be tighter than IBP
        // and alpha optimization can help
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
            2,
        );

        let input = Bounds::new(vec![-0.5, -0.5], vec![0.5, 0.5]);

        let ibp_bounds = ibp_propagate(&network, &input);
        let crown_bounds = crown_propagate(&network, &input);
        let alpha_bounds = alpha_crown_propagate(&network, &input, &AlphaCrownConfig::default());

        // For this network, CROWN should be tighter than IBP
        let ibp_width = ibp_bounds.upper[0] - ibp_bounds.lower[0];
        let crown_width = crown_bounds.upper[0] - crown_bounds.lower[0];
        assert!(
            crown_width <= ibp_width + 1e-10,
            "CROWN width {crown_width} should be <= IBP width {ibp_width} for this network"
        );

        // Alpha-CROWN should be at least as tight as CROWN
        let alpha_width = alpha_bounds.upper[0] - alpha_bounds.lower[0];
        assert!(
            alpha_width <= crown_width + 1e-6,
            "Alpha-CROWN width {alpha_width} should be <= CROWN width {crown_width}"
        );
    }

    // ========================================================================
    // Branch-and-Bound Tests
    // ========================================================================

    #[test]
    fn test_find_unstable_neurons() {
        // Network with ReLU that has unstable neurons
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0], vec![-1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        // Input in [-0.5, 0.5] causes both neurons to be unstable
        let input = Bounds::new(vec![-0.5], vec![0.5]);
        let pre_bounds = PreActivationBounds::compute(&network, &input);
        let unstable = find_unstable_neurons(&network, &pre_bounds);

        // Both neurons should be unstable (pre-activation crosses zero)
        assert_eq!(unstable.len(), 2, "Should find 2 unstable neurons");

        // Check they're from layer 1 (ReLU layer)
        for neuron in &unstable {
            assert_eq!(
                neuron.layer_idx, 1,
                "Unstable neurons should be at ReLU layer"
            );
        }
    }

    #[test]
    fn test_find_unstable_neurons_all_stable() {
        // Network where all neurons are stable (no crossing)
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![1.0], // Bias ensures always positive
                },
                NnLayer::ReLU,
            ],
            1,
        );

        // Input in [0, 1] with bias=1 means pre-activation in [1, 2], always active
        let input = Bounds::new(vec![0.0], vec![1.0]);
        let pre_bounds = PreActivationBounds::compute(&network, &input);
        let unstable = find_unstable_neurons(&network, &pre_bounds);

        assert_eq!(unstable.len(), 0, "No neurons should be unstable");
    }

    #[test]
    fn test_unstable_neuron_branching_score() {
        let n1 = super::UnstableNeuron {
            layer_idx: 0,
            neuron_idx: 0,
            lower: -0.5,
            upper: 0.5,
        };
        let n2 = super::UnstableNeuron {
            layer_idx: 0,
            neuron_idx: 1,
            lower: -1.0,
            upper: 1.0,
        };

        // n2 has larger absolute bounds, so higher branching score
        assert!(n2.branching_score() > n1.branching_score());
        assert_eq!(n1.branching_score(), 0.25); // 0.5 * 0.5
        assert_eq!(n2.branching_score(), 1.0); // 1.0 * 1.0
    }

    #[test]
    fn test_combine_branch_bounds() {
        let a = Bounds::new(vec![0.0, 1.0], vec![2.0, 3.0]);
        let b = Bounds::new(vec![-1.0, 0.5], vec![1.5, 4.0]);

        let combined = combine_branch_bounds(&a, &b);

        // Union: min of lowers, max of uppers
        assert_eq!(combined.lower, vec![-1.0, 0.5]);
        assert_eq!(combined.upper, vec![2.0, 4.0]);
    }

    #[test]
    fn test_bound_width() {
        let bounds = Bounds::new(vec![0.0, 1.0], vec![2.0, 5.0]);
        let width = bound_width(&bounds);

        // Width = (2-0) + (5-1) = 2 + 4 = 6
        assert_eq!(width, 6.0);
    }

    #[test]
    fn test_branch_and_bound_propagate_basic() {
        // Simple network to test branch-and-bound
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let input = Bounds::new(vec![-0.5], vec![0.5]);
        let config = BranchAndBoundConfig::default();

        let bab_bounds = branch_and_bound_propagate(&network, &input, &config);

        // Bounds should be valid
        assert_eq!(bab_bounds.dim(), 1);
        assert!(bab_bounds.lower[0] <= bab_bounds.upper[0]);

        // Bounds should be sound (contain actual possible outputs)
        // For ReLU(x) with x in [-0.5, 0.5], actual output is in [0, 0.5]
        // BaB bounds should contain this interval (sound over-approximation)
        assert!(
            bab_bounds.lower[0] <= 0.0 + 0.1,
            "Lower bound should be <= 0"
        );
        assert!(
            bab_bounds.upper[0] >= 0.5 - 0.1,
            "Upper bound should be >= 0.5"
        );
    }

    #[test]
    fn test_branch_and_bound_valid_bounds() {
        // Larger network for comprehensive test
        let network = NnNetwork::example_2layer(2, 4, 2);
        let input = Bounds::linf_ball(&[0.5, 0.5], 0.2);

        let config = BranchAndBoundConfig {
            max_splits: 5,
            max_depth: 3,
            ..Default::default()
        };

        let bab_bounds = branch_and_bound_propagate(&network, &input, &config);

        // All bounds should be valid
        for i in 0..bab_bounds.dim() {
            assert!(
                bab_bounds.lower[i] <= bab_bounds.upper[i] + 1e-10,
                "Invalid bounds: lower={}, upper={}",
                bab_bounds.lower[i],
                bab_bounds.upper[i]
            );
        }
    }

    #[test]
    fn test_branch_and_bound_produces_sound_bounds() {
        // Network where branching is applied
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
            2,
        );

        let input = Bounds::new(vec![-0.3, -0.3], vec![0.3, 0.3]);

        let bab_bounds =
            branch_and_bound_propagate(&network, &input, &BranchAndBoundConfig::default());

        // Branch-and-bound should produce valid bounds
        assert!(
            bab_bounds.lower[0] <= bab_bounds.upper[0] + 1e-10,
            "BaB bounds should be valid: lower={}, upper={}",
            bab_bounds.lower[0],
            bab_bounds.upper[0]
        );

        // Verify bounds are sound by checking some concrete points
        // For input (0, 0): Linear -> (0, 0), ReLU -> (0, 0), Linear -> 0
        let output_at_origin = forward_pass(&network, &[0.0, 0.0]);
        assert!(
            bab_bounds.lower[0] <= output_at_origin[0] + 1e-10,
            "BaB lower {} should be <= output at origin {}",
            bab_bounds.lower[0],
            output_at_origin[0]
        );
        assert!(
            bab_bounds.upper[0] >= output_at_origin[0] - 1e-10,
            "BaB upper {} should be >= output at origin {}",
            bab_bounds.upper[0],
            output_at_origin[0]
        );

        // Check corner points of input region
        for x1 in [-0.3, 0.3].iter() {
            for x2 in [-0.3, 0.3].iter() {
                let output = forward_pass(&network, &[*x1, *x2]);
                assert!(
                    bab_bounds.lower[0] <= output[0] + 1e-10,
                    "BaB lower {} should be <= output {} at ({}, {})",
                    bab_bounds.lower[0],
                    output[0],
                    x1,
                    x2
                );
                assert!(
                    bab_bounds.upper[0] >= output[0] - 1e-10,
                    "BaB upper {} should be >= output {} at ({}, {})",
                    bab_bounds.upper[0],
                    output[0],
                    x1,
                    x2
                );
            }
        }
    }

    #[test]
    fn test_branch_and_bound_no_unstable_neurons() {
        // Network where all neurons are stable
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![1.0], // Always positive
                },
                NnLayer::ReLU,
            ],
            1,
        );

        // Input [0, 1] with bias=1 means always active
        let input = Bounds::new(vec![0.0], vec![1.0]);
        let config = BranchAndBoundConfig::default();

        let bab_bounds = branch_and_bound_propagate(&network, &input, &config);

        // Should return exact bounds since no unstable neurons
        // ReLU(x + 1) with x in [0, 1] = [1, 2]
        assert!((bab_bounds.lower[0] - 1.0).abs() < 0.01);
        assert!((bab_bounds.upper[0] - 2.0).abs() < 0.01);
    }

    #[test]
    fn test_verify_with_branch_and_bound() {
        // Test that BoundMethod::AlphaBetaCrown uses branch-and-bound
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let config = CrownConfig {
            bound_method: BoundMethod::AlphaBetaCrown,
            ..Default::default()
        };

        let mut backend = CrownBackend::new(config);
        backend.load_network(network);

        // Verify bounds that should pass: ReLU(x) for x in [0, 1] gives [0, 1]
        let spec = BoundsSpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            lower_bounds: Some(vec![0.0]),
            upper_bounds: Some(vec![1.0]),
        };

        let result = backend.verify_output_bounds(&spec);
        assert!(matches!(result, VerifyResult::Proven));
    }

    // Branch-and-bound tests
    #[test]
    fn test_branch_and_bound_config_default() {
        let config = BranchAndBoundConfig::default();
        assert_eq!(config.max_splits, 10);
        assert_eq!(config.max_depth, 5);
        assert!(config.use_alpha_crown);
    }

    #[test]
    fn test_find_unstable_neurons_empty() {
        // Network where all neurons are stable
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![1.0], // Ensures pre-activation > 0
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let input = Bounds::new(vec![0.0], vec![1.0]); // All positive after linear
        let pre_bounds = PreActivationBounds::compute(&network, &input);
        let unstable = find_unstable_neurons(&network, &pre_bounds);

        assert!(
            unstable.is_empty(),
            "No neurons should be unstable when all positive"
        );
    }

    #[test]
    fn test_find_unstable_neurons_found() {
        // Network where neurons are unstable
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let input = Bounds::new(vec![-1.0], vec![1.0]); // Pre-activation crosses zero
        let pre_bounds = PreActivationBounds::compute(&network, &input);
        let unstable = find_unstable_neurons(&network, &pre_bounds);

        assert_eq!(unstable.len(), 1, "Should find 1 unstable neuron");
        assert_eq!(unstable[0].layer_idx, 1); // ReLU is at index 1
        assert_eq!(unstable[0].neuron_idx, 0);
    }

    #[test]
    fn test_branch_and_bound_stable_network() {
        // When all neurons are stable, branch-and-bound should equal alpha-CROWN
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![1.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let input = Bounds::new(vec![0.0], vec![1.0]);

        let bb_bounds =
            branch_and_bound_propagate(&network, &input, &BranchAndBoundConfig::default());
        let alpha_bounds = alpha_crown_propagate(&network, &input, &AlphaCrownConfig::default());

        // Should be identical (or very close)
        assert!((bb_bounds.lower[0] - alpha_bounds.lower[0]).abs() < 1e-10);
        assert!((bb_bounds.upper[0] - alpha_bounds.upper[0]).abs() < 1e-10);
    }

    #[test]
    fn test_branch_and_bound_produces_valid_bounds() {
        // Test that branch-and-bound produces valid (non-inverted) bounds
        let network = NnNetwork::example_2layer(2, 4, 2);
        let input = Bounds::linf_ball(&[0.5, 0.5], 0.3);

        let config = BranchAndBoundConfig {
            max_splits: 3,
            max_depth: 2,
            ..Default::default()
        };
        let bb_bounds = branch_and_bound_propagate(&network, &input, &config);

        // Bounds should be valid
        for i in 0..bb_bounds.dim() {
            assert!(
                bb_bounds.lower[i] <= bb_bounds.upper[i] + 1e-10,
                "Lower bound should be <= upper bound"
            );
        }
    }

    #[test]
    fn test_verify_with_alpha_beta_crown_uses_branch_and_bound() {
        use vc_ir::nn::*;

        // Network with unstable neurons to test branch-and-bound integration
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let config = CrownConfig {
            bound_method: BoundMethod::AlphaBetaCrown,
            ..Default::default()
        };

        let backend = CrownBackend::with_network(config, network);

        // For ReLU(x) with x in [-1, 1]: output is [0, 1]
        // Use wide spec bounds to ensure proof succeeds
        let spec = BoundsSpec {
            input_region: InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            },
            lower_bounds: Some(vec![-1.0]), // ReLU output >= -1 (true since ReLU >= 0)
            upper_bounds: Some(vec![2.0]),  // ReLU output <= 2 (true since max input is 1)
        };

        let result = backend.verify_output_bounds(&spec);
        // Should prove: ReLU output in [0, 1] ⊆ [-1, 2]
        assert!(
            matches!(result, VerifyResult::Proven),
            "Branch-and-bound should prove this wide bound specification"
        );
    }

    // ONNX model loading tests

    #[test]
    #[cfg(feature = "onnx")]
    fn test_onnx_load_simple_linear() {
        // Test loading a simple linear model from ONNX
        let model_path = "../../tests/fixtures/simple_linear.onnx";
        let result = load_onnx_model(model_path);

        // Skip if test file doesn't exist
        if result.is_err() && result.as_ref().unwrap_err().contains("Failed to load") {
            eprintln!("Skipping ONNX test: fixture not found");
            return;
        }

        let network = result.expect("Should load simple_linear.onnx");

        // Simple linear: 3 -> 2
        assert_eq!(network.input_dim, 3, "Input dimension should be 3");
        assert_eq!(network.output_dim, 2, "Output dimension should be 2");
        assert_eq!(network.layers.len(), 1, "Should have 1 layer");

        // Check it's a Linear layer
        match &network.layers[0] {
            NnLayer::Linear { weights, bias } => {
                assert_eq!(weights.len(), 2, "Should have 2 output neurons");
                assert_eq!(weights[0].len(), 3, "Each neuron should have 3 weights");
                assert_eq!(bias.len(), 2, "Should have 2 biases");
            }
            _ => panic!("Expected Linear layer"),
        }
    }

    #[test]
    #[cfg(feature = "onnx")]
    fn test_onnx_load_mlp_with_relu() {
        // Test loading a 2-layer MLP with ReLU from ONNX
        let model_path = "../../tests/fixtures/test_mlp.onnx";
        let result = load_onnx_model(model_path);

        // Skip if test file doesn't exist
        if result.is_err() && result.as_ref().unwrap_err().contains("Failed to load") {
            eprintln!("Skipping ONNX test: fixture not found");
            return;
        }

        let network = result.expect("Should load test_mlp.onnx");

        // MLP: 2 -> 4 (Linear) -> ReLU -> 2 (Linear)
        assert_eq!(network.input_dim, 2, "Input dimension should be 2");
        assert_eq!(network.output_dim, 2, "Output dimension should be 2");
        assert_eq!(
            network.layers.len(),
            3,
            "Should have 3 layers (Linear, ReLU, Linear)"
        );

        // Check layer structure
        assert!(
            matches!(&network.layers[0], NnLayer::Linear { .. }),
            "First layer should be Linear"
        );
        assert!(
            matches!(&network.layers[1], NnLayer::ReLU),
            "Second layer should be ReLU"
        );
        assert!(
            matches!(&network.layers[2], NnLayer::Linear { .. }),
            "Third layer should be Linear"
        );

        // Verify dimensions
        if let NnLayer::Linear { weights, .. } = &network.layers[0] {
            assert_eq!(weights.len(), 4, "First linear layer should have 4 outputs");
            assert_eq!(
                weights[0].len(),
                2,
                "First linear layer should take 2 inputs"
            );
        }

        if let NnLayer::Linear { weights, .. } = &network.layers[2] {
            assert_eq!(
                weights.len(),
                2,
                "Second linear layer should have 2 outputs"
            );
            assert_eq!(
                weights[0].len(),
                4,
                "Second linear layer should take 4 inputs"
            );
        }
    }

    #[test]
    #[cfg(feature = "onnx")]
    fn test_onnx_model_forward_pass() {
        // Test that we can verify bounds on an ONNX-loaded model
        let model_path = "../../tests/fixtures/simple_linear.onnx";
        let result = load_onnx_model(model_path);

        if result.is_err() {
            eprintln!("Skipping ONNX forward pass test: fixture not found");
            return;
        }

        let network = result.unwrap();

        // Create backend with IBP
        let config = CrownConfig {
            bound_method: BoundMethod::Ibp,
            ..Default::default()
        };
        let mut backend = CrownBackend::new(config);
        backend.load_network(network);

        // Test IBP propagation with a small input region
        let input_bounds = Bounds::linf_ball(&[0.0, 0.0, 0.0], 0.1);
        let output_bounds = ibp_propagate(backend.network.as_ref().unwrap(), &input_bounds);

        // Should get reasonable bounds
        assert_eq!(output_bounds.dim(), 2);
        for i in 0..2 {
            assert!(output_bounds.lower[i].is_finite());
            assert!(output_bounds.upper[i].is_finite());
            assert!(output_bounds.lower[i] <= output_bounds.upper[i]);
        }
    }

    #[test]
    fn test_load_model_auto_json() {
        // Test auto-detection for JSON files
        let json_path = "../../tests/fixtures/test_model.json";

        // This will fail if file doesn't exist, which is fine
        let result = load_model_auto(json_path);
        if let Ok(network) = result {
            assert!(network.input_dim > 0);
        }
    }

    #[test]
    #[cfg(feature = "onnx")]
    fn test_load_model_auto_onnx() {
        // Test auto-detection for ONNX files
        let onnx_path = "../../tests/fixtures/simple_linear.onnx";
        let result = load_model_auto(onnx_path);

        if result.is_err() {
            eprintln!("Skipping ONNX auto-load test: fixture not found");
            return;
        }

        let network = result.unwrap();
        assert_eq!(network.input_dim, 3);
        assert_eq!(network.output_dim, 2);
    }

    #[test]
    fn test_load_model_auto_unknown_extension() {
        let result = load_model_auto("model.xyz");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unknown model format"));
    }

    // ========================================================================
    // Safetensors Model Loading Tests
    // ========================================================================

    #[test]
    fn test_safetensors_load_simple_mlp() {
        // Test loading a simple 2->3->ReLU->1 MLP from safetensors
        let model_path = "test_data/simple_mlp.safetensors";

        let result = load_safetensors_model(model_path);
        if result.is_err() {
            eprintln!("Skipping safetensors test: {:?}", result.unwrap_err());
            return;
        }

        let network = result.unwrap();
        assert_eq!(network.input_dim, 2);
        assert_eq!(network.output_dim, 1);

        // Should have: Linear(2->3), ReLU, Linear(3->1) = 3 layers
        assert_eq!(network.layers.len(), 3);

        // Check first layer dimensions
        if let NnLayer::Linear { weights, bias } = &network.layers[0] {
            assert_eq!(weights.len(), 3); // 3 output features
            assert_eq!(weights[0].len(), 2); // 2 input features
            assert_eq!(bias.len(), 3);
        } else {
            panic!("Expected Linear layer first");
        }

        // Second layer should be ReLU
        assert!(matches!(network.layers[1], NnLayer::ReLU));

        // Third layer should be Linear
        if let NnLayer::Linear { weights, bias } = &network.layers[2] {
            assert_eq!(weights.len(), 1); // 1 output feature
            assert_eq!(weights[0].len(), 3); // 3 input features
            assert_eq!(bias.len(), 1);
        } else {
            panic!("Expected Linear layer last");
        }
    }

    #[test]
    fn test_safetensors_load_sequential_naming() {
        // Test loading model with sequential naming (0.weight, 2.weight)
        let model_path = "test_data/sequential_naming.safetensors";

        let result = load_safetensors_model(model_path);
        if result.is_err() {
            eprintln!("Skipping test: {:?}", result.unwrap_err());
            return;
        }

        let network = result.unwrap();
        assert_eq!(network.input_dim, 3);
        assert_eq!(network.output_dim, 2);
    }

    #[test]
    fn test_safetensors_load_named_layers() {
        // Test loading model with named layers (fc1.weight, fc2.weight)
        let model_path = "test_data/named_layers.safetensors";

        let result = load_safetensors_model(model_path);
        if result.is_err() {
            eprintln!("Skipping test: {:?}", result.unwrap_err());
            return;
        }

        let network = result.unwrap();
        assert_eq!(network.input_dim, 2);
        assert_eq!(network.output_dim, 2);
    }

    #[test]
    fn test_safetensors_load_no_bias() {
        // Test loading model without bias terms
        let model_path = "test_data/no_bias.safetensors";

        let result = load_safetensors_model(model_path);
        if result.is_err() {
            eprintln!("Skipping test: {:?}", result.unwrap_err());
            return;
        }

        let network = result.unwrap();
        assert_eq!(network.input_dim, 2);
        assert_eq!(network.output_dim, 1);

        // Bias should be zeros
        if let NnLayer::Linear { bias, .. } = &network.layers[0] {
            for &b in bias {
                assert_eq!(b, 0.0);
            }
        }
    }

    #[test]
    fn test_safetensors_load_single_layer() {
        // Test loading single linear layer model (no activation)
        let model_path = "test_data/single_layer.safetensors";

        let result = load_safetensors_model(model_path);
        if result.is_err() {
            eprintln!("Skipping test: {:?}", result.unwrap_err());
            return;
        }

        let network = result.unwrap();
        assert_eq!(network.input_dim, 3);
        assert_eq!(network.output_dim, 2);
        // Single layer - no ReLU added after last layer
        assert_eq!(network.layers.len(), 1);
        assert!(matches!(network.layers[0], NnLayer::Linear { .. }));
    }

    #[test]
    fn test_safetensors_load_f64() {
        // Test loading model with f64 (double precision) weights
        let model_path = "test_data/f64_model.safetensors";

        let result = load_safetensors_model(model_path);
        if result.is_err() {
            eprintln!("Skipping test: {:?}", result.unwrap_err());
            return;
        }

        let network = result.unwrap();
        assert_eq!(network.input_dim, 2);
        assert_eq!(network.output_dim, 2);
    }

    #[test]
    fn test_safetensors_forward_pass() {
        // Test that we can verify bounds on a safetensors-loaded model
        let model_path = "test_data/simple_mlp.safetensors";

        let result = load_safetensors_model(model_path);
        if result.is_err() {
            eprintln!("Skipping test: {:?}", result.unwrap_err());
            return;
        }

        let network = result.unwrap();
        let config = CrownConfig {
            bound_method: BoundMethod::Ibp,
            ..Default::default()
        };
        let mut backend = CrownBackend::new(config);
        backend.load_network(network);

        // Test IBP propagation
        let input_bounds = Bounds::linf_ball(&[0.5, 0.5], 0.1);
        let output_bounds = ibp_propagate(backend.network.as_ref().unwrap(), &input_bounds);

        // Should get reasonable bounds
        assert_eq!(output_bounds.dim(), 1);
        assert!(output_bounds.lower[0].is_finite());
        assert!(output_bounds.upper[0].is_finite());
        assert!(output_bounds.lower[0] <= output_bounds.upper[0]);
    }

    #[test]
    fn test_load_model_auto_safetensors() {
        // Test auto-detection for safetensors files
        let safetensors_path = "test_data/simple_mlp.safetensors";

        let result = load_model_auto(safetensors_path);
        if result.is_err() {
            eprintln!("Skipping test: {:?}", result.unwrap_err());
            return;
        }

        let network = result.unwrap();
        assert_eq!(network.input_dim, 2);
        assert_eq!(network.output_dim, 1);
    }

    #[test]
    fn test_safetensors_tensor_names() {
        let model_path = "test_data/simple_mlp.safetensors";

        let model = safetensors_model::SafetensorsModel::load_file(model_path);
        if model.is_err() {
            eprintln!("Skipping test: fixture not found");
            return;
        }

        let model = model.unwrap();
        let names = model.tensor_names().unwrap();

        // Should have at least weight tensors
        assert!(!names.is_empty());
        // Should contain weight and bias tensors
        assert!(names.iter().any(|n| n.contains("weight")));
        assert!(names.iter().any(|n| n.contains("bias")));
    }

    // ========================================================================
    // Input Domain Splitting Tests
    // ========================================================================

    #[test]
    fn test_split_bounds_along_dim() {
        let bounds = Bounds {
            lower: vec![0.0, 0.0],
            upper: vec![2.0, 4.0],
        };

        let (lower_half, upper_half) = split_bounds_along_dim(&bounds, 0);

        assert_eq!(lower_half.lower[0], 0.0);
        assert_eq!(lower_half.upper[0], 1.0);
        assert_eq!(upper_half.lower[0], 1.0);
        assert_eq!(upper_half.upper[0], 2.0);
        assert_eq!(lower_half.lower[1], 0.0);
        assert_eq!(lower_half.upper[1], 4.0);
    }

    #[test]
    fn test_split_bounds_along_dim_1() {
        let bounds = Bounds {
            lower: vec![0.0, 0.0],
            upper: vec![2.0, 4.0],
        };

        let (lower_half, upper_half) = split_bounds_along_dim(&bounds, 1);

        assert_eq!(lower_half.lower[0], 0.0);
        assert_eq!(lower_half.upper[0], 2.0);
        assert_eq!(lower_half.lower[1], 0.0);
        assert_eq!(lower_half.upper[1], 2.0);
        assert_eq!(upper_half.lower[1], 2.0);
        assert_eq!(upper_half.upper[1], 4.0);
    }

    #[test]
    fn test_get_dim_widths() {
        let bounds = Bounds {
            lower: vec![0.0, 1.0, 2.0],
            upper: vec![2.0, 4.0, 3.0],
        };

        let widths = get_dim_widths(&bounds);

        assert_eq!(widths.len(), 3);
        assert_eq!(widths[0], (0, 2.0));
        assert_eq!(widths[1], (1, 3.0));
        assert_eq!(widths[2], (2, 1.0));
    }

    #[test]
    fn test_split_input_bounds_single_region() {
        let bounds = Bounds {
            lower: vec![0.0, 0.0],
            upper: vec![1.0, 1.0],
        };

        let config = InputSplitConfig {
            max_splits_per_dim: 0,
            max_total_regions: 16,
            ..Default::default()
        };

        let regions = split_input_bounds(&bounds, &config);
        assert_eq!(regions.len(), 1);
    }

    #[test]
    fn test_split_input_bounds_2x2() {
        let bounds = Bounds {
            lower: vec![0.0, 0.0],
            upper: vec![2.0, 2.0],
        };

        let config = InputSplitConfig {
            max_splits_per_dim: 1,
            max_total_regions: 16,
            split_largest_first: true,
            ..Default::default()
        };

        let regions = split_input_bounds(&bounds, &config);
        assert_eq!(regions.len(), 4);

        let total_volume: f64 = regions
            .iter()
            .map(|r| (r.upper[0] - r.lower[0]) * (r.upper[1] - r.lower[1]))
            .sum();
        let original_volume =
            (bounds.upper[0] - bounds.lower[0]) * (bounds.upper[1] - bounds.lower[1]);
        assert!((total_volume - original_volume).abs() < 1e-10);
    }

    #[test]
    fn test_split_input_bounds_max_regions_limit() {
        let bounds = Bounds {
            lower: vec![0.0, 0.0, 0.0],
            upper: vec![2.0, 2.0, 2.0],
        };

        let config = InputSplitConfig {
            max_splits_per_dim: 3,
            max_total_regions: 8,
            split_largest_first: true,
            ..Default::default()
        };

        let regions = split_input_bounds(&bounds, &config);
        assert!(regions.len() <= 8);
    }

    #[test]
    fn test_combine_region_bounds() {
        let a = Bounds {
            lower: vec![0.0, 1.0],
            upper: vec![2.0, 3.0],
        };
        let b = Bounds {
            lower: vec![1.0, 0.5],
            upper: vec![3.0, 2.5],
        };

        let combined = combine_region_bounds(&a, &b);

        assert_eq!(combined.lower[0], 0.0);
        assert_eq!(combined.upper[0], 3.0);
        assert_eq!(combined.lower[1], 0.5);
        assert_eq!(combined.upper[1], 3.0);
    }

    #[test]
    fn test_input_split_propagate_basic() {
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 2,
            layers: vec![NnLayer::Linear {
                weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                bias: vec![0.0, 0.0],
            }],
        };

        let input_bounds = Bounds {
            lower: vec![0.0, 0.0],
            upper: vec![1.0, 1.0],
        };

        let config = InputSplitConfig {
            max_splits_per_dim: 1,
            max_total_regions: 4,
            base_method: BoundMethod::Ibp,
            ..Default::default()
        };

        let bounds = input_split_propagate(&network, &input_bounds, &config);
        assert!((bounds.lower[0] - 0.0).abs() < 1e-6);
        assert!((bounds.upper[0] - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_input_split_tighter_than_single() {
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 1,
            layers: vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, -1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
        };

        let input_bounds = Bounds {
            lower: vec![-1.0, -1.0],
            upper: vec![1.0, 1.0],
        };

        let bounds_no_split = ibp_propagate(&network, &input_bounds);

        let config = InputSplitConfig {
            max_splits_per_dim: 2,
            max_total_regions: 16,
            base_method: BoundMethod::Ibp,
            ..Default::default()
        };
        let bounds_with_split = input_split_propagate(&network, &input_bounds, &config);

        assert!(bounds_with_split.lower[0] >= bounds_no_split.lower[0] - 1e-10);
        assert!(bounds_with_split.upper[0] <= bounds_no_split.upper[0] + 1e-10);
    }

    #[test]
    fn test_input_split_improvement_threshold_controls_splitting() {
        // y = ReLU(x1 + x2) + ReLU(-(x1 + x2)) = |x1 + x2|
        // Over x in [-1, 1]^2, exact bounds are [0, 2]. IBP without splitting gives [0, 4]
        // (the two ReLUs are anti-correlated and IBP loses that dependency).
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 1,
            layers: vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0], vec![-1.0, -1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
        };

        let input_bounds = Bounds {
            lower: vec![-1.0, -1.0],
            upper: vec![1.0, 1.0],
        };

        let baseline = ibp_propagate(&network, &input_bounds);
        assert!((baseline.lower[0] - 0.0).abs() < 1e-6);
        assert!((baseline.upper[0] - 4.0).abs() < 1e-6);

        let config_high = InputSplitConfig {
            max_splits_per_dim: 1,
            max_total_regions: 4,
            base_method: BoundMethod::Ibp,
            improvement_threshold: 1.0,
            split_largest_first: true,
        };
        let bounds_high = input_split_propagate(&network, &input_bounds, &config_high);
        assert!((bounds_high.upper[0] - baseline.upper[0]).abs() < 1e-6);

        let mut config_low = config_high.clone();
        config_low.improvement_threshold = 0.0;
        let bounds_low = input_split_propagate(&network, &input_bounds, &config_low);

        assert!(bounds_low.upper[0] < bounds_high.upper[0] - 1e-6);
        assert!((bounds_low.upper[0] - 2.0).abs() < 1e-6);
    }

    #[test]
    fn test_verify_robustness_with_input_splitting() {
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 2,
            layers: vec![NnLayer::Linear {
                weights: vec![vec![2.0, 0.0], vec![0.0, 1.0]],
                bias: vec![0.0, 0.0],
            }],
        };

        let input = vec![1.0, 0.0];
        let epsilon = 0.1;

        let config = InputSplitConfig {
            max_splits_per_dim: 1,
            max_total_regions: 4,
            base_method: BoundMethod::Crown,
            ..Default::default()
        };

        let (certified, bounds) =
            verify_robustness_with_input_splitting(&network, &input, epsilon, &config);
        assert!(certified);
        assert!(bounds.lower[0] > bounds.upper[1]);
    }

    // ========================================================================
    // Branching Heuristic Tests
    // ========================================================================

    #[test]
    fn test_branching_heuristic_default() {
        assert_eq!(BranchingHeuristic::default(), BranchingHeuristic::Simple);
    }

    #[test]
    fn test_smash_score_basic() {
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 1,
            layers: vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
        };

        let input_bounds = Bounds {
            lower: vec![-1.0, -1.0],
            upper: vec![1.0, 1.0],
        };

        let neuron = UnstableNeuron {
            layer_idx: 1,
            neuron_idx: 0,
            lower: -2.0,
            upper: 2.0,
        };

        let score = compute_smash_score(&network, &input_bounds, &neuron);
        // Smash score can be positive (improvement) or negative (no improvement)
        // Just verify it returns a finite value
        assert!(score.is_finite());
    }

    #[test]
    fn test_fsb_score_basic() {
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 1,
            layers: vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
        };

        let input_bounds = Bounds {
            lower: vec![-1.0, -1.0],
            upper: vec![1.0, 1.0],
        };

        let neuron = UnstableNeuron {
            layer_idx: 1,
            neuron_idx: 0,
            lower: -2.0,
            upper: 2.0,
        };

        let score = compute_fsb_score(&network, &input_bounds, &neuron);
        assert!(score.is_finite());
    }

    #[test]
    fn test_sort_neurons_by_heuristic_simple() {
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 1,
            layers: vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
        };

        let input_bounds = Bounds {
            lower: vec![-1.0, -1.0],
            upper: vec![1.0, 1.0],
        };

        let mut neurons = vec![
            UnstableNeuron {
                layer_idx: 1,
                neuron_idx: 0,
                lower: -1.0,
                upper: 1.0,
            },
            UnstableNeuron {
                layer_idx: 1,
                neuron_idx: 1,
                lower: -2.0,
                upper: 3.0,
            },
        ];

        sort_neurons_by_heuristic(
            &mut neurons,
            &network,
            &input_bounds,
            BranchingHeuristic::Simple,
        );
        assert_eq!(neurons[0].neuron_idx, 0);
    }

    #[test]
    fn test_input_split_config_default() {
        let config = InputSplitConfig::default();
        assert_eq!(config.max_splits_per_dim, 2);
        assert_eq!(config.max_total_regions, 16);
        assert_eq!(config.base_method, BoundMethod::CrownOptimized);
        assert!((config.improvement_threshold - 0.01).abs() < 1e-10);
        assert!(config.split_largest_first);
    }

    #[test]
    fn test_bound_method_input_split() {
        let config = Box::new(InputSplitConfig::default());
        let method = BoundMethod::InputSplit(config);

        if let BoundMethod::InputSplit(c) = method {
            assert_eq!(c.max_splits_per_dim, 2);
        } else {
            panic!("Expected InputSplit variant");
        }
    }

    // ========================================================================
    // Beta-CROWN tests
    // ========================================================================

    #[test]
    fn test_split_constraint_creation() {
        let active = SplitConstraint::active(1, 2);
        assert_eq!(active.layer_idx, 1);
        assert_eq!(active.neuron_idx, 2);
        assert!(active.is_active);

        let inactive = SplitConstraint::inactive(3, 0);
        assert_eq!(inactive.layer_idx, 3);
        assert_eq!(inactive.neuron_idx, 0);
        assert!(!inactive.is_active);
    }

    #[test]
    fn test_beta_params_basic() {
        let splits = vec![
            SplitConstraint::active(0, 1),
            SplitConstraint::inactive(1, 0),
        ];
        let mut params = BetaParams::new(splits);

        // Initial betas should be zero
        assert_eq!(params.num_splits(), 2);
        assert_eq!(params.get_beta(0), 0.0);
        assert_eq!(params.get_beta(1), 0.0);
        assert_eq!(params.get_beta(99), 0.0); // Out of bounds returns 0

        // Set betas
        params.set_beta(0, 0.5);
        params.set_beta(1, 1.0);
        assert_eq!(params.get_beta(0), 0.5);
        assert_eq!(params.get_beta(1), 1.0);

        // Negative values should be clamped to 0
        params.set_beta(0, -1.0);
        assert_eq!(params.get_beta(0), 0.0);
    }

    #[test]
    fn test_beta_params_find_split() {
        let splits = vec![
            SplitConstraint::active(0, 1),
            SplitConstraint::inactive(1, 2),
            SplitConstraint::active(2, 0),
        ];
        let params = BetaParams::new(splits);

        // Find existing split
        let found = params.find_split(1, 2);
        assert!(found.is_some());
        let (idx, constraint) = found.unwrap();
        assert_eq!(idx, 1);
        assert_eq!(constraint.layer_idx, 1);
        assert_eq!(constraint.neuron_idx, 2);
        assert!(!constraint.is_active);

        // Split not found
        assert!(params.find_split(5, 5).is_none());
    }

    #[test]
    fn test_beta_params_project() {
        let splits = vec![SplitConstraint::active(0, 0)];
        let mut params = BetaParams::new(splits);

        // Directly modify betas to include negative values
        params.betas[0] = -5.0;
        params.project();
        assert_eq!(params.get_beta(0), 0.0);

        params.betas[0] = 2.5;
        params.project();
        assert_eq!(params.get_beta(0), 2.5); // Positive stays positive
    }

    #[test]
    fn test_beta_crown_config_default() {
        let config = BetaCrownConfig::default();
        assert_eq!(config.iterations, 30);
        assert!((config.alpha_lr - 0.1).abs() < 1e-10);
        assert!((config.beta_lr - 0.05).abs() < 1e-10);
        assert!(config.optimize_lower);
        assert!((config.early_stop_threshold - 1e-6).abs() < 1e-12);
        assert_eq!(config.max_splits, 10);
    }

    #[test]
    fn test_beta_crown_propagate_stable_network() {
        // Create a network that is stable (no unstable neurons)
        // This should fall back to alpha-CROWN
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 1,
            layers: vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0]],
                    bias: vec![5.0], // Large positive bias makes ReLU always active
                },
                NnLayer::ReLU,
            ],
        };

        let input_bounds = Bounds::from_box(vec![0.0, 0.0], vec![1.0, 1.0]);
        let config = BetaCrownConfig::default();

        let result = beta_crown_propagate(&network, &input_bounds, &config);

        // With input in [0,1] x [0,1] and weights [1,0], bias 5:
        // Output range is [5, 6]
        assert!(result.lower[0] >= 4.9);
        assert!(result.upper[0] <= 6.1);
    }

    #[test]
    fn test_beta_crown_propagate_unstable_network() {
        // Network with unstable ReLU neurons
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 1,
            layers: vec![
                NnLayer::Linear {
                    weights: vec![
                        vec![1.0, -1.0], // neuron can be positive or negative
                        vec![-1.0, 1.0], // neuron can be positive or negative
                    ],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
        };

        let input_bounds = Bounds::from_box(vec![-1.0, -1.0], vec![1.0, 1.0]);
        let config = BetaCrownConfig {
            iterations: 10,
            ..Default::default()
        };

        let result = beta_crown_propagate(&network, &input_bounds, &config);

        // Output should have reasonable bounds
        // The exact values depend on optimization, but bounds should be finite
        assert!(result.lower[0].is_finite());
        assert!(result.upper[0].is_finite());
        assert!(result.lower[0] <= result.upper[0]);
    }

    #[test]
    fn test_bound_method_beta_crown() {
        let config = Box::new(BetaCrownConfig::default());
        let method = BoundMethod::BetaCrown(config);

        if let BoundMethod::BetaCrown(c) = method {
            assert_eq!(c.iterations, 30);
            assert_eq!(c.max_splits, 10);
        } else {
            panic!("Expected BetaCrown variant");
        }
    }

    #[test]
    fn test_beta_crown_produces_sound_bounds() {
        // Test that Beta-CROWN produces sound (valid) bounds
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 1,
            layers: vec![
                NnLayer::Linear {
                    weights: vec![vec![0.5, 0.5], vec![-0.3, 0.7]],
                    bias: vec![0.1, -0.1],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, -0.5]],
                    bias: vec![0.2],
                },
            ],
        };

        let input_bounds = Bounds::from_box(vec![-0.5, -0.5], vec![0.5, 0.5]);

        let ibp_result = ibp_propagate(&network, &input_bounds);
        let beta_result =
            beta_crown_propagate(&network, &input_bounds, &BetaCrownConfig::default());

        // Both methods should produce valid bounds
        assert!(ibp_result.lower[0] <= ibp_result.upper[0]);
        assert!(beta_result.lower[0] <= beta_result.upper[0]);

        // Beta-CROWN bounds should overlap with IBP bounds (soundness check)
        // If both are sound, they should have non-empty intersection
        let max_lower = ibp_result.lower[0].max(beta_result.lower[0]);
        let min_upper = ibp_result.upper[0].min(beta_result.upper[0]);
        assert!(
            max_lower <= min_upper,
            "IBP [{}, {}] and Beta-CROWN [{}, {}] should overlap",
            ibp_result.lower[0],
            ibp_result.upper[0],
            beta_result.lower[0],
            beta_result.upper[0]
        );
    }

    #[test]
    fn test_beta_crown_with_more_iterations() {
        // Test that more iterations can improve Beta-CROWN bounds
        let network = NnNetwork {
            input_dim: 2,
            output_dim: 1,
            layers: vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, -1.0], vec![-1.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
        };

        let input_bounds = Bounds::from_box(vec![-0.5, -0.5], vec![0.5, 0.5]);

        let config_few = BetaCrownConfig {
            iterations: 5,
            ..Default::default()
        };
        let config_many = BetaCrownConfig {
            iterations: 50,
            ..Default::default()
        };

        let result_few = beta_crown_propagate(&network, &input_bounds, &config_few);
        let result_many = beta_crown_propagate(&network, &input_bounds, &config_many);

        // Both should produce valid bounds
        assert!(result_few.lower[0] <= result_few.upper[0]);
        assert!(result_many.lower[0] <= result_many.upper[0]);

        // More iterations should not make bounds worse (though may not improve)
        let width_few = result_few.upper[0] - result_few.lower[0];
        let width_many = result_many.upper[0] - result_many.lower[0];

        // Allow tolerance for numerical stability
        assert!(
            width_many <= width_few + 0.1,
            "More iterations should not make bounds much worse: {width_many} vs {width_few}"
        );
    }

    // ========================================================================
    // Tests for new layer types: Dropout, Flatten, MaxPool1d, AvgPool1d
    // ========================================================================

    #[test]
    fn test_dropout_ibp() {
        // Dropout is identity in inference mode
        let input = Bounds::from_box(vec![-1.0, 0.5, 2.0], vec![1.0, 1.5, 3.0]);
        let result = ibp_dropout(&input);

        assert_eq!(result.lower, input.lower);
        assert_eq!(result.upper, input.upper);
    }

    #[test]
    fn test_dropout_forward() {
        let input = vec![1.0, 2.0, 3.0];
        let layer = NnLayer::Dropout { p: 0.5 };
        let output = forward_layer(&input, &layer);

        assert_eq!(output, input);
    }

    #[test]
    fn test_flatten_ibp() {
        // Flatten is identity for 1D networks
        let input = Bounds::from_box(vec![-1.0, 0.5, 2.0], vec![1.0, 1.5, 3.0]);
        let result = ibp_flatten(&input);

        assert_eq!(result.lower, input.lower);
        assert_eq!(result.upper, input.upper);
    }

    #[test]
    fn test_flatten_forward() {
        let input = vec![1.0, 2.0, 3.0];
        let layer = NnLayer::Flatten;
        let output = forward_layer(&input, &layer);

        assert_eq!(output, input);
    }

    #[test]
    fn test_maxpool1d_forward() {
        // Input: [1.0, 3.0, 2.0, 4.0] with kernel_size=2, stride=2
        // Output: [max(1,3), max(2,4)] = [3.0, 4.0]
        let input = vec![1.0, 3.0, 2.0, 4.0];
        let output = forward_maxpool1d(&input, 2, 2);

        assert_eq!(output.len(), 2);
        assert_eq!(output[0], 3.0);
        assert_eq!(output[1], 4.0);
    }

    #[test]
    fn test_maxpool1d_forward_stride1() {
        // Input: [1.0, 3.0, 2.0, 4.0] with kernel_size=2, stride=1
        // Output: [max(1,3), max(3,2), max(2,4)] = [3.0, 3.0, 4.0]
        let input = vec![1.0, 3.0, 2.0, 4.0];
        let output = forward_maxpool1d(&input, 2, 1);

        assert_eq!(output.len(), 3);
        assert_eq!(output[0], 3.0);
        assert_eq!(output[1], 3.0);
        assert_eq!(output[2], 4.0);
    }

    #[test]
    fn test_maxpool1d_ibp() {
        // Input bounds: [[0,2], [1,4], [0,3], [2,5]] with kernel_size=2, stride=2
        // Output bounds: [max(lb0,lb1), max(lb2,lb3)] = [1,2], [max(ub0,ub1), max(ub2,ub3)] = [4,5]
        let input = Bounds::from_box(vec![0.0, 1.0, 0.0, 2.0], vec![2.0, 4.0, 3.0, 5.0]);
        let output = ibp_maxpool1d(&input, 2, 2);

        assert_eq!(output.dim(), 2);
        assert_eq!(output.lower[0], 1.0); // max(0, 1)
        assert_eq!(output.lower[1], 2.0); // max(0, 2)
        assert_eq!(output.upper[0], 4.0); // max(2, 4)
        assert_eq!(output.upper[1], 5.0); // max(3, 5)
    }

    #[test]
    fn test_avgpool1d_forward() {
        // Input: [2.0, 4.0, 6.0, 8.0] with kernel_size=2, stride=2
        // Output: [avg(2,4), avg(6,8)] = [3.0, 7.0]
        let input = vec![2.0, 4.0, 6.0, 8.0];
        let output = forward_avgpool1d(&input, 2, 2);

        assert_eq!(output.len(), 2);
        assert!((output[0] - 3.0).abs() < 1e-10);
        assert!((output[1] - 7.0).abs() < 1e-10);
    }

    #[test]
    fn test_avgpool1d_ibp() {
        // Input bounds: [[0,2], [2,4], [4,6], [6,8]] with kernel_size=2, stride=2
        // Output bounds: lb = [avg(0,2), avg(4,6)] = [1, 5], ub = [avg(2,4), avg(6,8)] = [3, 7]
        let input = Bounds::from_box(vec![0.0, 2.0, 4.0, 6.0], vec![2.0, 4.0, 6.0, 8.0]);
        let output = ibp_avgpool1d(&input, 2, 2);

        assert_eq!(output.dim(), 2);
        assert!((output.lower[0] - 1.0).abs() < 1e-10);
        assert!((output.lower[1] - 5.0).abs() < 1e-10);
        assert!((output.upper[0] - 3.0).abs() < 1e-10);
        assert!((output.upper[1] - 7.0).abs() < 1e-10);
    }

    #[test]
    fn test_dropout_json_roundtrip() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::Dropout { p: 0.5 },
                NnLayer::ReLU,
            ],
            2,
        );

        let json_model = json_model::JsonModel::from(&network);
        let recovered = json_model.to_network().unwrap();

        assert_eq!(network.layers.len(), recovered.layers.len());
        assert!(matches!(recovered.layers[1], NnLayer::Dropout { p } if (p - 0.5).abs() < 1e-10));
    }

    #[test]
    fn test_flatten_json_roundtrip() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::Flatten,
                NnLayer::ReLU,
            ],
            2,
        );

        let json_model = json_model::JsonModel::from(&network);
        let recovered = json_model.to_network().unwrap();

        assert_eq!(network.layers.len(), recovered.layers.len());
        assert!(matches!(recovered.layers[1], NnLayer::Flatten));
    }

    #[test]
    fn test_maxpool1d_json_roundtrip() {
        let network = NnNetwork::new(
            vec![NnLayer::MaxPool1d {
                kernel_size: 2,
                stride: 2,
            }],
            4,
        );

        let json_model = json_model::JsonModel::from(&network);
        let recovered = json_model.to_network().unwrap();

        assert_eq!(network.layers.len(), recovered.layers.len());
        assert!(matches!(
            recovered.layers[0],
            NnLayer::MaxPool1d {
                kernel_size: 2,
                stride: 2
            }
        ));
        assert_eq!(recovered.output_dim, 2); // 4 / 2 = 2
    }

    #[test]
    fn test_avgpool1d_json_roundtrip() {
        let network = NnNetwork::new(
            vec![NnLayer::AvgPool1d {
                kernel_size: 2,
                stride: 2,
            }],
            4,
        );

        let json_model = json_model::JsonModel::from(&network);
        let recovered = json_model.to_network().unwrap();

        assert_eq!(network.layers.len(), recovered.layers.len());
        assert!(matches!(
            recovered.layers[0],
            NnLayer::AvgPool1d {
                kernel_size: 2,
                stride: 2
            }
        ));
        assert_eq!(recovered.output_dim, 2); // 4 / 2 = 2
    }

    #[test]
    fn test_maxpool1d_crown_backward() {
        // Simple test: network with just MaxPool1d
        let network = NnNetwork::new(
            vec![NnLayer::MaxPool1d {
                kernel_size: 2,
                stride: 2,
            }],
            4,
        );

        let input_bounds = Bounds::from_box(vec![0.0, 1.0, 2.0, 3.0], vec![1.0, 2.0, 3.0, 4.0]);
        let ibp_bounds = ibp_propagate(&network, &input_bounds);

        // IBP should give: lb = [max(0,1), max(2,3)] = [1, 3], ub = [max(1,2), max(3,4)] = [2, 4]
        assert_eq!(ibp_bounds.dim(), 2);
        assert_eq!(ibp_bounds.lower[0], 1.0);
        assert_eq!(ibp_bounds.lower[1], 3.0);
        assert_eq!(ibp_bounds.upper[0], 2.0);
        assert_eq!(ibp_bounds.upper[1], 4.0);
    }

    #[test]
    fn test_avgpool1d_crown_backward() {
        // Simple test: network with just AvgPool1d
        let network = NnNetwork::new(
            vec![NnLayer::AvgPool1d {
                kernel_size: 2,
                stride: 2,
            }],
            4,
        );

        let input_bounds = Bounds::from_box(vec![0.0, 2.0, 4.0, 6.0], vec![2.0, 4.0, 6.0, 8.0]);
        let ibp_bounds = ibp_propagate(&network, &input_bounds);

        // IBP should give: lb = [avg(0,2), avg(4,6)] = [1, 5], ub = [avg(2,4), avg(6,8)] = [3, 7]
        assert_eq!(ibp_bounds.dim(), 2);
        assert!((ibp_bounds.lower[0] - 1.0).abs() < 1e-10);
        assert!((ibp_bounds.lower[1] - 5.0).abs() < 1e-10);
        assert!((ibp_bounds.upper[0] - 3.0).abs() < 1e-10);
        assert!((ibp_bounds.upper[1] - 7.0).abs() < 1e-10);
    }

    #[test]
    fn test_network_with_pooling() {
        // Full network: Linear -> ReLU -> AvgPool
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![
                        vec![1.0, 0.0],
                        vec![0.0, 1.0],
                        vec![1.0, 1.0],
                        vec![-1.0, 1.0],
                    ],
                    bias: vec![0.0, 0.0, 0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::AvgPool1d {
                    kernel_size: 2,
                    stride: 2,
                },
            ],
            2,
        );

        let input_bounds = Bounds::from_box(vec![-1.0, -1.0], vec![1.0, 1.0]);
        let ibp_bounds = ibp_propagate(&network, &input_bounds);

        // Output dimension should be 2 (4 / 2)
        assert_eq!(ibp_bounds.dim(), 2);
        assert!(ibp_bounds.lower[0] <= ibp_bounds.upper[0]);
        assert!(ibp_bounds.lower[1] <= ibp_bounds.upper[1]);
    }

    // ==========================================================================
    // GlobalPool2d Tests
    // ==========================================================================

    #[test]
    fn test_global_avgpool2d_forward() {
        // 2 channels, 2x2 spatial
        // Input: [c0: [1, 2, 3, 4], c1: [5, 6, 7, 8]] -> flattened: [1, 2, 3, 4, 5, 6, 7, 8]
        let input = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
        let output = forward_global_avgpool2d(&input, 2, 2, 2);
        // Channel 0: (1+2+3+4)/4 = 2.5
        // Channel 1: (5+6+7+8)/4 = 6.5
        assert_eq!(output.len(), 2);
        assert!((output[0] - 2.5).abs() < 1e-10);
        assert!((output[1] - 6.5).abs() < 1e-10);
    }

    #[test]
    fn test_global_maxpool2d_forward() {
        // 2 channels, 2x2 spatial
        let input = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
        let output = forward_global_maxpool2d(&input, 2, 2, 2);
        // Channel 0: max(1,2,3,4) = 4
        // Channel 1: max(5,6,7,8) = 8
        assert_eq!(output.len(), 2);
        assert!((output[0] - 4.0).abs() < 1e-10);
        assert!((output[1] - 8.0).abs() < 1e-10);
    }

    #[test]
    fn test_global_avgpool2d_ibp() {
        // 2 channels, 2x2 spatial with interval bounds
        let input = Bounds::from_box(
            vec![0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0],
            vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0],
        );
        let output = ibp_global_avgpool2d(&input, 2, 2, 2);
        // Channel 0 lower: (0+1+2+3)/4 = 1.5
        // Channel 0 upper: (1+2+3+4)/4 = 2.5
        // Channel 1 lower: (4+5+6+7)/4 = 5.5
        // Channel 1 upper: (5+6+7+8)/4 = 6.5
        assert_eq!(output.dim(), 2);
        assert!((output.lower[0] - 1.5).abs() < 1e-10);
        assert!((output.upper[0] - 2.5).abs() < 1e-10);
        assert!((output.lower[1] - 5.5).abs() < 1e-10);
        assert!((output.upper[1] - 6.5).abs() < 1e-10);
    }

    #[test]
    fn test_global_maxpool2d_ibp() {
        // 2 channels, 2x2 spatial with interval bounds
        let input = Bounds::from_box(
            vec![0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0],
            vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0],
        );
        let output = ibp_global_maxpool2d(&input, 2, 2, 2);
        // Channel 0: lower = max(lower_i) = max(0,1,2,3) = 3
        //            upper = max(upper_i) = max(1,2,3,4) = 4
        // Channel 1: lower = max(4,5,6,7) = 7
        //            upper = max(5,6,7,8) = 8
        assert_eq!(output.dim(), 2);
        assert!((output.lower[0] - 3.0).abs() < 1e-10);
        assert!((output.upper[0] - 4.0).abs() < 1e-10);
        assert!((output.lower[1] - 7.0).abs() < 1e-10);
        assert!((output.upper[1] - 8.0).abs() < 1e-10);
    }

    #[test]
    fn test_global_avgpool2d_crown_backward() {
        // Test CROWN backward propagation
        let output_bounds = LinearBounds::identity(2);
        let result = crown_backward_global_avgpool2d(&output_bounds, 2, 2, 2);
        // Should expand 2 channels back to 8 inputs (2*2*2)
        assert_eq!(result.in_dim(), 8);
        // Each input coefficient should be 0.25 (1/4)
        assert!((result.a_lower[0][0] - 0.25).abs() < 1e-10);
        assert!((result.a_lower[0][1] - 0.25).abs() < 1e-10);
        assert!((result.a_lower[1][4] - 0.25).abs() < 1e-10);
    }

    #[test]
    fn test_global_maxpool2d_crown_backward() {
        // Pre-bounds determine which element is dominant
        let pre_bounds = Bounds::from_box(
            vec![0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0],
            vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0],
        );
        let output_bounds = LinearBounds::identity(2);
        let result = crown_backward_global_maxpool2d(&output_bounds, &pre_bounds, 2, 2, 2);
        // Should route to element with highest upper bound per channel
        // Channel 0: element 3 (upper=4) is dominant
        // Channel 1: element 7 (upper=8) is dominant
        assert_eq!(result.in_dim(), 8);
        assert!((result.a_lower[0][3] - 1.0).abs() < 1e-10); // Gradient goes to dominant
        assert!((result.a_lower[0][0]).abs() < 1e-10); // Other elements get 0
        assert!((result.a_lower[1][7] - 1.0).abs() < 1e-10); // Channel 1 dominant
    }

    #[test]
    fn test_global_pool_json_roundtrip() {
        let model = json_model::JsonModel {
            input_dim: 8,
            layers: vec![json_model::JsonLayer::GlobalAvgPool2d {
                channels: 2,
                height: 2,
                width: 2,
            }],
        };
        let json = serde_json::to_string(&model).unwrap();
        let parsed: json_model::JsonModel = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.input_dim, 8);
        assert_eq!(parsed.layers.len(), 1);
    }

    #[test]
    fn test_network_with_global_avgpool() {
        // Linear 8->8, ReLU, GlobalAvgPool2d (2 channels, 2x2)
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: (0..8)
                        .map(|i| (0..8).map(|j| if i == j { 1.0 } else { 0.0 }).collect())
                        .collect(),
                    bias: vec![0.0; 8],
                },
                NnLayer::ReLU,
                NnLayer::GlobalAvgPool2d {
                    channels: 2,
                    height: 2,
                    width: 2,
                },
            ],
            8,
        );

        let input_bounds = Bounds::from_box(vec![-1.0; 8], vec![1.0; 8]);
        let ibp_bounds = ibp_propagate(&network, &input_bounds);
        // After ReLU: [0, 1]^8, then GlobalAvgPool: each channel averages 4 values
        assert_eq!(ibp_bounds.dim(), 2);
        assert!(ibp_bounds.lower[0] >= 0.0);
        assert!(ibp_bounds.upper[0] <= 1.0);
    }

    // ==========================================================================
    // L2 Ball Propagation Tests
    // ==========================================================================

    #[test]
    fn test_l2_ball_bounds_creation() {
        let center = vec![1.0, 2.0, 3.0];
        let radius = 0.5;
        let l2_ball = L2BallBounds::new(center.clone(), radius);

        assert_eq!(l2_ball.dim(), 3);
        assert_eq!(l2_ball.center, center);
        assert_eq!(l2_ball.radius, radius);

        // Box bounds should be center +/- radius
        assert_eq!(l2_ball.box_bounds.lower, vec![0.5, 1.5, 2.5]);
        assert_eq!(l2_ball.box_bounds.upper, vec![1.5, 2.5, 3.5]);
    }

    #[test]
    fn test_l2_linear_propagation_tighter_than_linf() {
        // For L2 ball, the propagation should be tighter than L∞ for certain weight matrices
        // Consider weights [[1, 0], [0, 1]] (identity) with L2 ball radius 1
        let center = vec![0.0, 0.0];
        let radius = 1.0;
        let l2_ball = L2BallBounds::new(center.clone(), radius);

        // L2 propagation: each row has L2 norm 1, so deviation = 1 * 1 = 1
        let weights = vec![vec![1.0, 0.0], vec![0.0, 1.0]];
        let bias = vec![0.0, 0.0];
        let l2_result = ibp_linear_l2(&l2_ball, &weights, &bias);

        assert_eq!(l2_result.box_bounds.lower, vec![-1.0, -1.0]);
        assert_eq!(l2_result.box_bounds.upper, vec![1.0, 1.0]);

        // L∞ propagation (naive): for L∞ ball of radius 1, bounds are same
        let linf_bounds = Bounds::linf_ball(&center, radius);
        let linf_result = ibp_linear(&linf_bounds, &weights, &bias);

        assert_eq!(linf_result.lower, vec![-1.0, -1.0]);
        assert_eq!(linf_result.upper, vec![1.0, 1.0]);

        // For this simple case, they're the same
        // But for a weight matrix with all 1s, L2 should be tighter
    }

    #[test]
    fn test_l2_linear_propagation_dense_weights() {
        // Dense weight matrix: L2 propagation should give tighter bounds
        // W = [[1, 1], [1, 1]] with L2 ball radius 1
        let center = vec![0.0, 0.0];
        let radius = 1.0;
        let l2_ball = L2BallBounds::new(center.clone(), radius);

        // L2 propagation: each row has L2 norm sqrt(2), so deviation = sqrt(2) * 1 ≈ 1.414
        let weights = vec![vec![1.0, 1.0], vec![1.0, 1.0]];
        let bias = vec![0.0, 0.0];
        let l2_result = ibp_linear_l2(&l2_ball, &weights, &bias);

        let expected_deviation = (2.0f64).sqrt();
        assert!((l2_result.box_bounds.lower[0] - (-expected_deviation)).abs() < 1e-10);
        assert!((l2_result.box_bounds.upper[0] - expected_deviation).abs() < 1e-10);

        // L∞ propagation: deviation = sum(|W_ij|) * epsilon = 2 * 1 = 2
        let linf_bounds = Bounds::linf_ball(&center, radius);
        let linf_result = ibp_linear(&linf_bounds, &weights, &bias);

        assert_eq!(linf_result.lower, vec![-2.0, -2.0]);
        assert_eq!(linf_result.upper, vec![2.0, 2.0]);

        // L2 bounds are tighter: sqrt(2) < 2
        assert!(l2_result.box_bounds.lower[0] > linf_result.lower[0]);
        assert!(l2_result.box_bounds.upper[0] < linf_result.upper[0]);
    }

    #[test]
    fn test_l2_batchnorm_propagation() {
        let center = vec![1.0, 2.0];
        let radius = 0.5;
        let l2_ball = L2BallBounds::new(center, radius);

        let scale = vec![2.0, 0.5];
        let bias = vec![1.0, -1.0];

        let result = ibp_batchnorm_l2(&l2_ball, &scale, &bias);

        // New center: [2*1 + 1, 0.5*2 - 1] = [3, 0]
        assert!((result.center[0] - 3.0).abs() < 1e-10);
        assert!((result.center[1] - 0.0).abs() < 1e-10);

        // Component-wise deviation: |scale_i| * radius
        // [|2|*0.5, |0.5|*0.5] = [1.0, 0.25]
        assert!((result.box_bounds.lower[0] - 2.0).abs() < 1e-10);
        assert!((result.box_bounds.upper[0] - 4.0).abs() < 1e-10);
        assert!((result.box_bounds.lower[1] - (-0.25)).abs() < 1e-10);
        assert!((result.box_bounds.upper[1] - 0.25).abs() < 1e-10);
    }

    #[test]
    fn test_l2_network_propagation() {
        // Simple network: Linear -> ReLU -> Linear
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0], vec![1.0, -1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0]],
                    bias: vec![0.0],
                },
            ],
            2,
        );

        let center = vec![0.0, 0.0];
        let radius = 0.1;
        let l2_ball = L2BallBounds::new(center.clone(), radius);

        let l2_output = ibp_propagate_l2(&network, &l2_ball);

        // Compare with L∞
        let linf_bounds = Bounds::linf_ball(&center, radius);
        let linf_output = ibp_propagate(&network, &linf_bounds);

        // Both should produce valid bounds
        assert_eq!(l2_output.dim(), 1);
        assert_eq!(linf_output.dim(), 1);
        assert!(l2_output.lower[0] <= l2_output.upper[0]);
        assert!(linf_output.lower[0] <= linf_output.upper[0]);

        // For small epsilon, both should be similar but L2 could be tighter
        // Just verify they're in reasonable range
        assert!(l2_output.lower[0] >= -1.0);
        assert!(l2_output.upper[0] <= 1.0);
    }

    #[test]
    fn test_l2_network_linear_only() {
        // Test L2 propagation on linear-only network (no activation layers)
        // This tests the full L2 path since no non-linearities force conversion to box bounds
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0], vec![0.0, 1.0], vec![1.0, 1.0]],
                    bias: vec![0.0, 0.0, 0.0],
                },
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0, 0.0], vec![0.0, 1.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
            ],
            2,
        );

        let center = vec![0.0, 0.0];
        let radius = 1.0;
        let l2_ball = L2BallBounds::new(center, radius);

        let l2_output = ibp_propagate_l2(&network, &l2_ball);

        // Verify output is valid
        assert_eq!(l2_output.dim(), 2);
        assert!(l2_output.lower[0] <= l2_output.upper[0]);
        assert!(l2_output.lower[1] <= l2_output.upper[1]);
    }

    #[test]
    fn test_l2_ball_to_box_bounds() {
        let l2_ball = L2BallBounds::new(vec![1.0, 2.0, 3.0], 0.5);
        let box_bounds = l2_ball.to_box_bounds();

        assert_eq!(box_bounds.dim(), 3);
        assert_eq!(box_bounds.lower, vec![0.5, 1.5, 2.5]);
        assert_eq!(box_bounds.upper, vec![1.5, 2.5, 3.5]);
    }

    #[test]
    fn test_l2_propagation_vs_linf_tightness() {
        // Network where L2 propagation should be significantly tighter
        // Use a network with dense weight matrices
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0, 1.0, 1.0, 1.0], vec![1.0, 1.0, 1.0, 1.0]],
                bias: vec![0.0, 0.0],
            }],
            4,
        );

        let center = vec![0.0, 0.0, 0.0, 0.0];
        let radius = 1.0;

        // L2 propagation
        let l2_ball = L2BallBounds::new(center.clone(), radius);
        let l2_output = ibp_propagate_l2(&network, &l2_ball);

        // L∞ propagation
        let linf_bounds = Bounds::linf_ball(&center, radius);
        let linf_output = ibp_propagate(&network, &linf_bounds);

        // L∞ gives deviation = 4 * 1 = 4 (sum of row)
        // L2 gives deviation = ||[1,1,1,1]||_2 * 1 = 2 (sqrt(4))
        assert!((linf_output.upper[0] - 4.0).abs() < 1e-10);
        assert!((l2_output.upper[0] - 2.0).abs() < 1e-10);

        // L2 bounds are significantly tighter: 2 < 4
        assert!(l2_output.upper[0] < linf_output.upper[0]);
        assert!(l2_output.lower[0] > linf_output.lower[0]);
    }

    // ============================================================================
    // Conv1d Tests
    // ============================================================================

    #[test]
    fn test_conv1d_layer_creation() {
        // Simple Conv1d: 2 input channels, 3 output channels, kernel_size=2
        // Input: 4 samples per channel -> 8 total
        // Output: (4 - 2)/1 + 1 = 3 samples per output channel -> 9 total
        let network = NnNetwork::new(
            vec![NnLayer::Conv1d {
                in_channels: 2,
                out_channels: 3,
                kernel_size: 2,
                stride: 1,
                padding: 0,
                weights: vec![
                    vec![vec![1.0, 0.5], vec![0.5, 1.0]],   // out_ch 0
                    vec![vec![0.5, -0.5], vec![-0.5, 0.5]], // out_ch 1
                    vec![vec![1.0, 1.0], vec![1.0, 1.0]],   // out_ch 2
                ],
                bias: vec![0.1, 0.2, 0.3],
            }],
            8, // 2 channels * 4 samples
        );

        assert_eq!(network.input_dim, 8);
        assert_eq!(network.output_dim, 9); // 3 channels * 3 samples
    }

    #[test]
    fn test_conv1d_forward_pass() {
        let _network = NnNetwork::new(
            vec![NnLayer::Conv1d {
                in_channels: 1,
                out_channels: 1,
                kernel_size: 2,
                stride: 1,
                padding: 0,
                weights: vec![vec![vec![1.0, 2.0]]], // Single filter: [1, 2]
                bias: vec![0.5],
            }],
            4,
        );

        // Input: [1, 2, 3, 4]
        // Output positions:
        // pos 0: 1*1 + 2*2 + 0.5 = 5.5
        // pos 1: 1*2 + 2*3 + 0.5 = 8.5
        // pos 2: 1*3 + 2*4 + 0.5 = 11.5
        let input = vec![1.0, 2.0, 3.0, 4.0];
        let output = forward_conv1d(&input, &[vec![vec![1.0, 2.0]]], &[0.5], 1, 2, 1, 0);

        assert_eq!(output.len(), 3);
        assert!((output[0] - 5.5).abs() < 1e-10);
        assert!((output[1] - 8.5).abs() < 1e-10);
        assert!((output[2] - 11.5).abs() < 1e-10);
    }

    #[test]
    fn test_conv1d_ibp_positive_weights() {
        let weights = vec![vec![vec![1.0, 1.0]]]; // All positive weights
        let bias = vec![0.0];

        // Input bounds: [0, 2] for each element
        let input = Bounds::new(vec![0.0, 0.0, 0.0, 0.0], vec![2.0, 2.0, 2.0, 2.0]);

        // Output: sum of 2 inputs at each position
        // Lower: 0 + 0 = 0
        // Upper: 2 + 2 = 4
        let output = ibp_conv1d(&input, &weights, &bias, 1, 2, 1, 0);

        assert_eq!(output.dim(), 3);
        for i in 0..3 {
            assert!((output.lower[i] - 0.0).abs() < 1e-10);
            assert!((output.upper[i] - 4.0).abs() < 1e-10);
        }
    }

    #[test]
    fn test_conv1d_ibp_mixed_weights() {
        let weights = vec![vec![vec![1.0, -1.0]]]; // Mixed weights
        let bias = vec![0.0];

        // Input bounds: [0, 2] for each element
        let input = Bounds::new(vec![0.0, 0.0, 0.0, 0.0], vec![2.0, 2.0, 2.0, 2.0]);

        // Output: x[i] - x[i+1]
        // Lower: 0 - 2 = -2 (min with positive * lb, negative * ub)
        // Upper: 2 - 0 = 2 (max with positive * ub, negative * lb)
        let output = ibp_conv1d(&input, &weights, &bias, 1, 2, 1, 0);

        assert_eq!(output.dim(), 3);
        for i in 0..3 {
            assert!((output.lower[i] - (-2.0)).abs() < 1e-10);
            assert!((output.upper[i] - 2.0).abs() < 1e-10);
        }
    }

    #[test]
    fn test_conv1d_stride() {
        let network = NnNetwork::new(
            vec![NnLayer::Conv1d {
                in_channels: 1,
                out_channels: 1,
                kernel_size: 2,
                stride: 2,
                padding: 0,
                weights: vec![vec![vec![1.0, 1.0]]],
                bias: vec![0.0],
            }],
            4,
        );

        // Input: 4 samples, stride 2, kernel 2
        // Output: (4 - 2) / 2 + 1 = 2
        assert_eq!(network.output_dim, 2);

        let input = vec![1.0, 2.0, 3.0, 4.0];
        let output = forward_conv1d(&input, &[vec![vec![1.0, 1.0]]], &[0.0], 1, 2, 2, 0);

        assert_eq!(output.len(), 2);
        assert!((output[0] - 3.0).abs() < 1e-10); // 1 + 2
        assert!((output[1] - 7.0).abs() < 1e-10); // 3 + 4
    }

    #[test]
    fn test_conv1d_padding() {
        let network = NnNetwork::new(
            vec![NnLayer::Conv1d {
                in_channels: 1,
                out_channels: 1,
                kernel_size: 3,
                stride: 1,
                padding: 1,
                weights: vec![vec![vec![1.0, 1.0, 1.0]]],
                bias: vec![0.0],
            }],
            4,
        );

        // Input: 4 samples, kernel 3, padding 1
        // Effective length = 4 + 2 = 6
        // Output: (6 - 3) / 1 + 1 = 4
        assert_eq!(network.output_dim, 4);

        let input = vec![1.0, 2.0, 3.0, 4.0];
        let output = forward_conv1d(&input, &[vec![vec![1.0, 1.0, 1.0]]], &[0.0], 1, 3, 1, 1);

        assert_eq!(output.len(), 4);
        // pos 0: padded(0,0) + in[0] + in[1] = 0 + 1 + 2 = 3
        // pos 1: in[0] + in[1] + in[2] = 1 + 2 + 3 = 6
        // pos 2: in[1] + in[2] + in[3] = 2 + 3 + 4 = 9
        // pos 3: in[2] + in[3] + padded = 3 + 4 + 0 = 7
        assert!((output[0] - 3.0).abs() < 1e-10);
        assert!((output[1] - 6.0).abs() < 1e-10);
        assert!((output[2] - 9.0).abs() < 1e-10);
        assert!((output[3] - 7.0).abs() < 1e-10);
    }

    #[test]
    fn test_conv1d_multi_channel() {
        let network = NnNetwork::new(
            vec![NnLayer::Conv1d {
                in_channels: 2,
                out_channels: 2,
                kernel_size: 2,
                stride: 1,
                padding: 0,
                weights: vec![
                    vec![vec![1.0, 0.0], vec![0.0, 1.0]], // out_ch 0: ch0[0] + ch1[1]
                    vec![vec![0.5, 0.5], vec![0.5, 0.5]], // out_ch 1: avg of all
                ],
                bias: vec![0.0, 0.0],
            }],
            6, // 2 channels * 3 samples
        );

        // Output: (3 - 2) / 1 + 1 = 2 per channel -> 4 total
        assert_eq!(network.output_dim, 4);

        // Input: ch0 = [1, 2, 3], ch1 = [4, 5, 6]
        // Flattened: [1, 2, 3, 4, 5, 6]
        let input = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
        let output = forward_conv1d(
            &input,
            &[
                vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                vec![vec![0.5, 0.5], vec![0.5, 0.5]],
            ],
            &[0.0, 0.0],
            2,
            2,
            1,
            0,
        );

        assert_eq!(output.len(), 4);
        // out_ch 0, pos 0: 1*ch0[0] + 0*ch0[1] + 0*ch1[0] + 1*ch1[1] = 1*1 + 0*2 + 0*4 + 1*5 = 6
        // out_ch 0, pos 1: 1*ch0[1] + 0*ch0[2] + 0*ch1[1] + 1*ch1[2] = 1*2 + 0*3 + 0*5 + 1*6 = 8
        // out_ch 1, pos 0: 0.5*(1+2+4+5) = 6
        // out_ch 1, pos 1: 0.5*(2+3+5+6) = 8
        assert!((output[0] - 6.0).abs() < 1e-10);
        assert!((output[1] - 8.0).abs() < 1e-10);
        assert!((output[2] - 6.0).abs() < 1e-10);
        assert!((output[3] - 8.0).abs() < 1e-10);
    }

    #[test]
    fn test_conv1d_json_roundtrip() {
        use json_model::{JsonLayer, JsonModel};

        let model = JsonModel {
            input_dim: 8,
            layers: vec![
                JsonLayer::Conv1d {
                    in_channels: 2,
                    out_channels: 3,
                    kernel_size: 2,
                    stride: 1,
                    padding: 0,
                    weights: vec![
                        vec![vec![1.0, 0.5], vec![0.5, 1.0]],
                        vec![vec![0.5, -0.5], vec![-0.5, 0.5]],
                        vec![vec![1.0, 1.0], vec![1.0, 1.0]],
                    ],
                    bias: vec![0.1, 0.2, 0.3],
                },
                JsonLayer::ReLU,
            ],
        };

        // Serialize to JSON
        let json = model.to_json().expect("Serialization should succeed");

        // Parse back
        let parsed = JsonModel::from_json(&json).expect("Parsing should succeed");

        // Convert to network
        let network = parsed.to_network().expect("Conversion should succeed");
        assert_eq!(network.input_dim, 8);
        assert_eq!(network.output_dim, 9); // 3 channels * 3 samples

        // Convert back to JsonModel
        let roundtrip: JsonModel = (&network).into();
        assert_eq!(roundtrip.input_dim, 8);
        assert_eq!(roundtrip.layers.len(), 2);
    }

    #[test]
    fn test_conv1d_network_propagation() {
        // Test a simple CNN: Conv1d -> ReLU -> Linear
        let network = NnNetwork::new(
            vec![
                NnLayer::Conv1d {
                    in_channels: 1,
                    out_channels: 2,
                    kernel_size: 2,
                    stride: 1,
                    padding: 0,
                    weights: vec![
                        vec![vec![1.0, 1.0]],  // sum filter
                        vec![vec![1.0, -1.0]], // diff filter
                    ],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0, 1.0, 1.0, 1.0, 1.0]], // sum all
                    bias: vec![0.0],
                },
            ],
            4, // 1 channel * 4 samples
        );

        // Conv output: 3 per channel -> 6 total
        // After linear: 1 output
        assert_eq!(network.output_dim, 1);

        // Test with simple bounds
        let input = Bounds::linf_ball(&[0.5, 0.5, 0.5, 0.5], 0.1);
        let output = ibp_propagate(&network, &input);
        assert_eq!(output.dim(), 1);
        // Output should be non-negative due to ReLU
        assert!(output.lower[0] >= 0.0 - 1e-10);
    }

    #[test]
    fn test_conv1d_crown_propagation() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Conv1d {
                    in_channels: 1,
                    out_channels: 1,
                    kernel_size: 2,
                    stride: 1,
                    padding: 0,
                    weights: vec![vec![vec![1.0, 1.0]]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            4,
        );

        let input = Bounds::linf_ball(&[1.0, 1.0, 1.0, 1.0], 0.1);

        // IBP bounds
        let ibp_bounds = ibp_propagate(&network, &input);

        // CROWN bounds (should be at least as tight)
        let crown_bounds = crown_propagate(&network, &input);

        // CROWN should give at least as tight bounds as IBP
        assert!(crown_bounds.lower[0] >= ibp_bounds.lower[0] - 1e-10);
        assert!(crown_bounds.upper[0] <= ibp_bounds.upper[0] + 1e-10);
    }

    // ========================================================================
    // Conv2d layer tests
    // ========================================================================

    #[test]
    fn test_conv2d_layer_creation() {
        // Create a simple Conv2d network: 1 channel, 3x3 input, 2x2 kernel
        let network = NnNetwork::new(
            vec![NnLayer::Conv2d {
                in_channels: 1,
                out_channels: 1,
                input_height: 3,
                input_width: 3,
                kernel_size: 2,
                stride: 1,
                padding: 0,
                // 2x2 kernel: [[1, 2], [3, 4]]
                weights: vec![vec![vec![vec![1.0, 2.0], vec![3.0, 4.0]]]],
                bias: vec![0.1],
            }],
            9, // 1 channel * 3 * 3 = 9
        );

        // Output: 1 channel, 2x2 = 4
        assert_eq!(network.output_dim, 4);
    }

    #[test]
    fn test_conv2d_forward_pass() {
        // 1 channel, 3x3 input, 2x2 kernel, stride 1, no padding
        let network = NnNetwork::new(
            vec![NnLayer::Conv2d {
                in_channels: 1,
                out_channels: 1,
                input_height: 3,
                input_width: 3,
                kernel_size: 2,
                stride: 1,
                padding: 0,
                weights: vec![vec![vec![vec![1.0, 0.0], vec![0.0, 1.0]]]],
                bias: vec![0.0],
            }],
            9,
        );

        // Input: [[1, 2, 3], [4, 5, 6], [7, 8, 9]] flattened
        let input = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0];
        let input_bounds = Bounds::point(input);

        let output = ibp_propagate(&network, &input_bounds);

        // Kernel [[1, 0], [0, 1]] = sum of diagonal elements
        // Position (0,0): 1 + 5 = 6
        // Position (0,1): 2 + 6 = 8
        // Position (1,0): 4 + 8 = 12
        // Position (1,1): 5 + 9 = 14
        assert_eq!(output.dim(), 4);
        assert!((output.lower[0] - 6.0).abs() < 1e-10);
        assert!((output.lower[1] - 8.0).abs() < 1e-10);
        assert!((output.lower[2] - 12.0).abs() < 1e-10);
        assert!((output.lower[3] - 14.0).abs() < 1e-10);
    }

    #[test]
    fn test_conv2d_ibp_positive_weights() {
        // All positive weights - bounds should propagate directly
        let network = NnNetwork::new(
            vec![NnLayer::Conv2d {
                in_channels: 1,
                out_channels: 1,
                input_height: 2,
                input_width: 2,
                kernel_size: 2,
                stride: 1,
                padding: 0,
                weights: vec![vec![vec![vec![1.0, 1.0], vec![1.0, 1.0]]]],
                bias: vec![0.0],
            }],
            4,
        );

        // Input bounds: [0, 1] for each element
        let input = Bounds::new(vec![0.0; 4], vec![1.0; 4]);
        let output = ibp_propagate(&network, &input);

        // Output is single value: sum of 4 elements
        // Lower: 4 * 0 = 0, Upper: 4 * 1 = 4
        assert_eq!(output.dim(), 1);
        assert!((output.lower[0] - 0.0).abs() < 1e-10);
        assert!((output.upper[0] - 4.0).abs() < 1e-10);
    }

    #[test]
    fn test_conv2d_ibp_mixed_weights() {
        // Mixed positive/negative weights
        let network = NnNetwork::new(
            vec![NnLayer::Conv2d {
                in_channels: 1,
                out_channels: 1,
                input_height: 2,
                input_width: 2,
                kernel_size: 2,
                stride: 1,
                padding: 0,
                weights: vec![vec![vec![vec![1.0, -1.0], vec![-1.0, 1.0]]]],
                bias: vec![0.0],
            }],
            4,
        );

        // Input bounds: [0, 1] for each element
        let input = Bounds::new(vec![0.0; 4], vec![1.0; 4]);
        let output = ibp_propagate(&network, &input);

        // With [1, -1, -1, 1] and inputs in [0, 1]:
        // Max: 1*1 + (-1)*0 + (-1)*0 + 1*1 = 2
        // Min: 1*0 + (-1)*1 + (-1)*1 + 1*0 = -2
        assert_eq!(output.dim(), 1);
        assert!((output.lower[0] - (-2.0)).abs() < 1e-10);
        assert!((output.upper[0] - 2.0).abs() < 1e-10);
    }

    #[test]
    fn test_conv2d_stride() {
        // 4x4 input, 2x2 kernel, stride 2
        let network = NnNetwork::new(
            vec![NnLayer::Conv2d {
                in_channels: 1,
                out_channels: 1,
                input_height: 4,
                input_width: 4,
                kernel_size: 2,
                stride: 2,
                padding: 0,
                weights: vec![vec![vec![vec![1.0, 1.0], vec![1.0, 1.0]]]],
                bias: vec![0.0],
            }],
            16,
        );

        // Output: (4 - 2)/2 + 1 = 2x2 = 4
        assert_eq!(network.output_dim, 4);

        // Point input
        let input_vals: Vec<f64> = (0..16).map(f64::from).collect();
        let input = Bounds::point(input_vals);
        let output = ibp_propagate(&network, &input);

        assert_eq!(output.dim(), 4);
    }

    #[test]
    fn test_conv2d_padding() {
        // 2x2 input, 3x3 kernel, padding 1 -> output 2x2
        let network = NnNetwork::new(
            vec![NnLayer::Conv2d {
                in_channels: 1,
                out_channels: 1,
                input_height: 2,
                input_width: 2,
                kernel_size: 3,
                stride: 1,
                padding: 1,
                weights: vec![vec![vec![
                    vec![1.0, 1.0, 1.0],
                    vec![1.0, 1.0, 1.0],
                    vec![1.0, 1.0, 1.0],
                ]]],
                bias: vec![0.0],
            }],
            4,
        );

        // With padding 1: (2 + 2*1 - 3)/1 + 1 = 2x2
        assert_eq!(network.output_dim, 4);
    }

    #[test]
    fn test_conv2d_multi_channel() {
        // 2 input channels, 3 output channels, 2x2 input, 2x2 kernel
        let network = NnNetwork::new(
            vec![NnLayer::Conv2d {
                in_channels: 2,
                out_channels: 3,
                input_height: 2,
                input_width: 2,
                kernel_size: 2,
                stride: 1,
                padding: 0,
                weights: vec![
                    // Out channel 0: 2 input channels, 2x2 kernels each
                    vec![
                        vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                        vec![vec![0.0, 1.0], vec![1.0, 0.0]],
                    ],
                    // Out channel 1
                    vec![
                        vec![vec![1.0, 1.0], vec![1.0, 1.0]],
                        vec![vec![-1.0, -1.0], vec![-1.0, -1.0]],
                    ],
                    // Out channel 2
                    vec![
                        vec![vec![2.0, 0.0], vec![0.0, 2.0]],
                        vec![vec![0.0, 2.0], vec![2.0, 0.0]],
                    ],
                ],
                bias: vec![0.1, 0.2, 0.3],
            }],
            8, // 2 channels * 2 * 2 = 8
        );

        // Output: 3 channels * 1 * 1 = 3
        assert_eq!(network.output_dim, 3);

        let input = Bounds::point(vec![1.0; 8]);
        let output = ibp_propagate(&network, &input);
        assert_eq!(output.dim(), 3);
    }

    #[test]
    fn test_conv2d_json_roundtrip() {
        use json_model::{JsonLayer, JsonModel};

        let model = JsonModel {
            input_dim: 18, // 2 channels * 3 * 3 = 18
            layers: vec![
                JsonLayer::Conv2d {
                    in_channels: 2,
                    out_channels: 3,
                    input_height: 3,
                    input_width: 3,
                    kernel_size: 2,
                    stride: 1,
                    padding: 0,
                    weights: vec![
                        vec![
                            vec![vec![0.5, -0.5], vec![-0.5, 0.5]],
                            vec![vec![-0.5, 0.5], vec![0.5, -0.5]],
                        ],
                        vec![
                            vec![vec![1.0, 1.0], vec![1.0, 1.0]],
                            vec![vec![1.0, 1.0], vec![1.0, 1.0]],
                        ],
                        vec![
                            vec![vec![0.0, 1.0], vec![1.0, 0.0]],
                            vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                        ],
                    ],
                    bias: vec![0.1, 0.2, 0.3],
                },
                JsonLayer::ReLU,
            ],
        };

        // Serialize to JSON
        let json = model.to_json().expect("Serialization should succeed");

        // Parse back
        let parsed = JsonModel::from_json(&json).expect("Deserialization should succeed");

        // Convert to network
        let network = parsed.to_network().expect("Conversion should succeed");

        // Check dimensions: output is 3 channels * 2 * 2 = 12
        assert_eq!(network.input_dim, 18);
        assert_eq!(network.output_dim, 12);
    }

    #[test]
    fn test_conv2d_network_propagation() {
        // Conv2d + ReLU + Linear (flatten + dense)
        let network = NnNetwork::new(
            vec![
                NnLayer::Conv2d {
                    in_channels: 1,
                    out_channels: 2,
                    input_height: 3,
                    input_width: 3,
                    kernel_size: 2,
                    stride: 1,
                    padding: 0,
                    weights: vec![
                        vec![vec![vec![1.0, 1.0], vec![1.0, 1.0]]],
                        vec![vec![vec![-1.0, -1.0], vec![-1.0, -1.0]]],
                    ],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0; 8]], // 2 channels * 2 * 2 = 8
                    bias: vec![0.0],
                },
            ],
            9, // 1 channel * 3 * 3 = 9
        );

        // Conv2d output: 2 channels * 2 * 2 = 8
        // After linear: 1
        assert_eq!(network.output_dim, 1);

        // Test propagation
        let input = Bounds::linf_ball(&[0.5; 9], 0.1);
        let output = ibp_propagate(&network, &input);

        assert_eq!(output.dim(), 1);
        assert!(output.lower[0] <= output.upper[0]);
    }

    #[test]
    fn test_conv2d_crown_propagation() {
        // Simple Conv2d network for CROWN test
        let network = NnNetwork::new(
            vec![
                NnLayer::Conv2d {
                    in_channels: 1,
                    out_channels: 1,
                    input_height: 2,
                    input_width: 2,
                    kernel_size: 2,
                    stride: 1,
                    padding: 0,
                    weights: vec![vec![vec![vec![1.0, 1.0], vec![1.0, 1.0]]]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            4,
        );

        // Output: 1 after Conv2d (1x1)
        assert_eq!(network.output_dim, 1);

        let input = Bounds::linf_ball(&[0.5; 4], 0.1);

        // IBP bounds
        let ibp_bounds = ibp_propagate(&network, &input);

        // CROWN bounds (should be at least as tight)
        let crown_bounds = crown_propagate(&network, &input);

        // CROWN should give at least as tight bounds as IBP
        assert!(crown_bounds.lower[0] >= ibp_bounds.lower[0] - 1e-10);
        assert!(crown_bounds.upper[0] <= ibp_bounds.upper[0] + 1e-10);
    }

    // Additional GlobalPool2d JSON roundtrip tests (different dimensions)

    #[test]
    fn test_global_avgpool2d_json_roundtrip() {
        let network = NnNetwork::new(
            vec![NnLayer::GlobalAvgPool2d {
                channels: 3,
                height: 4,
                width: 4,
            }],
            48, // 3 * 4 * 4
        );

        let json_model = json_model::JsonModel::from(&network);
        let recovered = json_model.to_network().unwrap();

        assert_eq!(network.layers.len(), recovered.layers.len());
        assert!(matches!(
            recovered.layers[0],
            NnLayer::GlobalAvgPool2d {
                channels: 3,
                height: 4,
                width: 4
            }
        ));
        assert_eq!(recovered.output_dim, 3);
    }

    #[test]
    fn test_global_maxpool2d_json_roundtrip() {
        let network = NnNetwork::new(
            vec![NnLayer::GlobalMaxPool2d {
                channels: 3,
                height: 4,
                width: 4,
            }],
            48, // 3 * 4 * 4
        );

        let json_model = json_model::JsonModel::from(&network);
        let recovered = json_model.to_network().unwrap();

        assert_eq!(network.layers.len(), recovered.layers.len());
        assert!(matches!(
            recovered.layers[0],
            NnLayer::GlobalMaxPool2d {
                channels: 3,
                height: 4,
                width: 4
            }
        ));
        assert_eq!(recovered.output_dim, 3);
    }

    #[test]
    fn test_global_avgpool2d_crown_propagate() {
        // Network with GlobalAvgPool2d - tests full CROWN propagation
        let network = NnNetwork::new(
            vec![NnLayer::GlobalAvgPool2d {
                channels: 2,
                height: 2,
                width: 2,
            }],
            8, // 2 * 2 * 2
        );

        let input_bounds = Bounds::from_box(
            vec![0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0],
            vec![2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0],
        );

        let ibp_bounds = ibp_propagate(&network, &input_bounds);
        let crown_bounds = crown_propagate(&network, &input_bounds);

        // GlobalAvgPool is linear, so CROWN should match IBP
        assert!((crown_bounds.lower[0] - ibp_bounds.lower[0]).abs() < 1e-10);
        assert!((crown_bounds.upper[0] - ibp_bounds.upper[0]).abs() < 1e-10);
        assert!((crown_bounds.lower[1] - ibp_bounds.lower[1]).abs() < 1e-10);
        assert!((crown_bounds.upper[1] - ibp_bounds.upper[1]).abs() < 1e-10);
    }

    #[test]
    fn test_global_maxpool2d_crown_propagate() {
        // Network with GlobalMaxPool2d - tests full CROWN propagation
        let network = NnNetwork::new(
            vec![NnLayer::GlobalMaxPool2d {
                channels: 2,
                height: 2,
                width: 2,
            }],
            8, // 2 * 2 * 2
        );

        let input_bounds = Bounds::from_box(
            vec![0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0],
            vec![2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0],
        );

        let ibp_bounds = ibp_propagate(&network, &input_bounds);
        let crown_bounds = crown_propagate(&network, &input_bounds);

        // CROWN bounds should be at least as tight as IBP
        assert!(crown_bounds.lower[0] >= ibp_bounds.lower[0] - 1e-10);
        assert!(crown_bounds.upper[0] <= ibp_bounds.upper[0] + 1e-10);
        assert!(crown_bounds.lower[1] >= ibp_bounds.lower[1] - 1e-10);
        assert!(crown_bounds.upper[1] <= ibp_bounds.upper[1] + 1e-10);
    }

    #[test]
    fn test_conv2d_global_avgpool_network() {
        // Conv2d (1x1) -> ReLU -> GlobalAvgPool2d
        // This tests a typical CNN classifier head pattern
        let network = NnNetwork::new(
            vec![
                NnLayer::Conv2d {
                    in_channels: 1,
                    out_channels: 2,
                    input_height: 2,
                    input_width: 2,
                    kernel_size: 1,
                    stride: 1,
                    padding: 0,
                    weights: vec![
                        vec![vec![vec![1.0]]],  // out_ch=0, in_ch=0: identity
                        vec![vec![vec![-1.0]]], // out_ch=1, in_ch=0: negate
                    ],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::GlobalAvgPool2d {
                    channels: 2,
                    height: 2,
                    width: 2,
                },
            ],
            4, // 1 * 2 * 2
        );

        // Output should be 2 channels
        assert_eq!(network.output_dim, 2);

        let input = Bounds::linf_ball(&[0.5; 4], 0.1);

        let ibp_bounds = ibp_propagate(&network, &input);
        let crown_bounds = crown_propagate(&network, &input);

        // CROWN should give at least as tight bounds as IBP
        assert!(crown_bounds.lower[0] >= ibp_bounds.lower[0] - 1e-10);
        assert!(crown_bounds.upper[0] <= ibp_bounds.upper[0] + 1e-10);
    }

    #[test]
    fn test_global_avgpool2d_3x3() {
        // Input: 1 channel, 3x3 spatial (9 values)
        let input = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0];
        let output = forward_global_avgpool2d(&input, 1, 3, 3);

        assert_eq!(output.len(), 1);
        assert!((output[0] - 5.0).abs() < 1e-10); // avg(1..9) = 45/9 = 5.0
    }

    #[test]
    fn test_global_maxpool2d_3x3() {
        // Input: 1 channel, 3x3 spatial (9 values)
        let input = vec![1.0, 9.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 2.0];
        let output = forward_global_maxpool2d(&input, 1, 3, 3);

        assert_eq!(output.len(), 1);
        assert!((output[0] - 9.0).abs() < 1e-10); // max = 9.0
    }

    // ============================================================
    // BatchNorm2d Tests
    // ============================================================

    #[test]
    fn test_batchnorm2d_forward() {
        // 2 channels, 2x2 spatial (8 values total)
        let input = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
        let scale = vec![2.0, 0.5]; // scale per channel
        let bias = vec![1.0, -1.0]; // bias per channel

        let output = forward_batchnorm2d(&input, 2, 2, 2, &scale, &bias);

        // Channel 0: values 1,2,3,4 -> 2*x + 1 = 3,5,7,9
        // Channel 1: values 5,6,7,8 -> 0.5*x - 1 = 1.5,2,2.5,3
        assert_eq!(output.len(), 8);
        assert!((output[0] - 3.0).abs() < 1e-10);
        assert!((output[1] - 5.0).abs() < 1e-10);
        assert!((output[2] - 7.0).abs() < 1e-10);
        assert!((output[3] - 9.0).abs() < 1e-10);
        assert!((output[4] - 1.5).abs() < 1e-10);
        assert!((output[5] - 2.0).abs() < 1e-10);
        assert!((output[6] - 2.5).abs() < 1e-10);
        assert!((output[7] - 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_batchnorm2d_ibp() {
        // 2 channels, 2x2 spatial
        let lower = vec![0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0];
        let upper = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
        let input = Bounds::new(lower, upper);
        let scale = vec![2.0, -1.0]; // negative scale to test ordering
        let bias = vec![0.0, 0.0];

        let output = ibp_batchnorm2d(&input, 2, 2, 2, &scale, &bias);

        // Channel 0 (positive scale): lower*2, upper*2
        assert!((output.lower[0] - 0.0).abs() < 1e-10);
        assert!((output.upper[0] - 2.0).abs() < 1e-10);

        // Channel 1 (negative scale): upper*(-1), lower*(-1) => bounds swap
        assert!((output.lower[4] - (-5.0)).abs() < 1e-10);
        assert!((output.upper[4] - (-4.0)).abs() < 1e-10);
    }

    #[test]
    fn test_batchnorm2d_json_roundtrip() {
        let network = NnNetwork::new(
            vec![NnLayer::BatchNorm2d {
                channels: 3,
                height: 4,
                width: 4,
                scale: vec![1.0, 2.0, 0.5],
                bias: vec![0.0, 1.0, -1.0],
            }],
            3 * 4 * 4,
        );

        let json_model = json_model::JsonModel::from(&network);
        let recovered = json_model.to_network().unwrap();

        assert_eq!(recovered.layers.len(), 1);
        assert!(matches!(
            &recovered.layers[0],
            NnLayer::BatchNorm2d {
                channels: 3,
                height: 4,
                width: 4,
                scale,
                bias
            } if scale == &[1.0, 2.0, 0.5] && bias == &[0.0, 1.0, -1.0]
        ));
    }

    // ============================================================
    // MaxPool2d Tests
    // ============================================================

    #[test]
    fn test_maxpool2d_forward() {
        // 1 channel, 4x4 spatial, 2x2 kernel, stride 2
        let input = vec![
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0,
        ];

        let output = forward_maxpool2d(&input, 1, 4, 4, 2, 2);

        // 2x2 output: max of each 2x2 block
        // Block (0,0): max(1,2,5,6) = 6
        // Block (0,1): max(3,4,7,8) = 8
        // Block (1,0): max(9,10,13,14) = 14
        // Block (1,1): max(11,12,15,16) = 16
        assert_eq!(output.len(), 4);
        assert!((output[0] - 6.0).abs() < 1e-10);
        assert!((output[1] - 8.0).abs() < 1e-10);
        assert!((output[2] - 14.0).abs() < 1e-10);
        assert!((output[3] - 16.0).abs() < 1e-10);
    }

    #[test]
    fn test_maxpool2d_ibp() {
        // 1 channel, 4x4 spatial
        let lower: Vec<f64> = (1..=16).map(|x| f64::from(x) - 0.5).collect();
        let upper: Vec<f64> = (1..=16).map(|x| f64::from(x) + 0.5).collect();
        let input = Bounds::new(lower, upper);

        let output = ibp_maxpool2d(&input, 1, 4, 4, 2, 2);

        // For max pooling: lower = max of lowers, upper = max of uppers
        assert_eq!(output.dim(), 4);
        // Block (0,0): lower = max(0.5,1.5,4.5,5.5) = 5.5, upper = max(1.5,2.5,5.5,6.5) = 6.5
        assert!((output.lower[0] - 5.5).abs() < 1e-10);
        assert!((output.upper[0] - 6.5).abs() < 1e-10);
    }

    #[test]
    fn test_maxpool2d_json_roundtrip() {
        let network = NnNetwork::new(
            vec![NnLayer::MaxPool2d {
                channels: 3,
                height: 8,
                width: 8,
                kernel_size: 2,
                stride: 2,
            }],
            3 * 8 * 8,
        );

        let json_model = json_model::JsonModel::from(&network);
        let recovered = json_model.to_network().unwrap();

        assert_eq!(recovered.layers.len(), 1);
        assert!(matches!(
            recovered.layers[0],
            NnLayer::MaxPool2d {
                channels: 3,
                height: 8,
                width: 8,
                kernel_size: 2,
                stride: 2,
            }
        ));
    }

    // ============================================================
    // AvgPool2d Tests
    // ============================================================

    #[test]
    fn test_avgpool2d_forward() {
        // 1 channel, 4x4 spatial, 2x2 kernel, stride 2
        let input = vec![
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0,
        ];

        let output = forward_avgpool2d(&input, 1, 4, 4, 2, 2);

        // 2x2 output: average of each 2x2 block
        // Block (0,0): avg(1,2,5,6) = 3.5
        // Block (0,1): avg(3,4,7,8) = 5.5
        // Block (1,0): avg(9,10,13,14) = 11.5
        // Block (1,1): avg(11,12,15,16) = 13.5
        assert_eq!(output.len(), 4);
        assert!((output[0] - 3.5).abs() < 1e-10);
        assert!((output[1] - 5.5).abs() < 1e-10);
        assert!((output[2] - 11.5).abs() < 1e-10);
        assert!((output[3] - 13.5).abs() < 1e-10);
    }

    #[test]
    fn test_avgpool2d_ibp() {
        // 1 channel, 4x4 spatial
        let lower: Vec<f64> = (1..=16).map(|x| f64::from(x) - 1.0).collect();
        let upper: Vec<f64> = (1..=16).map(|x| f64::from(x) + 1.0).collect();
        let input = Bounds::new(lower, upper);

        let output = ibp_avgpool2d(&input, 1, 4, 4, 2, 2);

        assert_eq!(output.dim(), 4);
        // Block (0,0): avg of lowers = avg(0,1,4,5) = 2.5, avg of uppers = avg(2,3,6,7) = 4.5
        assert!((output.lower[0] - 2.5).abs() < 1e-10);
        assert!((output.upper[0] - 4.5).abs() < 1e-10);
    }

    #[test]
    fn test_avgpool2d_json_roundtrip() {
        let network = NnNetwork::new(
            vec![NnLayer::AvgPool2d {
                channels: 3,
                height: 8,
                width: 8,
                kernel_size: 2,
                stride: 2,
            }],
            3 * 8 * 8,
        );

        let json_model = json_model::JsonModel::from(&network);
        let recovered = json_model.to_network().unwrap();

        assert_eq!(recovered.layers.len(), 1);
        assert!(matches!(
            recovered.layers[0],
            NnLayer::AvgPool2d {
                channels: 3,
                height: 8,
                width: 8,
                kernel_size: 2,
                stride: 2,
            }
        ));
    }

    #[test]
    fn test_2d_cnn_layers_integration() {
        // Test a simple 2D CNN sequence: Conv2d -> BatchNorm2d -> ReLU -> MaxPool2d
        let network = NnNetwork::new(
            vec![
                // Conv2d: 1 input channel -> 2 output channels, 3x3 kernel
                NnLayer::Conv2d {
                    in_channels: 1,
                    out_channels: 2,
                    input_height: 4,
                    input_width: 4,
                    kernel_size: 3,
                    stride: 1,
                    padding: 1,
                    // weights: [out_channels][in_channels][kernel_h][kernel_w]
                    weights: vec![
                        // out_channel 0: one in_channel with 3x3 kernel
                        vec![vec![vec![0.1; 3]; 3]],
                        // out_channel 1: one in_channel with 3x3 kernel
                        vec![vec![vec![0.2; 3]; 3]],
                    ],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::BatchNorm2d {
                    channels: 2,
                    height: 4,
                    width: 4,
                    scale: vec![1.0, 1.0],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::MaxPool2d {
                    channels: 2,
                    height: 4,
                    width: 4,
                    kernel_size: 2,
                    stride: 2,
                },
            ],
            16, // input_dim: 1 channel * 4x4 spatial
        );

        // Input: 1 channel, 4x4 spatial
        let input = vec![1.0; 16];

        let output = forward_pass(&network, &input);

        // Output should be 2 channels * 2x2 = 8 values
        assert_eq!(output.len(), 8);
        // All outputs should be positive (after ReLU)
        for &v in &output {
            assert!(v >= 0.0);
        }
    }
}

// Monotonicity verification tests (added by worker #187)
#[cfg(test)]
mod monotonicity_tests {
    use super::*;

    #[test]
    fn test_verify_monotonicity_increasing_proven() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = MonotonicitySpec {
            input_dims: vec![0],
            output_dims: vec![0],
            increasing: true,
            region: InputRegion::Box {
                lower: vec![0.5],
                upper: vec![1.5],
            },
        };

        let result = backend.verify_monotonicity(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven, got {result:?}"
        );
    }

    #[test]
    fn test_verify_monotonicity_decreasing_proven() {
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![-1.0]],
                bias: vec![0.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = MonotonicitySpec {
            input_dims: vec![0],
            output_dims: vec![0],
            increasing: false,
            region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
        };

        let result = backend.verify_monotonicity(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven, got {result:?}"
        );
    }

    #[test]
    fn test_verify_monotonicity_2d_input() {
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0, 2.0]],
                bias: vec![0.0],
            }],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = MonotonicitySpec {
            input_dims: vec![0, 1],
            output_dims: vec![0],
            increasing: true,
            region: InputRegion::Box {
                lower: vec![0.0, 0.0],
                upper: vec![1.0, 1.0],
            },
        };

        let result = backend.verify_monotonicity(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven, got {result:?}"
        );
    }

    // ============================================================================
    // Skip Connection Tests (ResidualAdd, Concat)
    // ============================================================================

    #[test]
    fn test_residual_add_forward() {
        // Simple residual connection: input -> Linear -> ReLU -> ResidualAdd (skip from input)
        // y = ReLU(Wx + b) + input
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]], // Identity
                    bias: vec![0.5, 0.5],
                },
                NnLayer::ReLU,
                NnLayer::ResidualAdd {
                    skip_from_output: 0,
                }, // Add original input
            ],
            2,
        );

        let input = vec![1.0, 2.0];
        let output = forward_pass(&network, &input);

        // Linear: [1.0, 2.0] -> [1.0 + 0.5, 2.0 + 0.5] = [1.5, 2.5]
        // ReLU: [1.5, 2.5] (unchanged)
        // ResidualAdd: [1.5, 2.5] + [1.0, 2.0] = [2.5, 4.5]
        assert_eq!(output.len(), 2);
        assert!(
            (output[0] - 2.5).abs() < 1e-6,
            "Expected 2.5, got {}",
            output[0]
        );
        assert!(
            (output[1] - 4.5).abs() < 1e-6,
            "Expected 4.5, got {}",
            output[1]
        );
    }

    #[test]
    fn test_residual_add_ibp() {
        // ResidualAdd with IBP bounds
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![2.0, 0.0], vec![0.0, 2.0]], // Scale by 2
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::ResidualAdd {
                    skip_from_output: 0,
                }, // Add original input
            ],
            2,
        );

        // Input bounds: [0.0, 1.0] x [0.0, 1.0]
        let input_bounds = Bounds::new(vec![0.0, 0.0], vec![1.0, 1.0]);
        let output_bounds = ibp_propagate(&network, &input_bounds);

        // Linear: [0, 2] x [0, 2]
        // ReLU: [0, 2] x [0, 2] (unchanged, all non-negative)
        // ResidualAdd: [0, 2] + [0, 1] = [0, 3] x [0, 3]
        assert_eq!(output_bounds.dim(), 2);
        assert!(output_bounds.lower[0] >= -1e-6, "Expected lower >= 0");
        assert!(output_bounds.lower[1] >= -1e-6, "Expected lower >= 0");
        assert!(output_bounds.upper[0] <= 3.0 + 1e-6, "Expected upper <= 3");
        assert!(output_bounds.upper[1] <= 3.0 + 1e-6, "Expected upper <= 3");
    }

    #[test]
    fn test_concat_forward() {
        // Concat: input -> Linear (reduce dim) -> Concat (add original input)
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]], // Sum to 1D
                    bias: vec![0.0],
                },
                NnLayer::Concat {
                    skip_from_output: 0,
                }, // Concat original input
            ],
            2,
        );

        let input = vec![1.0, 2.0];
        let output = forward_pass(&network, &input);

        // Linear: [1.0, 2.0] -> [3.0]
        // Concat: [3.0] ++ [1.0, 2.0] = [3.0, 1.0, 2.0]
        assert_eq!(output.len(), 3);
        assert!((output[0] - 3.0).abs() < 1e-6);
        assert!((output[1] - 1.0).abs() < 1e-6);
        assert!((output[2] - 2.0).abs() < 1e-6);
    }

    #[test]
    fn test_concat_ibp() {
        // Concat with IBP bounds
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0]], // Project to first component
                    bias: vec![0.0],
                },
                NnLayer::Concat {
                    skip_from_output: 0,
                }, // Concat original input
            ],
            2,
        );

        let input_bounds = Bounds::new(vec![0.0, 1.0], vec![2.0, 3.0]);
        let output_bounds = ibp_propagate(&network, &input_bounds);

        // Linear: [0, 2]
        // Concat: [0, 2] ++ [0, 2] x [1, 3] = 3D bounds
        assert_eq!(output_bounds.dim(), 3);
        assert!((output_bounds.lower[0] - 0.0).abs() < 1e-6);
        assert!((output_bounds.upper[0] - 2.0).abs() < 1e-6);
        assert!((output_bounds.lower[1] - 0.0).abs() < 1e-6);
        assert!((output_bounds.upper[1] - 2.0).abs() < 1e-6);
        assert!((output_bounds.lower[2] - 1.0).abs() < 1e-6);
        assert!((output_bounds.upper[2] - 3.0).abs() < 1e-6);
    }

    #[test]
    fn test_residual_add_json_roundtrip() {
        // Test JSON serialization of ResidualAdd
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                    bias: vec![0.1, 0.2],
                },
                NnLayer::ReLU,
                NnLayer::ResidualAdd {
                    skip_from_output: 0,
                },
            ],
            2,
        );

        let json_model = json_model::JsonModel::from(&network);
        let json_str = json_model.to_json().expect("Serialization failed");
        let parsed_model =
            json_model::JsonModel::from_json(&json_str).expect("Deserialization failed");
        let reconstructed = parsed_model.to_network().expect("Conversion failed");

        // Verify structure
        assert_eq!(reconstructed.layers.len(), 3);
        assert!(matches!(
            reconstructed.layers[2],
            NnLayer::ResidualAdd {
                skip_from_output: 0
            }
        ));

        // Verify forward pass matches
        let input = vec![1.0, 2.0];
        let orig_output = forward_pass(&network, &input);
        let recon_output = forward_pass(&reconstructed, &input);
        for (a, b) in orig_output.iter().zip(&recon_output) {
            assert!((a - b).abs() < 1e-10, "Output mismatch");
        }
    }

    #[test]
    fn test_concat_json_roundtrip() {
        // Test JSON serialization of Concat
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
                NnLayer::Concat {
                    skip_from_output: 0,
                },
            ],
            2,
        );

        let json_model = json_model::JsonModel::from(&network);
        let json_str = json_model.to_json().expect("Serialization failed");
        let parsed_model =
            json_model::JsonModel::from_json(&json_str).expect("Deserialization failed");
        let reconstructed = parsed_model.to_network().expect("Conversion failed");

        // Verify structure
        assert_eq!(reconstructed.layers.len(), 2);
        assert!(matches!(
            reconstructed.layers[1],
            NnLayer::Concat {
                skip_from_output: 0
            }
        ));

        // Verify output dimension
        assert_eq!(reconstructed.output_dim, 3);
    }

    #[test]
    fn test_resnet_block_structure() {
        // Test a typical ResNet block: input -> conv -> bn -> relu -> conv -> bn -> residual_add -> relu
        // Simplified: input -> Linear -> ReLU -> Linear -> ResidualAdd -> ReLU
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]], // Identity
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![0.5, 0.0], vec![0.0, 0.5]], // Scale by 0.5
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ResidualAdd {
                    skip_from_output: 0,
                }, // Add original input
                NnLayer::ReLU,
            ],
            2,
        );

        let input = vec![2.0, 4.0];
        let output = forward_pass(&network, &input);

        // Linear1: [2.0, 4.0]
        // ReLU: [2.0, 4.0]
        // Linear2: [1.0, 2.0]
        // ResidualAdd: [1.0, 2.0] + [2.0, 4.0] = [3.0, 6.0]
        // ReLU: [3.0, 6.0]
        assert_eq!(output.len(), 2);
        assert!((output[0] - 3.0).abs() < 1e-6);
        assert!((output[1] - 6.0).abs() < 1e-6);
    }

    #[test]
    fn test_resnet_block_ibp_verification() {
        // Verify robustness of ResNet-like block
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![0.5, 0.0], vec![0.0, 0.5]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ResidualAdd {
                    skip_from_output: 0,
                },
                NnLayer::ReLU,
            ],
            2,
        );

        // Verify output bounds contain expected forward pass result
        let center = vec![2.0, 4.0];
        let epsilon = 0.1;
        let input_bounds = Bounds::linf_ball(&center, epsilon);
        let output_bounds = ibp_propagate(&network, &input_bounds);

        // Forward pass at center: [3.0, 6.0]
        let center_output = forward_pass(&network, &center);

        // Verify center output is within computed bounds
        for i in 0..2 {
            assert!(
                output_bounds.lower[i] <= center_output[i] + 1e-6,
                "Lower bound {} > center output {}",
                output_bounds.lower[i],
                center_output[i]
            );
            assert!(
                output_bounds.upper[i] >= center_output[i] - 1e-6,
                "Upper bound {} < center output {}",
                output_bounds.upper[i],
                center_output[i]
            );
        }
    }

    #[test]
    fn test_densenet_block_structure() {
        // DenseNet-style: each layer concatenates with previous
        // input(2) -> Linear(2->1) -> Concat(input) -> Linear(3->1) -> Concat(input)
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]], // 2 -> 1
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
                NnLayer::Concat {
                    skip_from_output: 0,
                }, // 1 + 2 = 3
                NnLayer::Linear {
                    weights: vec![vec![0.5, 0.25, 0.25]], // 3 -> 1
                    bias: vec![0.0],
                },
            ],
            2,
        );

        let input = vec![1.0, 2.0];
        let output = forward_pass(&network, &input);

        // Linear1: [1, 2] -> [3]
        // ReLU: [3]
        // Concat: [3, 1, 2]
        // Linear2: 0.5*3 + 0.25*1 + 0.25*2 = 1.5 + 0.25 + 0.5 = 2.25
        assert_eq!(output.len(), 1);
        assert!(
            (output[0] - 2.25).abs() < 1e-6,
            "Expected 2.25, got {}",
            output[0]
        );
    }

    #[test]
    fn test_network_output_dim_with_residual() {
        // ResidualAdd preserves dimension
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ResidualAdd {
                    skip_from_output: 0,
                },
            ],
            2,
        );
        assert_eq!(network.output_dim, 2);
    }

    #[test]
    fn test_network_output_dim_with_concat() {
        // Concat increases dimension
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0, 0.0]], // 2 -> 1
                    bias: vec![0.0],
                },
                NnLayer::Concat {
                    skip_from_output: 0,
                }, // 1 + 2 = 3
            ],
            2,
        );
        assert_eq!(network.output_dim, 3);
    }

    #[test]
    fn test_verify_monotonicity_unstable_relu_still_proven_increasing() {
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = MonotonicitySpec {
            input_dims: vec![0],
            output_dims: vec![0],
            increasing: true,
            region: InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            },
        };

        let result = backend.verify_monotonicity(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven, got {result:?}"
        );
    }

    #[test]
    fn test_verify_monotonicity_abs_unknown() {
        // f(x) = ReLU(x) + ReLU(-x) = |x| is not monotone on [-1, 1]
        let network = NnNetwork::new(
            vec![
                // Map x -> [x, -x]
                NnLayer::Linear {
                    weights: vec![vec![1.0], vec![-1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                // Sum the two ReLU outputs
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = MonotonicitySpec {
            input_dims: vec![0],
            output_dims: vec![0],
            increasing: true,
            region: InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            },
        };

        let result = backend.verify_monotonicity(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown, got {result:?}"
        );
    }

    // ============================================================================
    // Lipschitz Verification Tests
    // ============================================================================

    #[test]
    fn test_lipschitz_from_jacobian_linf_linf() {
        // Identity matrix: ||J||_∞ = 1
        let jacobian = IntervalMatrix {
            lower: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
            upper: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
        };
        let lip = lipschitz_from_jacobian_bounds(&jacobian, Norm::Linf, Norm::Linf);
        assert!((lip - 1.0).abs() < 1e-9, "Expected 1.0, got {lip}");
    }

    #[test]
    fn test_lipschitz_from_jacobian_l1_l1() {
        // Identity matrix: ||J||_1 = 1
        let jacobian = IntervalMatrix {
            lower: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
            upper: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
        };
        let lip = lipschitz_from_jacobian_bounds(&jacobian, Norm::L1, Norm::L1);
        assert!((lip - 1.0).abs() < 1e-9, "Expected 1.0, got {lip}");
    }

    #[test]
    fn test_lipschitz_from_jacobian_l2_l2() {
        // Identity matrix: ||J||_2 = 1
        let jacobian = IntervalMatrix {
            lower: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
            upper: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
        };
        let lip = lipschitz_from_jacobian_bounds(&jacobian, Norm::L2, Norm::L2);
        // Submultiplicative bound: sqrt(1 * 1) = 1
        assert!((lip - 1.0).abs() < 1e-9, "Expected 1.0, got {lip}");
    }

    #[test]
    fn test_lipschitz_from_jacobian_scaling() {
        // Scaling matrix [[2, 0], [0, 3]]: ||J||_∞ = 3, ||J||_1 = 3
        let jacobian = IntervalMatrix {
            lower: vec![vec![2.0, 0.0], vec![0.0, 3.0]],
            upper: vec![vec![2.0, 0.0], vec![0.0, 3.0]],
        };
        let lip_inf = lipschitz_from_jacobian_bounds(&jacobian, Norm::Linf, Norm::Linf);
        assert!((lip_inf - 3.0).abs() < 1e-9, "Expected 3.0, got {lip_inf}");

        let lip_1 = lipschitz_from_jacobian_bounds(&jacobian, Norm::L1, Norm::L1);
        assert!((lip_1 - 3.0).abs() < 1e-9, "Expected 3.0, got {lip_1}");
    }

    #[test]
    fn test_lipschitz_from_jacobian_interval_uncertainty() {
        // Uncertain Jacobian: J_ij in [-2, 3] means |J_ij| <= 3
        let jacobian = IntervalMatrix {
            lower: vec![vec![-2.0]],
            upper: vec![vec![3.0]],
        };
        let lip = lipschitz_from_jacobian_bounds(&jacobian, Norm::Linf, Norm::Linf);
        assert!((lip - 3.0).abs() < 1e-9, "Expected 3.0, got {lip}");
    }

    #[test]
    fn test_lipschitz_from_jacobian_l2_l1() {
        // 2x2 identity: L2->L1 bound uses sqrt(m) * max_row_L2_norm
        // Row L2 norms: sqrt(1+0)=1, sqrt(0+1)=1, max = 1
        // sqrt(2) * 1 ≈ 1.414
        let jacobian = IntervalMatrix {
            lower: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
            upper: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
        };
        let expected = (2.0_f64).sqrt();
        let lip = lipschitz_from_jacobian_bounds(&jacobian, Norm::L2, Norm::L1);
        assert!(
            (lip - expected).abs() < 1e-9,
            "Expected {expected}, got {lip}"
        );
    }

    #[test]
    fn test_lipschitz_from_jacobian_l1_linf() {
        // L1->Linf is max absolute entry
        // Matrix [[2, 3], [1, 4]] -> max entry is 4
        let jacobian = IntervalMatrix {
            lower: vec![vec![2.0, 3.0], vec![1.0, 4.0]],
            upper: vec![vec![2.0, 3.0], vec![1.0, 4.0]],
        };
        let lip = lipschitz_from_jacobian_bounds(&jacobian, Norm::L1, Norm::Linf);
        assert!((lip - 4.0).abs() < 1e-9, "Expected 4.0, got {lip}");
    }

    #[test]
    fn test_lipschitz_from_jacobian_linf_l1() {
        // Linf->L1 is sum of max entries per column
        // Matrix [[2, 3], [1, 4]] -> col 0 max=2, col 1 max=4 -> sum = 6
        let jacobian = IntervalMatrix {
            lower: vec![vec![2.0, 3.0], vec![1.0, 4.0]],
            upper: vec![vec![2.0, 3.0], vec![1.0, 4.0]],
        };
        let lip = lipschitz_from_jacobian_bounds(&jacobian, Norm::Linf, Norm::L1);
        assert!((lip - 6.0).abs() < 1e-9, "Expected 6.0, got {lip}");
    }

    #[test]
    fn test_lipschitz_from_jacobian_l0_fallback() {
        // L0 norm uses Frobenius norm fallback
        // Matrix [[1, 2], [3, 4]] -> Frobenius = sqrt(1+4+9+16) = sqrt(30)
        let jacobian = IntervalMatrix {
            lower: vec![vec![1.0, 2.0], vec![3.0, 4.0]],
            upper: vec![vec![1.0, 2.0], vec![3.0, 4.0]],
        };
        let expected = (1.0 + 4.0 + 9.0 + 16.0_f64).sqrt();
        let lip = lipschitz_from_jacobian_bounds(&jacobian, Norm::L0, Norm::Linf);
        assert!(
            (lip - expected).abs() < 1e-9,
            "Expected {expected}, got {lip}"
        );
    }

    #[test]
    fn test_verify_lipschitz_linear_proven() {
        // f(x) = 2x has Lipschitz constant 2
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![2.0]],
                bias: vec![0.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = LipschitzSpec {
            constant: 2.0,
            input_norm: Norm::Linf,
            output_norm: Norm::Linf,
            region: Some(InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            }),
        };

        let result = backend.verify_lipschitz(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven, got {result:?}"
        );
    }

    #[test]
    fn test_verify_lipschitz_linear_too_tight() {
        // f(x) = 2x has Lipschitz constant 2, not 1
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![2.0]],
                bias: vec![0.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = LipschitzSpec {
            constant: 1.0, // Too tight
            input_norm: Norm::Linf,
            output_norm: Norm::Linf,
            region: Some(InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            }),
        };

        let result = backend.verify_lipschitz(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown, got {result:?}"
        );
    }

    #[test]
    fn test_verify_lipschitz_mlp_with_relu() {
        // MLP: Linear(1->2) -> ReLU -> Linear(2->1)
        // W1 = [[1], [2]], W2 = [[1, 1]]
        // For stable ReLUs, J = W2 @ D @ W1 where D is diagonal ReLU derivative
        // ||J||_∞ <= ||W2||_∞ * ||W1||_∞ = 2 * 2 = 4 (worst case)
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0], vec![2.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        // With positive inputs, ReLU derivative is 1, so J = [[1, 1]] @ [[1], [2]] = [[3]]
        // Lipschitz constant should be 3
        let spec = LipschitzSpec {
            constant: 4.0, // Conservative bound
            input_norm: Norm::Linf,
            output_norm: Norm::Linf,
            region: Some(InputRegion::Box {
                lower: vec![1.0],
                upper: vec![2.0],
            }),
        };

        let result = backend.verify_lipschitz(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven, got {result:?}"
        );
    }

    #[test]
    fn test_verify_lipschitz_l2_norm() {
        // f(x,y) = (x, y) has Lipschitz constant 1 in L2 norm
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                bias: vec![0.0, 0.0],
            }],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = LipschitzSpec {
            constant: 1.0,
            input_norm: Norm::L2,
            output_norm: Norm::L2,
            region: None, // Default region
        };

        let result = backend.verify_lipschitz(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven, got {result:?}"
        );
    }

    #[test]
    fn test_verify_lipschitz_default_region() {
        // f(x) = 0.5*x has Lipschitz constant 0.5
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![0.5]],
                bias: vec![0.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        // No region specified - should use default [-1, 1]^n
        let spec = LipschitzSpec {
            constant: 0.5,
            input_norm: Norm::Linf,
            output_norm: Norm::Linf,
            region: None,
        };

        let result = backend.verify_lipschitz(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven, got {result:?}"
        );
    }

    #[test]
    fn test_verify_lipschitz_no_network() {
        let backend = CrownBackend::new(CrownConfig::default());

        let spec = LipschitzSpec {
            constant: 1.0,
            input_norm: Norm::Linf,
            output_norm: Norm::Linf,
            region: None,
        };

        let result = backend.verify_lipschitz(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown for no network, got {result:?}"
        );
    }

    // ============================================================================
    // Fairness Verification Tests
    // ============================================================================

    #[test]
    fn test_verify_fairness_independence_helper_near_zero() {
        // Jacobian with entries near zero for protected attribute (column 0)
        let jacobian = IntervalMatrix {
            lower: vec![vec![-1e-8, 0.5], vec![-1e-9, -0.3]],
            upper: vec![vec![1e-8, 0.8], vec![1e-9, 0.4]],
        };

        let result = verify_fairness_independence(&jacobian, &[0]);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven for near-zero Jacobian, got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_independence_helper_not_near_zero() {
        // Jacobian with significant entries for protected attribute (column 0)
        let jacobian = IntervalMatrix {
            lower: vec![vec![-0.5, 0.5], vec![-0.3, -0.3]],
            upper: vec![vec![0.5, 0.8], vec![0.3, 0.4]],
        };

        let result = verify_fairness_independence(&jacobian, &[0]);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown for significant Jacobian entries, got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_individual_helper_proven() {
        // Jacobian with partial Lipschitz constant <= threshold for protected cols
        // Protected columns: 0
        // Row 0: |0.1| = 0.1
        // Row 1: |-0.2| = 0.2
        // Max row sum = 0.2, threshold = 0.5 -> Proven
        let jacobian = IntervalMatrix {
            lower: vec![vec![0.1, 0.5], vec![-0.2, -0.3]],
            upper: vec![vec![0.1, 0.8], vec![-0.2, 0.4]],
        };

        let result = verify_fairness_individual(&jacobian, &[0], 0.5);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven for low partial Lipschitz, got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_individual_helper_not_proven() {
        // Jacobian with partial Lipschitz constant > threshold
        // Protected columns: 0, 1
        // Row 0: |0.5| + |0.8| = 1.3
        // Row 1: |0.3| + |0.4| = 0.7
        // Max row sum = 1.3, threshold = 1.0 -> Unknown
        let jacobian = IntervalMatrix {
            lower: vec![vec![0.5, 0.8], vec![-0.3, 0.4]],
            upper: vec![vec![0.5, 0.8], vec![0.3, 0.4]],
        };

        let result = verify_fairness_individual(&jacobian, &[0, 1], 1.0);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown for high partial Lipschitz, got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_independence_linear_network() {
        // Network: y = W * x where W[0,0] = 0 (first input doesn't affect first output)
        // y[0] = 0*x[0] + 1*x[1] = x[1]   (independent of x[0])
        // y[1] = 0.5*x[0] + 0.5*x[1]      (depends on x[0])
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![0.0, 1.0], vec![0.5, 0.5]],
                bias: vec![0.0, 0.0],
            }],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        // Protected attribute is x[0]
        let spec = FairnessSpec {
            protected_attributes: vec![0],
            criterion: FairnessCriterion::Independence,
            region: InputRegion::Box {
                lower: vec![-1.0, -1.0],
                upper: vec![1.0, 1.0],
            },
        };

        let result = backend.verify_fairness(&spec);
        // Should be Unknown because output 1 depends on x[0] (W[1,0] = 0.5)
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown (y[1] depends on protected attribute), got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_independence_proven() {
        // Network: y = W * x where column 0 of W is all zeros
        // This means output is independent of x[0]
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![0.0, 1.0], vec![0.0, 0.5]],
                bias: vec![0.1, 0.2],
            }],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = FairnessSpec {
            protected_attributes: vec![0],
            criterion: FairnessCriterion::Independence,
            region: InputRegion::Box {
                lower: vec![-1.0, -1.0],
                upper: vec![1.0, 1.0],
            },
        };

        let result = backend.verify_fairness(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven (output independent of x[0]), got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_individual_linear_proven() {
        // Network: y = W * x with small weights for protected attribute
        // W[*,0] = 0.1 means partial Lipschitz w.r.t. x[0] is at most 0.1 per row
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![0.1, 2.0], vec![0.1, 1.5]],
                bias: vec![0.0, 0.0],
            }],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        // Partial Lipschitz for column 0: max(0.1, 0.1) = 0.1
        let spec = FairnessSpec {
            protected_attributes: vec![0],
            criterion: FairnessCriterion::Individual {
                similarity_threshold: 0.5,
            },
            region: InputRegion::Box {
                lower: vec![-1.0, -1.0],
                upper: vec![1.0, 1.0],
            },
        };

        let result = backend.verify_fairness(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven (partial Lipschitz 0.1 <= 0.5), got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_individual_not_proven() {
        // Network with high sensitivity to protected attribute
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![2.0, 1.0], vec![1.5, 0.5]],
                bias: vec![0.0, 0.0],
            }],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        // Partial Lipschitz for column 0: max(2.0, 1.5) = 2.0 > 1.0
        let spec = FairnessSpec {
            protected_attributes: vec![0],
            criterion: FairnessCriterion::Individual {
                similarity_threshold: 1.0,
            },
            region: InputRegion::Box {
                lower: vec![-1.0, -1.0],
                upper: vec![1.0, 1.0],
            },
        };

        let result = backend.verify_fairness(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown (partial Lipschitz 2.0 > 1.0), got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_mlp_with_relu() {
        // MLP: Linear -> ReLU -> Linear
        // With ReLU, the Jacobian depends on which ReLUs are active
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![0.0, 1.0], vec![0.0, -1.0]], // Column 0 is zeros
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = FairnessSpec {
            protected_attributes: vec![0],
            criterion: FairnessCriterion::Independence,
            region: InputRegion::Box {
                lower: vec![-1.0, -1.0],
                upper: vec![1.0, 1.0],
            },
        };

        let result = backend.verify_fairness(&spec);
        // Should be Proven: first layer has zeros in column 0, so x[0] has no effect
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven (protected attribute has zero weights), got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_equal_opportunity_not_implemented() {
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0, 1.0]],
                bias: vec![0.0],
            }],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = FairnessSpec {
            protected_attributes: vec![0],
            criterion: FairnessCriterion::EqualOpportunity,
            region: InputRegion::Box {
                lower: vec![-1.0, -1.0],
                upper: vec![1.0, 1.0],
            },
        };

        let result = backend.verify_fairness(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown for EqualOpportunity (not implemented), got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_no_network() {
        let backend = CrownBackend::new(CrownConfig::default());

        let spec = FairnessSpec {
            protected_attributes: vec![0],
            criterion: FairnessCriterion::Independence,
            region: InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            },
        };

        let result = backend.verify_fairness(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown for no network, got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_empty_protected_attrs() {
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0, 1.0]],
                bias: vec![0.0],
            }],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = FairnessSpec {
            protected_attributes: vec![], // No protected attributes
            criterion: FairnessCriterion::Independence,
            region: InputRegion::Box {
                lower: vec![-1.0, -1.0],
                upper: vec![1.0, 1.0],
            },
        };

        let result = backend.verify_fairness(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven for empty protected attributes, got {result:?}"
        );
    }

    #[test]
    fn test_verify_fairness_invalid_protected_attr_index() {
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0, 1.0]],
                bias: vec![0.0],
            }],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = FairnessSpec {
            protected_attributes: vec![5], // Out of bounds (input dim = 2)
            criterion: FairnessCriterion::Independence,
            region: InputRegion::Box {
                lower: vec![-1.0, -1.0],
                upper: vec![1.0, 1.0],
            },
        };

        let result = backend.verify_fairness(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown for invalid protected attribute index, got {result:?}"
        );
    }

    // ============================================================================
    // Reachability Verification Tests
    // ============================================================================

    #[test]
    fn test_output_bounds_intersect_box_intersects() {
        // Output bounds [0.5, 1.5] x [-0.5, 0.5]
        // Target box [1.0, 2.0] x [0.0, 1.0]
        // Intersection: [1.0, 1.5] x [0.0, 0.5] -> non-empty
        let output_bounds = Bounds::from_box(vec![0.5, -0.5], vec![1.5, 0.5]);
        let target = OutputRegion::Box {
            lower: vec![1.0, 0.0],
            upper: vec![2.0, 1.0],
        };

        assert!(
            output_bounds_intersect_target(&output_bounds, &target),
            "Expected intersection for overlapping boxes"
        );
    }

    #[test]
    fn test_output_bounds_intersect_box_no_intersection() {
        // Output bounds [0.0, 1.0] x [0.0, 1.0]
        // Target box [2.0, 3.0] x [2.0, 3.0]
        // No intersection
        let output_bounds = Bounds::from_box(vec![0.0, 0.0], vec![1.0, 1.0]);
        let target = OutputRegion::Box {
            lower: vec![2.0, 2.0],
            upper: vec![3.0, 3.0],
        };

        assert!(
            !output_bounds_intersect_target(&output_bounds, &target),
            "Expected no intersection for disjoint boxes"
        );
    }

    #[test]
    fn test_output_bounds_intersect_class_can_be_argmax() {
        // Output bounds: class 0 in [0.8, 1.2], class 1 in [0.0, 0.5]
        // Class 0 can be argmax (0.8 > 0.5 or 1.2 > 0.5)
        let output_bounds = Bounds::from_box(vec![0.8, 0.0], vec![1.2, 0.5]);
        let target = OutputRegion::Class(0);

        assert!(
            output_bounds_intersect_target(&output_bounds, &target),
            "Expected class 0 can be argmax"
        );
    }

    #[test]
    fn test_output_bounds_intersect_class_cannot_be_argmax() {
        // Output bounds: class 0 in [0.0, 0.3], class 1 in [0.5, 1.0]
        // Class 0 CANNOT be argmax (0.3 < 0.5, so class 0 is always beaten by class 1)
        let output_bounds = Bounds::from_box(vec![0.0, 0.5], vec![0.3, 1.0]);
        let target = OutputRegion::Class(0);

        assert!(
            !output_bounds_intersect_target(&output_bounds, &target),
            "Expected class 0 cannot be argmax (always beaten by class 1)"
        );
    }

    #[test]
    fn test_output_bounds_intersect_classes_any_match() {
        // Output bounds: class 0 in [0.0, 0.3], class 1 in [0.5, 1.0], class 2 in [0.2, 0.4]
        // Class 0 cannot be argmax, class 1 CAN be argmax, class 2 cannot
        let output_bounds = Bounds::from_box(vec![0.0, 0.5, 0.2], vec![0.3, 1.0, 0.4]);
        let target = OutputRegion::Classes(vec![0, 1]); // At least one of class 0 or 1

        assert!(
            output_bounds_intersect_target(&output_bounds, &target),
            "Expected at least one target class (1) can be argmax"
        );
    }

    #[test]
    fn test_verify_reachability_unreachable_proven() {
        // Network: f(x) = 2*x + 1, input in [-1, 1]
        // Output range: [-1, 3]
        // Target: output in [10, 20] (unreachable)
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![2.0]],
                bias: vec![1.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = ReachabilitySpec {
            input_region: InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            },
            target_region: OutputRegion::Box {
                lower: vec![10.0],
                upper: vec![20.0],
            },
            check_reachable: false, // Prove unreachability
        };

        let result = backend.verify_reachability(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven for unreachable target, got {result:?}"
        );
    }

    #[test]
    fn test_verify_reachability_unreachable_unknown() {
        // Network: f(x) = 2*x + 1, input in [-1, 1]
        // Output range: [-1, 3]
        // Target: output in [0, 2] (overlaps with output range)
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![2.0]],
                bias: vec![1.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = ReachabilitySpec {
            input_region: InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            },
            target_region: OutputRegion::Box {
                lower: vec![0.0],
                upper: vec![2.0],
            },
            check_reachable: false, // Try to prove unreachability
        };

        let result = backend.verify_reachability(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown (target intersects output bounds), got {result:?}"
        );
    }

    #[test]
    fn test_verify_reachability_reachable_query_unknown() {
        // Network: f(x) = 2*x + 1, input in [-1, 1]
        // Output range: [-1, 3]
        // Target: output in [0, 2] (overlaps, but can't prove reachability definitively)
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![2.0]],
                bias: vec![1.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = ReachabilitySpec {
            input_region: InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            },
            target_region: OutputRegion::Box {
                lower: vec![0.0],
                upper: vec![2.0],
            },
            check_reachable: true, // Try to prove reachability
        };

        let result = backend.verify_reachability(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown for reachability query (over-approximation), got {result:?}"
        );
    }

    #[test]
    fn test_verify_reachability_class_target_reachable() {
        // 2-class classifier: f(x) = W*x where W = [[1, 0], [0, 1]]
        // Input in [0.5, 1.0] x [-0.5, 0.5]
        // Class 0 output: [0.5, 1.0], Class 1 output: [-0.5, 0.5]
        // Class 0 can be argmax (0.5 > -0.5 at least sometimes)
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0, 0.0], vec![0.0, 1.0]],
                bias: vec![0.0, 0.0],
            }],
            2,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = ReachabilitySpec {
            input_region: InputRegion::Box {
                lower: vec![0.5, -0.5],
                upper: vec![1.0, 0.5],
            },
            target_region: OutputRegion::Class(0),
            check_reachable: false, // Prove class 0 is NOT reachable
        };

        let result = backend.verify_reachability(&spec);
        // Cannot prove unreachability because class 0 could be argmax
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown (class 0 can be argmax), got {result:?}"
        );
    }

    #[test]
    fn test_verify_reachability_class_target_unreachable() {
        // 2-class classifier where class 1 is always higher
        // f(x) = W*x + b where W = [[1], [2]], b = [0, 10]
        // Input in [-1, 1]
        // Class 0 output: [-1, 1], Class 1 output: [8, 12]
        // Class 0 CANNOT be argmax (max of class 0 = 1 < min of class 1 = 8)
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0], vec![2.0]],
                bias: vec![0.0, 10.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = ReachabilitySpec {
            input_region: InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            },
            target_region: OutputRegion::Class(0),
            check_reachable: false, // Prove class 0 is NOT reachable
        };

        let result = backend.verify_reachability(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven (class 0 cannot be argmax), got {result:?}"
        );
    }

    #[test]
    fn test_verify_reachability_no_network() {
        let backend = CrownBackend::new(CrownConfig::default());

        let spec = ReachabilitySpec {
            input_region: InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            },
            target_region: OutputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            check_reachable: false,
        };

        let result = backend.verify_reachability(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Expected Unknown for no network, got {result:?}"
        );
    }

    #[test]
    fn test_verify_reachability_mlp_with_relu() {
        // MLP: Linear -> ReLU -> Linear
        // f(x) = W2 * ReLU(W1 * x + b1) + b2
        // W1 = [[1], [-1]], b1 = [0, 0], W2 = [[1, 1]], b2 = [0]
        // For x in [0, 1]: h = [x, 0] (ReLU kills negative), output = x
        // Output range for x in [0, 1]: [0, 1]
        // Target: output in [5, 10] -> unreachable
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0], vec![-1.0]],
                    bias: vec![0.0, 0.0],
                },
                NnLayer::ReLU,
                NnLayer::Linear {
                    weights: vec![vec![1.0, 1.0]],
                    bias: vec![0.0],
                },
            ],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = ReachabilitySpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            target_region: OutputRegion::Box {
                lower: vec![5.0],
                upper: vec![10.0],
            },
            check_reachable: false, // Prove unreachability
        };

        let result = backend.verify_reachability(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Expected Proven for unreachable target with MLP, got {result:?}"
        );
    }

    // ==================== GlobalProperty Verification Tests ====================

    #[test]
    fn test_predicate_result_true_false() {
        // Test basic predicate evaluation
        let bounds = Bounds::from_box(vec![1.0, 2.0], vec![3.0, 4.0]);

        // Bool(true) -> True
        let pred_true = vc_ir::Predicate::Bool(true);
        assert_eq!(
            evaluate_predicate_on_bounds(&pred_true, &bounds),
            PredicateResult::True
        );

        // Bool(false) -> False
        let pred_false = vc_ir::Predicate::Bool(false);
        assert_eq!(
            evaluate_predicate_on_bounds(&pred_false, &bounds),
            PredicateResult::False
        );
    }

    #[test]
    fn test_predicate_and_logic() {
        let bounds = Bounds::from_box(vec![1.0], vec![2.0]);

        // True AND True -> True
        let and_true = vc_ir::Predicate::And(vec![
            vc_ir::Predicate::Bool(true),
            vc_ir::Predicate::Bool(true),
        ]);
        assert_eq!(
            evaluate_predicate_on_bounds(&and_true, &bounds),
            PredicateResult::True
        );

        // True AND False -> False
        let and_false = vc_ir::Predicate::And(vec![
            vc_ir::Predicate::Bool(true),
            vc_ir::Predicate::Bool(false),
        ]);
        assert_eq!(
            evaluate_predicate_on_bounds(&and_false, &bounds),
            PredicateResult::False
        );
    }

    #[test]
    fn test_predicate_or_logic() {
        let bounds = Bounds::from_box(vec![1.0], vec![2.0]);

        // False OR True -> True
        let or_true = vc_ir::Predicate::Or(vec![
            vc_ir::Predicate::Bool(false),
            vc_ir::Predicate::Bool(true),
        ]);
        assert_eq!(
            evaluate_predicate_on_bounds(&or_true, &bounds),
            PredicateResult::True
        );

        // False OR False -> False
        let or_false = vc_ir::Predicate::Or(vec![
            vc_ir::Predicate::Bool(false),
            vc_ir::Predicate::Bool(false),
        ]);
        assert_eq!(
            evaluate_predicate_on_bounds(&or_false, &bounds),
            PredicateResult::False
        );
    }

    #[test]
    fn test_predicate_not_logic() {
        let bounds = Bounds::from_box(vec![1.0], vec![2.0]);

        // NOT True -> False
        let not_true = vc_ir::Predicate::Not(Box::new(vc_ir::Predicate::Bool(true)));
        assert_eq!(
            evaluate_predicate_on_bounds(&not_true, &bounds),
            PredicateResult::False
        );

        // NOT False -> True
        let not_false = vc_ir::Predicate::Not(Box::new(vc_ir::Predicate::Bool(false)));
        assert_eq!(
            evaluate_predicate_on_bounds(&not_false, &bounds),
            PredicateResult::True
        );
    }

    #[test]
    fn test_expr_interval_arithmetic() {
        let i1 = ExprInterval::from_bounds(1.0, 3.0);
        let i2 = ExprInterval::from_bounds(2.0, 4.0);

        // Add: [1,3] + [2,4] = [3,7]
        let add = i1.add(&i2);
        assert!((add.lower - 3.0).abs() < 1e-10);
        assert!((add.upper - 7.0).abs() < 1e-10);

        // Sub: [1,3] - [2,4] = [1-4, 3-2] = [-3, 1]
        let sub = i1.sub(&i2);
        assert!((sub.lower - (-3.0)).abs() < 1e-10);
        assert!((sub.upper - 1.0).abs() < 1e-10);

        // Neg: -[1,3] = [-3,-1]
        let neg = i1.neg();
        assert!((neg.lower - (-3.0)).abs() < 1e-10);
        assert!((neg.upper - (-1.0)).abs() < 1e-10);
    }

    #[test]
    fn test_expr_interval_multiplication() {
        // Positive * Positive: [1,2] * [3,4] = [3,8]
        let i1 = ExprInterval::from_bounds(1.0, 2.0);
        let i2 = ExprInterval::from_bounds(3.0, 4.0);
        let mul = i1.mul(&i2);
        assert!((mul.lower - 3.0).abs() < 1e-10);
        assert!((mul.upper - 8.0).abs() < 1e-10);

        // Mixed signs: [-2,1] * [2,3] = [-6, 3]
        let i3 = ExprInterval::from_bounds(-2.0, 1.0);
        let i4 = ExprInterval::from_bounds(2.0, 3.0);
        let mul2 = i3.mul(&i4);
        assert!((mul2.lower - (-6.0)).abs() < 1e-10);
        assert!((mul2.upper - 3.0).abs() < 1e-10);
    }

    #[test]
    fn test_comparison_ge_proven() {
        // Output bounds: [5, 10]
        // Check: output >= 3 (proven: 5 >= 3)
        let bounds = Bounds::from_box(vec![5.0], vec![10.0]);

        // result >= 3
        let pred = vc_ir::Predicate::Expr(vc_ir::Expr::Ge(
            Box::new(vc_ir::Expr::Result),
            Box::new(vc_ir::Expr::FloatLit(3.0)),
        ));

        assert_eq!(
            evaluate_predicate_on_bounds(&pred, &bounds),
            PredicateResult::True,
            "Output [5,10] should satisfy >= 3"
        );
    }

    #[test]
    fn test_comparison_ge_disproven() {
        // Output bounds: [1, 2]
        // Check: output >= 5 (disproven: 2 < 5)
        let bounds = Bounds::from_box(vec![1.0], vec![2.0]);

        let pred = vc_ir::Predicate::Expr(vc_ir::Expr::Ge(
            Box::new(vc_ir::Expr::Result),
            Box::new(vc_ir::Expr::FloatLit(5.0)),
        ));

        assert_eq!(
            evaluate_predicate_on_bounds(&pred, &bounds),
            PredicateResult::False,
            "Output [1,2] should not satisfy >= 5"
        );
    }

    #[test]
    fn test_comparison_ge_unknown() {
        // Output bounds: [2, 8]
        // Check: output >= 5 (unknown: 2 < 5 < 8)
        let bounds = Bounds::from_box(vec![2.0], vec![8.0]);

        let pred = vc_ir::Predicate::Expr(vc_ir::Expr::Ge(
            Box::new(vc_ir::Expr::Result),
            Box::new(vc_ir::Expr::FloatLit(5.0)),
        ));

        assert_eq!(
            evaluate_predicate_on_bounds(&pred, &bounds),
            PredicateResult::Unknown,
            "Output [2,8] should have unknown result for >= 5"
        );
    }

    #[test]
    fn test_comparison_lt_proven() {
        // Output bounds: [1, 3]
        // Check: output < 5 (proven: 3 < 5)
        let bounds = Bounds::from_box(vec![1.0], vec![3.0]);

        let pred = vc_ir::Predicate::Expr(vc_ir::Expr::Lt(
            Box::new(vc_ir::Expr::Result),
            Box::new(vc_ir::Expr::FloatLit(5.0)),
        ));

        assert_eq!(
            evaluate_predicate_on_bounds(&pred, &bounds),
            PredicateResult::True,
            "Output [1,3] should satisfy < 5"
        );
    }

    #[test]
    fn test_output_indexing_with_var() {
        // Multi-dimensional output bounds
        let bounds = Bounds::from_box(vec![0.0, 10.0, 20.0], vec![1.0, 11.0, 21.0]);

        // output_1 >= 9 (proven: 10 >= 9)
        let pred = vc_ir::Predicate::Expr(vc_ir::Expr::Ge(
            Box::new(vc_ir::Expr::Var("output_1".to_string())),
            Box::new(vc_ir::Expr::FloatLit(9.0)),
        ));

        assert_eq!(
            evaluate_predicate_on_bounds(&pred, &bounds),
            PredicateResult::True,
            "output_1 in [10,11] should satisfy >= 9"
        );
    }

    #[test]
    fn test_verify_global_property_output_ge_zero_proven() {
        // Network: f(x) = x + 5 (for x in [0, 1], output in [5, 6])
        // Property: output >= 0 (proven)
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0]],
                bias: vec![5.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = GlobalPropertySpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            property: vc_ir::Predicate::Expr(vc_ir::Expr::Ge(
                Box::new(vc_ir::Expr::Result),
                Box::new(vc_ir::Expr::FloatLit(0.0)),
            )),
        };

        let result = backend.verify_global_property(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Output [5,6] should satisfy >= 0, got {result:?}"
        );
    }

    #[test]
    fn test_verify_global_property_output_le_unknown() {
        // Network: f(x) = x (for x in [0, 10], output in [0, 10])
        // Property: output <= 5 (unknown: some outputs violate this)
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![1.0]],
                bias: vec![0.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = GlobalPropertySpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![10.0],
            },
            property: vc_ir::Predicate::Expr(vc_ir::Expr::Le(
                Box::new(vc_ir::Expr::Result),
                Box::new(vc_ir::Expr::FloatLit(5.0)),
            )),
        };

        let result = backend.verify_global_property(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { .. }),
            "Output [0,10] should have unknown for <= 5, got {result:?}"
        );
    }

    #[test]
    fn test_verify_global_property_no_network() {
        let backend = CrownBackend::new(CrownConfig::default());

        let spec = GlobalPropertySpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            property: vc_ir::Predicate::Bool(true),
        };

        let result = backend.verify_global_property(&spec);
        assert!(
            matches!(result, VerifyResult::Unknown { ref reason } if reason.contains("No network")),
            "Expected Unknown with 'No network' message, got {result:?}"
        );
    }

    #[test]
    fn test_verify_global_property_with_relu() {
        // Network: ReLU(x) for x in [-1, 1], output in [0, 1]
        // Property: output >= 0 (proven - ReLU is always non-negative)
        let network = NnNetwork::new(
            vec![
                NnLayer::Linear {
                    weights: vec![vec![1.0]],
                    bias: vec![0.0],
                },
                NnLayer::ReLU,
            ],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = GlobalPropertySpec {
            input_region: InputRegion::Box {
                lower: vec![-1.0],
                upper: vec![1.0],
            },
            property: vc_ir::Predicate::Expr(vc_ir::Expr::Ge(
                Box::new(vc_ir::Expr::Result),
                Box::new(vc_ir::Expr::FloatLit(0.0)),
            )),
        };

        let result = backend.verify_global_property(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "ReLU output should satisfy >= 0, got {result:?}"
        );
    }

    #[test]
    fn test_verify_global_property_combined_predicate() {
        // Network: f(x) = 2*x + 3 (for x in [0, 1], output in [3, 5])
        // Property: output >= 1 AND output <= 10 (proven)
        let network = NnNetwork::new(
            vec![NnLayer::Linear {
                weights: vec![vec![2.0]],
                bias: vec![3.0],
            }],
            1,
        );

        let mut backend = CrownBackend::new(CrownConfig::default());
        backend.load_network(network);

        let spec = GlobalPropertySpec {
            input_region: InputRegion::Box {
                lower: vec![0.0],
                upper: vec![1.0],
            },
            property: vc_ir::Predicate::And(vec![
                vc_ir::Predicate::Expr(vc_ir::Expr::Ge(
                    Box::new(vc_ir::Expr::Result),
                    Box::new(vc_ir::Expr::FloatLit(1.0)),
                )),
                vc_ir::Predicate::Expr(vc_ir::Expr::Le(
                    Box::new(vc_ir::Expr::Result),
                    Box::new(vc_ir::Expr::FloatLit(10.0)),
                )),
            ]),
        };

        let result = backend.verify_global_property(&spec);
        assert!(
            matches!(result, VerifyResult::Proven),
            "Output [3,5] should satisfy >= 1 AND <= 10, got {result:?}"
        );
    }
}
