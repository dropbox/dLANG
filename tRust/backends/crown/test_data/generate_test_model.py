#!/usr/bin/env python3
"""Generate simple ONNX models for testing trust_crown ONNX loading.

Run: python generate_test_model.py

Creates:
  - simple_mlp.onnx: 2-layer MLP with ReLU (input: 2, hidden: 3, output: 1)
"""

import numpy as np

try:
    import onnx
    from onnx import TensorProto, helper, numpy_helper
except ImportError:
    print("Error: ONNX library required. Install with: pip install onnx")
    exit(1)


def create_simple_mlp():
    """Create a simple 2-layer MLP: input(2) -> Linear(3) -> ReLU -> Linear(1)"""

    # Define weights and biases
    # Layer 1: 2 inputs -> 3 outputs
    W1 = np.array([
        [0.5, -0.5],   # neuron 0
        [0.3, 0.7],    # neuron 1
        [-0.2, 0.4],   # neuron 2
    ], dtype=np.float32)  # shape: [3, 2]

    b1 = np.array([0.1, -0.1, 0.0], dtype=np.float32)  # shape: [3]

    # Layer 2: 3 inputs -> 1 output
    W2 = np.array([
        [1.0, -1.0, 0.5],  # neuron 0
    ], dtype=np.float32)  # shape: [1, 3]

    b2 = np.array([0.2], dtype=np.float32)  # shape: [1]

    # Create ONNX graph
    # Inputs
    X = helper.make_tensor_value_info('input', TensorProto.FLOAT, [1, 2])

    # Outputs
    Y = helper.make_tensor_value_info('output', TensorProto.FLOAT, [1, 1])

    # Initializers (weights and biases)
    W1_init = numpy_helper.from_array(W1, 'W1')
    b1_init = numpy_helper.from_array(b1, 'b1')
    W2_init = numpy_helper.from_array(W2, 'W2')
    b2_init = numpy_helper.from_array(b2, 'b2')

    # Nodes
    # Gemm: Y = alpha * A * B + beta * C, with transB=1 means B is [out, in]
    gemm1 = helper.make_node(
        'Gemm',
        inputs=['input', 'W1', 'b1'],
        outputs=['gemm1_out'],
        name='gemm1',
        alpha=1.0,
        beta=1.0,
        transA=0,
        transB=1,  # W1 is [out, in] = [3, 2]
    )

    relu = helper.make_node(
        'Relu',
        inputs=['gemm1_out'],
        outputs=['relu_out'],
        name='relu1',
    )

    gemm2 = helper.make_node(
        'Gemm',
        inputs=['relu_out', 'W2', 'b2'],
        outputs=['output'],
        name='gemm2',
        alpha=1.0,
        beta=1.0,
        transA=0,
        transB=1,  # W2 is [out, in] = [1, 3]
    )

    # Create graph
    graph = helper.make_graph(
        [gemm1, relu, gemm2],
        'simple_mlp',
        [X],
        [Y],
        [W1_init, b1_init, W2_init, b2_init],
    )

    # Create model
    model = helper.make_model(graph, opset_imports=[helper.make_opsetid('', 13)])
    model.ir_version = 7

    # Validate
    onnx.checker.check_model(model)

    return model


def main():
    # Generate simple MLP
    mlp = create_simple_mlp()
    onnx.save(mlp, 'simple_mlp.onnx')
    print("Created simple_mlp.onnx")

    # Print model info
    print(f"  Input: {mlp.graph.input[0].type.tensor_type.shape}")
    print(f"  Output: {mlp.graph.output[0].type.tensor_type.shape}")
    print(f"  Nodes: {[n.op_type for n in mlp.graph.node]}")


if __name__ == '__main__':
    main()
