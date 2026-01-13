#!/usr/bin/env python3
"""
Generate test safetensors files for trust_crown unit tests.

Creates several test models:
1. simple_mlp.safetensors - A simple 2->3->1 MLP with ReLU
2. sequential_naming.safetensors - Sequential layer naming (0.weight, 2.weight)
3. named_layers.safetensors - Named layers (fc1.weight, fc2.weight)
4. no_bias.safetensors - Network without bias terms
"""

import numpy as np

try:
    from safetensors.numpy import save_file
except ImportError:
    print("Installing safetensors...")
    import subprocess
    subprocess.check_call(["pip", "install", "safetensors"])
    from safetensors.numpy import save_file


def create_simple_mlp():
    """Create a 2->3->1 MLP with known weights."""
    tensors = {
        # Layer 0: 2->3 (weight shape: [3, 2], bias shape: [3])
        "0.weight": np.array([
            [0.1, 0.2],
            [0.3, 0.4],
            [0.5, 0.6],
        ], dtype=np.float32),
        "0.bias": np.array([0.01, 0.02, 0.03], dtype=np.float32),

        # Layer 1 (ReLU) has no weights

        # Layer 2: 3->1 (weight shape: [1, 3], bias shape: [1])
        "2.weight": np.array([
            [0.7, 0.8, 0.9],
        ], dtype=np.float32),
        "2.bias": np.array([0.04], dtype=np.float32),
    }
    save_file(tensors, "simple_mlp.safetensors")
    print("Created simple_mlp.safetensors (2->3->ReLU->1)")


def create_sequential_naming():
    """Create model with sequential layer naming (0, 2, 4 skipping activations)."""
    tensors = {
        # Layer 0: 3->4
        "0.weight": np.array([
            [0.1, 0.2, 0.3],
            [0.4, 0.5, 0.6],
            [0.7, 0.8, 0.9],
            [1.0, 1.1, 1.2],
        ], dtype=np.float32),
        "0.bias": np.array([0.1, 0.2, 0.3, 0.4], dtype=np.float32),

        # Layer 2: 4->2
        "2.weight": np.array([
            [0.1, 0.2, 0.3, 0.4],
            [0.5, 0.6, 0.7, 0.8],
        ], dtype=np.float32),
        "2.bias": np.array([0.1, 0.2], dtype=np.float32),
    }
    save_file(tensors, "sequential_naming.safetensors")
    print("Created sequential_naming.safetensors (3->4->ReLU->2)")


def create_named_layers():
    """Create model with named layers (fc1, fc2)."""
    tensors = {
        # fc1: 2->4
        "fc1.weight": np.array([
            [0.1, 0.2],
            [0.3, 0.4],
            [0.5, 0.6],
            [0.7, 0.8],
        ], dtype=np.float32),
        "fc1.bias": np.array([0.1, 0.2, 0.3, 0.4], dtype=np.float32),

        # fc2: 4->2
        "fc2.weight": np.array([
            [0.1, 0.2, 0.3, 0.4],
            [0.5, 0.6, 0.7, 0.8],
        ], dtype=np.float32),
        "fc2.bias": np.array([0.1, 0.2], dtype=np.float32),
    }
    save_file(tensors, "named_layers.safetensors")
    print("Created named_layers.safetensors (2->4->ReLU->2)")


def create_no_bias():
    """Create model without bias terms."""
    tensors = {
        "0.weight": np.array([
            [0.5, 0.5],
            [0.5, 0.5],
        ], dtype=np.float32),
        "2.weight": np.array([
            [1.0, 1.0],
        ], dtype=np.float32),
    }
    save_file(tensors, "no_bias.safetensors")
    print("Created no_bias.safetensors (2->2->ReLU->1, no bias)")


def create_single_layer():
    """Create single linear layer model."""
    tensors = {
        "0.weight": np.array([
            [1.0, 2.0, 3.0],
            [4.0, 5.0, 6.0],
        ], dtype=np.float32),
        "0.bias": np.array([0.1, 0.2], dtype=np.float32),
    }
    save_file(tensors, "single_layer.safetensors")
    print("Created single_layer.safetensors (3->2, no activation)")


def create_f64_model():
    """Create model with f64 weights (double precision)."""
    tensors = {
        "0.weight": np.array([
            [0.1, 0.2],
            [0.3, 0.4],
        ], dtype=np.float64),
        "0.bias": np.array([0.01, 0.02], dtype=np.float64),
    }
    save_file(tensors, "f64_model.safetensors")
    print("Created f64_model.safetensors (2->2, f64 precision)")


if __name__ == "__main__":
    import os
    os.chdir(os.path.dirname(os.path.abspath(__file__)))

    create_simple_mlp()
    create_sequential_naming()
    create_named_layers()
    create_no_bias()
    create_single_layer()
    create_f64_model()

    print("\nAll test safetensors files created successfully!")
