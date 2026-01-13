//! Shape types for Tensor Forge

/// Tensor shape representation
#[derive(Clone, Debug, PartialEq)]
pub enum Shape {
    /// Fully static (compile-time known)
    Static(Vec<usize>),

    /// Dynamic (runtime determined)
    Dynamic(Vec<usize>),

    /// Scalar (0-dimensional)
    Scalar,
}

impl Shape {
    /// Create a static shape
    pub fn new(dims: &[usize]) -> Self {
        Shape::Dynamic(dims.to_vec())
    }

    /// Get dimensions as slice
    pub fn dims(&self) -> &[usize] {
        match self {
            Shape::Static(d) | Shape::Dynamic(d) => d,
            Shape::Scalar => &[],
        }
    }

    /// Number of dimensions (rank)
    pub fn ndim(&self) -> usize {
        self.dims().len()
    }

    /// Total number of elements
    pub fn numel(&self) -> usize {
        self.dims().iter().product()
    }

    /// Check if shapes are broadcastable
    pub fn is_broadcastable(&self, other: &Shape) -> bool {
        let a = self.dims();
        let b = other.dims();

        // Align from the right
        let max_len = a.len().max(b.len());
        for i in 0..max_len {
            let dim_a = if i < a.len() { a[a.len() - 1 - i] } else { 1 };
            let dim_b = if i < b.len() { b[b.len() - 1 - i] } else { 1 };

            if dim_a != dim_b && dim_a != 1 && dim_b != 1 {
                return false;
            }
        }
        true
    }

    /// Compute broadcast result shape
    pub fn broadcast(&self, other: &Shape) -> Option<Shape> {
        if !self.is_broadcastable(other) {
            return None;
        }

        let a = self.dims();
        let b = other.dims();
        let max_len = a.len().max(b.len());
        let mut result = Vec::with_capacity(max_len);

        for i in 0..max_len {
            let dim_a = if i < a.len() { a[a.len() - 1 - i] } else { 1 };
            let dim_b = if i < b.len() { b[b.len() - 1 - i] } else { 1 };
            result.push(dim_a.max(dim_b));
        }

        result.reverse();
        Some(Shape::Dynamic(result))
    }
}

impl From<&[usize]> for Shape {
    fn from(dims: &[usize]) -> Self {
        Shape::Dynamic(dims.to_vec())
    }
}

impl From<Vec<usize>> for Shape {
    fn from(dims: Vec<usize>) -> Self {
        Shape::Dynamic(dims)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_numel() {
        let s = Shape::new(&[2, 3, 4]);
        assert_eq!(s.numel(), 24);
    }

    #[test]
    fn test_broadcast() {
        let a = Shape::new(&[2, 1, 4]);
        let b = Shape::new(&[3, 4]);
        let c = a.broadcast(&b).unwrap();
        assert_eq!(c.dims(), &[2, 3, 4]);
    }
}
