//! Interval bounds for verification (gamma-crown integration)
//!
//! This module provides interval arithmetic types compatible with gamma-crown's
//! BoundedTensor, enabling compile-time and runtime verification of tensor operations.

use ndarray::{ArrayD, IxDyn};
use num_traits::Float;

/// Interval bounds for numerical verification
///
/// For each element, maintains [lower, upper] bounds such that:
/// `lower[i] <= actual_value[i] <= upper[i]`
///
/// Used by gamma-crown for IBP (Interval Bound Propagation) and CROWN.
#[derive(Clone, Debug)]
pub struct IntervalBounds<T> {
    /// Lower bounds (element-wise)
    pub lower: ArrayD<T>,
    /// Upper bounds (element-wise)
    pub upper: ArrayD<T>,
}

impl<T: Float + Clone> IntervalBounds<T> {
    /// Create bounds from lower and upper arrays
    pub fn new(lower: ArrayD<T>, upper: ArrayD<T>) -> Self {
        debug_assert_eq!(lower.shape(), upper.shape());
        Self { lower, upper }
    }

    /// Create bounds for a concrete value (lower == upper)
    pub fn concrete(values: ArrayD<T>) -> Self {
        Self {
            lower: values.clone(),
            upper: values,
        }
    }

    /// Create bounds with epsilon perturbation around center
    ///
    /// Each element gets bounds [center - epsilon, center + epsilon]
    pub fn from_epsilon(center: ArrayD<T>, epsilon: T) -> Self {
        let lower = center.mapv(|x| x - epsilon);
        let upper = center.mapv(|x| x + epsilon);
        Self { lower, upper }
    }

    /// Get shape of bounds
    pub fn shape(&self) -> &[usize] {
        self.lower.shape()
    }

    /// Maximum width across all elements
    pub fn max_width(&self) -> T {
        self.upper
            .iter()
            .zip(self.lower.iter())
            .map(|(u, l)| *u - *l)
            .fold(T::neg_infinity(), |a, b| if a > b { a } else { b })
    }

    /// Check if any bound is infinite
    pub fn has_unbounded(&self) -> bool {
        self.lower.iter().any(|x| x.is_infinite())
            || self.upper.iter().any(|x| x.is_infinite())
    }

    /// Check if any bound contains NaN
    pub fn has_nan(&self) -> bool {
        self.lower.iter().any(|x| x.is_nan())
            || self.upper.iter().any(|x| x.is_nan())
    }

    /// Check if bounds are finite (no inf, no nan)
    pub fn is_finite(&self) -> bool {
        !self.has_unbounded() && !self.has_nan()
    }
}

/// Interval arithmetic operations (for IBP)
impl<T: Float + Clone> IntervalBounds<T> {
    /// Add two interval bounds: [a,b] + [c,d] = [a+c, b+d]
    pub fn add(&self, other: &Self) -> Self {
        Self {
            lower: &self.lower + &other.lower,
            upper: &self.upper + &other.upper,
        }
    }

    /// Subtract: [a,b] - [c,d] = [a-d, b-c]
    pub fn sub(&self, other: &Self) -> Self {
        Self {
            lower: &self.lower - &other.upper,
            upper: &self.upper - &other.lower,
        }
    }

    /// Scale by positive constant: c * [a,b] = [c*a, c*b] if c >= 0
    pub fn scale(&self, c: T) -> Self {
        if c >= T::zero() {
            Self {
                lower: self.lower.mapv(|x| x * c),
                upper: self.upper.mapv(|x| x * c),
            }
        } else {
            // Negative scale flips bounds
            Self {
                lower: self.upper.mapv(|x| x * c),
                upper: self.lower.mapv(|x| x * c),
            }
        }
    }

    /// Apply ReLU: max(0, [a,b]) = [max(0,a), max(0,b)]
    pub fn relu(&self) -> Self {
        Self {
            lower: self.lower.mapv(|x| if x > T::zero() { x } else { T::zero() }),
            upper: self.upper.mapv(|x| if x > T::zero() { x } else { T::zero() }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ndarray::arr1;

    #[test]
    fn test_from_epsilon() {
        let center = arr1(&[1.0f32, 2.0, 3.0]).into_dyn();
        let bounds = IntervalBounds::from_epsilon(center, 0.1);
        assert!((bounds.lower[[0]] - 0.9).abs() < 1e-6);
        assert!((bounds.upper[[0]] - 1.1).abs() < 1e-6);
    }

    #[test]
    fn test_relu_bounds() {
        let lower = arr1(&[-1.0f32, 0.5, -0.5]).into_dyn();
        let upper = arr1(&[1.0f32, 1.5, 0.5]).into_dyn();
        let bounds = IntervalBounds::new(lower, upper);
        let relu = bounds.relu();
        assert_eq!(relu.lower[[0]], 0.0);
        assert_eq!(relu.upper[[0]], 1.0);
    }
}
