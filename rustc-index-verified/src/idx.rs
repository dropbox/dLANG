//! Core Idx trait for type-safe indexing.
//!
//! This module provides the `Idx` trait which represents newtyped `usize` wrappers
//! that prevent mixing indices for different domains.
//!
//! ## Verification Targets
//!
//! - `Idx::new`: Bounds safety, identity property
//! - `Idx::index`: Returns correct underlying value
//! - `Idx::plus`: Arithmetic correctness
//! - `Idx::increment_by`: Mutation correctness

use std::fmt::Debug;
use std::hash::Hash;
use std::ops;
use std::slice::SliceIndex;

// Note: #[requires] and #[ensures] are trustc built-in attributes.
// They use cfg_attr(trust_verify, ...) for cargo test compatibility.

/// Represents a newtyped `usize` wrapper.
///
/// Purpose: avoid mixing indexes for different bitvector domains.
///
/// ## Verification Properties
///
/// For any implementation of `Idx`:
/// - `new(idx).index() == idx` (round-trip identity, when idx is in bounds)
/// - `plus(n).index() == self.index() + n` (arithmetic correctness)
/// - `increment_by(n)` equivalent to `*self = self.plus(n)`
pub trait Idx: Copy + 'static + Eq + PartialEq + Debug + Hash {
    /// Creates a new index from a `usize`.
    ///
    /// # Specification (tRust)
    /// ```trust
    /// #[requires(/* idx representable by Self */)]
    /// #[ensures(result.index() == idx)]
    /// ```
    ///
    /// Implementation-specific preconditions:
    /// - `usize`: Always succeeds (no precondition)
    /// - `u32`: `idx <= u32::MAX as usize`
    fn new(idx: usize) -> Self;

    /// Returns the underlying `usize` value.
    ///
    /// # Specification (tRust)
    /// ```trust
    /// #[ensures(result == /* value originally passed to new() */)]
    /// ```
    ///
    /// This is the inverse of `new()` - extracting the wrapped index.
    #[cfg_attr(trust_verify, pure)]
    fn index(self) -> usize;

    /// Increments this index by `amount` in place.
    ///
    /// # Specification (tRust)
    ///
    /// Precondition: `self.index() + amount` must not overflow and must be representable.
    /// Postcondition: `self.index() == old(self.index()) + amount`
    ///
    /// Note: Actual verification attributes are on the implementation methods.
    /// Trait default methods delegate to `plus()` which has the verification.
    #[inline]
    fn increment_by(&mut self, amount: usize) {
        *self = self.plus(amount);
    }

    /// Returns a new index that is `amount` greater than `self`.
    ///
    /// # Specification (tRust)
    ///
    /// Precondition: `self.index() + amount` must not overflow and must be representable.
    /// Postcondition: `result.index() == self.index() + amount`
    ///
    /// Note: Actual verification attributes are on the implementation methods.
    /// Trait default methods delegate to `new()` and `index()` which have verification.
    #[inline]
    #[must_use = "Use `increment_by` if you wanted to update the index in-place"]
    fn plus(self, amount: usize) -> Self {
        Self::new(self.index() + amount)
    }
}

/// Implementation of `Idx` for `usize`.
///
/// This is the trivial implementation where the index IS the usize.
/// Both `new` and `index` are identity functions.
impl Idx for usize {
    /// Identity function: returns `idx` unchanged.
    ///
    /// # Verified Property
    /// `result == idx` (identity)
    #[cfg_attr(trust_verify, ensures("result == idx"))]
    #[inline]
    fn new(idx: usize) -> Self {
        idx
    }

    /// Identity function: returns `self` unchanged.
    ///
    /// # Verified Property
    /// `result == self` (identity)
    #[cfg_attr(trust_verify, ensures("result == self"))]
    #[inline]
    fn index(self) -> usize {
        self
    }
}

/// Implementation of `Idx` for `u32`.
///
/// This implementation enforces that the index fits in a `u32`.
/// Uses runtime assertion for bounds checking.
impl Idx for u32 {
    /// Creates a u32 index from usize.
    ///
    /// # Verified Properties
    /// - Precondition: `idx <= u32::MAX as usize`
    /// - Postcondition: `result as usize == idx`
    ///
    /// # Panics
    /// Panics if `idx > u32::MAX as usize`.
    #[cfg_attr(trust_verify, requires("idx <= 4294967295"))]
    #[cfg_attr(trust_verify, ensures("result as usize == idx"))]
    #[inline]
    fn new(idx: usize) -> Self {
        assert!(idx <= u32::MAX as usize);
        idx as u32
    }

    /// Returns the underlying index as usize.
    ///
    /// # Verified Property
    /// `result == self as usize` (lossless widening)
    #[cfg_attr(trust_verify, ensures("result == self as usize"))]
    #[inline]
    fn index(self) -> usize {
        self as usize
    }
}

// ============================================================================
// IntoSliceIdx - Conversion trait for IndexSlice range indexing
// ============================================================================

/// Converts a typed index or range into a slice index.
///
/// This trait enables range-based indexing on `IndexSlice`, allowing
/// expressions like `slice[start..end]` with typed indices.
pub trait IntoSliceIdx<I, T: ?Sized> {
    type Output: SliceIndex<T>;
    fn into_slice_idx(self) -> Self::Output;
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for I {
    type Output = usize;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        self.index()
    }
}

impl<I, T> IntoSliceIdx<I, [T]> for ops::RangeFull {
    type Output = ops::RangeFull;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        self
    }
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for ops::Range<I> {
    type Output = ops::Range<usize>;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        ops::Range {
            start: self.start.index(),
            end: self.end.index(),
        }
    }
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for ops::RangeFrom<I> {
    type Output = ops::RangeFrom<usize>;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        ops::RangeFrom {
            start: self.start.index(),
        }
    }
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for ops::RangeTo<I> {
    type Output = ops::RangeTo<usize>;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        ..self.end.index()
    }
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for ops::RangeInclusive<I> {
    type Output = ops::RangeInclusive<usize>;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        ops::RangeInclusive::new(self.start().index(), self.end().index())
    }
}

impl<I: Idx, T> IntoSliceIdx<I, [T]> for ops::RangeToInclusive<I> {
    type Output = ops::RangeToInclusive<usize>;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        ..=self.end.index()
    }
}

#[cfg(feature = "nightly")]
impl<I: Idx, T> IntoSliceIdx<I, [T]> for core::range::Range<I> {
    type Output = core::range::Range<usize>;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        core::range::Range {
            start: self.start.index(),
            end: self.end.index(),
        }
    }
}

#[cfg(feature = "nightly")]
impl<I: Idx, T> IntoSliceIdx<I, [T]> for core::range::RangeFrom<I> {
    type Output = core::range::RangeFrom<usize>;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        core::range::RangeFrom {
            start: self.start.index(),
        }
    }
}

#[cfg(feature = "nightly")]
impl<I: Idx, T> IntoSliceIdx<I, [T]> for core::range::RangeInclusive<I> {
    type Output = core::range::RangeInclusive<usize>;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        core::range::RangeInclusive {
            start: self.start.index(),
            last: self.last.index(),
        }
    }
}

#[cfg(feature = "nightly")]
impl<I: Idx, T> IntoSliceIdx<I, [T]> for core::range::RangeToInclusive<I> {
    type Output = core::range::RangeToInclusive<usize>;
    #[inline]
    fn into_slice_idx(self) -> Self::Output {
        core::range::RangeToInclusive {
            last: self.last.index(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_usize_idx_roundtrip() {
        let idx: usize = 42;
        let created = usize::new(idx);
        assert_eq!(Idx::index(created), idx);
    }

    #[test]
    fn test_u32_idx_roundtrip() {
        let idx: usize = 42;
        let created = u32::new(idx);
        assert_eq!(Idx::index(created), idx);
    }

    #[test]
    fn test_u32_idx_max() {
        let idx = u32::MAX as usize;
        let created = u32::new(idx);
        assert_eq!(Idx::index(created), idx);
    }

    #[test]
    #[should_panic(expected = "assertion failed: idx <= u32::MAX as usize")]
    fn test_u32_idx_overflow() {
        let idx = (u32::MAX as usize) + 1;
        let _ = u32::new(idx); // Should panic
    }

    #[test]
    fn test_plus() {
        let idx = u32::new(10);
        let incremented = idx.plus(5);
        assert_eq!(Idx::index(incremented), 15);
    }

    #[test]
    fn test_increment_by() {
        let mut idx = u32::new(10);
        idx.increment_by(5);
        assert_eq!(Idx::index(idx), 15);
    }
}
