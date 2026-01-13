//! IndexSlice - A view into contiguous `T`s, indexed by `I` rather than `usize`.
//!
//! This module provides a slice wrapper that enforces type-safe indexing.
//!
//! ## Verification Targets
//!
//! - Construction: `from_raw`, `from_raw_mut`, `empty`
//! - Access: `get`, `get_mut`, Index/IndexMut
//! - Query: `len`, `is_empty`, `next_index`, `last_index`
//! - Iteration: `iter`, `iter_mut`, `iter_enumerated`

use std::fmt;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut, RangeBounds};
use std::slice::GetDisjointMutError::*;
use std::slice::{self, SliceIndex};

// Note: #[requires] and #[ensures] are trustc built-in attributes.
// They use cfg_attr(trust_verify, ...) for cargo test compatibility.

use crate::{Idx, IndexVec, IntoSliceIdx};

/// A view into contiguous `T`s, indexed by `I` rather than by `usize`.
///
/// One common pattern you'll see is code that uses [`IndexVec::from_elem`]
/// to create the storage needed for a particular "universe" (aka the set of all
/// the possible keys that need an associated value) then passes that working
/// area as `&mut IndexSlice<I, T>` to clarify that nothing will be added nor
/// removed during processing (and, as a bonus, to chase fewer pointers).
///
/// ## Key Invariant
///
/// The `raw` field always reflects the true length and contents.
/// All operations preserve this invariant.
#[derive(PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct IndexSlice<I: Idx, T> {
    _marker: PhantomData<fn(&I)>,
    pub raw: [T],
}

impl<I: Idx, T> IndexSlice<I, T> {
    /// Returns an empty slice.
    ///
    /// # Verified Property (const fn - spec in doc)
    /// `result.len() == 0`
    #[inline]
    pub const fn empty<'a>() -> &'a Self {
        Self::from_raw(&[])
    }

    /// Creates a slice view from a raw slice.
    ///
    /// # Verified Property (const fn - spec in doc)
    /// `result.len() == raw.len()`
    ///
    /// # Safety Note
    /// Uses pointer cast, safe due to `repr(transparent)`.
    #[inline]
    pub const fn from_raw(raw: &[T]) -> &Self {
        let ptr: *const [T] = raw;
        // SAFETY: `IndexSlice` is `repr(transparent)` over a normal slice
        unsafe { &*(ptr as *const Self) }
    }

    /// Creates a mutable slice view from a raw slice.
    ///
    /// # Verified Property
    /// `result.len() == raw.len()`
    // SOLVER_LIMIT: L7 - result.raw through mutable reference not resolvable
    #[inline]
    pub fn from_raw_mut(raw: &mut [T]) -> &mut Self {
        let ptr: *mut [T] = raw;
        // SAFETY: `IndexSlice` is `repr(transparent)` over a normal slice
        unsafe { &mut *(ptr as *mut Self) }
    }

    /// Returns the number of elements in the slice.
    ///
    /// # Verified Property (const fn - spec in doc)
    /// `result == self.raw.len()`
    #[cfg_attr(trust_verify, pure)]
    #[inline]
    pub const fn len(&self) -> usize {
        self.raw.len()
    }

    /// Returns true if the slice contains no elements.
    ///
    /// # Verified Property (const fn - spec in doc)
    /// `result == (self.len() == 0)`
    #[cfg_attr(trust_verify, pure)]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    /// Gives the next index that will be assigned when `push` is called.
    ///
    /// Manual bounds checks can be done using `idx < slice.next_index()`
    /// (as opposed to `idx.index() < slice.len()`).
    ///
    /// # Verified Property
    /// `result.index() == self.len()`
    // SOLVER_LIMIT: L10 - trait method identity I::new(n).index() == n not provable for generic I
    #[cfg_attr(trust_verify, pure)]
    #[inline]
    pub fn next_index(&self) -> I {
        I::new(self.len())
    }

    /// Returns an iterator over the slice.
    ///
    /// # Note
    /// Yields exactly `self.len()` elements.
    #[inline]
    pub fn iter(&self) -> slice::Iter<'_, T> {
        self.raw.iter()
    }

    /// Returns an iterator that yields (index, value) pairs.
    ///
    /// # Note
    /// Yields exactly `self.len()` pairs with indices matching positions.
    #[inline]
    pub fn iter_enumerated(&self) -> impl DoubleEndedIterator<Item = (I, &T)> + ExactSizeIterator {
        // Allow the optimizer to elide the bounds checking when creating each index.
        let _ = I::new(self.len());
        self.raw.iter().enumerate().map(|(n, t)| (I::new(n), t))
    }

    /// Returns an iterator over all valid indices.
    ///
    /// # Note
    /// Yields exactly `self.len()` indices, each equal to its position.
    #[inline]
    pub fn indices(
        &self,
    ) -> impl DoubleEndedIterator<Item = I> + ExactSizeIterator + Clone + 'static {
        // Allow the optimizer to elide the bounds checking when creating each index.
        let _ = I::new(self.len());
        (0..self.len()).map(|n| I::new(n))
    }

    /// Returns a mutable iterator over the slice.
    ///
    /// # Note
    /// Yields exactly `self.len()` elements.
    #[inline]
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, T> {
        self.raw.iter_mut()
    }

    /// Returns a mutable iterator that yields (index, value) pairs.
    ///
    /// # Note
    /// Yields exactly `self.len()` pairs with indices matching positions.
    #[inline]
    pub fn iter_enumerated_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = (I, &mut T)> + ExactSizeIterator {
        // Allow the optimizer to elide the bounds checking when creating each index.
        let _ = I::new(self.len());
        self.raw.iter_mut().enumerate().map(|(n, t)| (I::new(n), t))
    }

    /// Returns the last valid index, or None if empty.
    ///
    /// # Verified Properties
    /// - `result.is_some() == (self.len() > 0)`
    ///
    /// Note: This postcondition avoids any dependence on `I::new(..)`/`I::index()`
    /// semantics (which are not available for generic `I`) and only states the
    /// Option-shape relationship to `len()`.
    #[cfg_attr(trust_verify, ensures("result.is_some() == (self.len() > 0)"))]
    #[inline]
    pub fn last_index(&self) -> Option<I> {
        let len = self.len();
        if len == 0 {
            None
        } else {
            Some(I::new(len - 1))
        }
    }

    /// Swaps two elements in the slice.
    ///
    /// # Verified Properties
    /// - Precondition: `a.index() < self.len() && b.index() < self.len()`
    #[cfg_attr(
        trust_verify,
        requires("a.index() < self.raw.len() && b.index() < self.raw.len()")
    )]
    #[inline]
    pub fn swap(&mut self, a: I, b: I) {
        self.raw.swap(a.index(), b.index())
    }

    /// Copies elements from one part of the slice to another part within the same slice.
    ///
    /// `src` is the range within the slice to copy from. `dest` is the starting index
    /// of the destination range.
    ///
    /// # Panics
    /// Panics if `src` is out of bounds or if `dest + src.len()` is out of bounds.
    #[inline]
    pub fn copy_within(
        &mut self,
        src: impl IntoSliceIdx<I, [T], Output: RangeBounds<usize>>,
        dest: I,
    ) where
        T: Copy,
    {
        self.raw.copy_within(src.into_slice_idx(), dest.index());
    }

    /// Returns a reference to an element or subslice, or None if out of bounds.
    ///
    /// # Verified Properties
    /// - `index.index() < self.len() => result.is_some()` (for single index)
    /// - `index.index() >= self.len() => result.is_none()` (for single index)
    // SOLVER_LIMIT: Vec::get semantics not tracked by solver
    // Note: result.is_some() is supported now (L3 fixed), but slice/Vec::get semantics
    // (returns Some when in bounds) aren't modeled by the verifier
    #[inline]
    pub fn get<R: IntoSliceIdx<I, [T]>>(
        &self,
        index: R,
    ) -> Option<&<R::Output as SliceIndex<[T]>>::Output> {
        self.raw.get(index.into_slice_idx())
    }

    /// Returns a mutable reference to an element or subslice, or None if out of bounds.
    ///
    /// # Verified Properties
    /// - `index.index() < self.len() => result.is_some()` (for single index)
    /// - `index.index() >= self.len() => result.is_none()` (for single index)
    // SOLVER_LIMIT: Vec::get_mut semantics not tracked by solver
    // Note: result.is_some() is supported now (L3 fixed), but slice/Vec::get_mut semantics
    // (returns Some when in bounds) aren't modeled by the verifier
    #[inline]
    pub fn get_mut<R: IntoSliceIdx<I, [T]>>(
        &mut self,
        index: R,
    ) -> Option<&mut <R::Output as SliceIndex<[T]>>::Output> {
        self.raw.get_mut(index.into_slice_idx())
    }

    /// Returns mutable references to two distinct elements, `a` and `b`.
    ///
    /// # Verified Properties
    /// - Precondition: `a.index() != b.index()`
    /// - Precondition: `a.index() < self.len() && b.index() < self.len()`
    ///
    /// # Panics
    /// Panics if `a == b`.
    #[cfg_attr(trust_verify, requires("a.index() != b.index()"))]
    #[cfg_attr(
        trust_verify,
        requires("a.index() < self.raw.len() && b.index() < self.raw.len()")
    )]
    #[inline]
    pub fn pick2_mut(&mut self, a: I, b: I) -> (&mut T, &mut T) {
        let (ai, bi) = (a.index(), b.index());
        match self.raw.get_disjoint_mut([ai, bi]) {
            Ok([a, b]) => (a, b),
            Err(OverlappingIndices) => panic!("Indices {ai:?} and {bi:?} are not disjoint!"),
            Err(IndexOutOfBounds) => {
                panic!("Some indices among ({ai:?}, {bi:?}) are out of bounds")
            }
        }
    }

    /// Returns mutable references to three distinct elements.
    ///
    /// # Verified Properties
    /// - Precondition: all indices are distinct
    /// - Precondition: all indices are in bounds
    ///
    /// # Panics
    /// Panics if the elements are not distinct.
    #[cfg_attr(
        trust_verify,
        requires("a.index() != b.index() && b.index() != c.index() && c.index() != a.index()")
    )]
    #[cfg_attr(
        trust_verify,
        requires("a.index() < self.raw.len() && b.index() < self.raw.len() && c.index() < self.raw.len()")
    )]
    #[inline]
    pub fn pick3_mut(&mut self, a: I, b: I, c: I) -> (&mut T, &mut T, &mut T) {
        let (ai, bi, ci) = (a.index(), b.index(), c.index());

        match self.raw.get_disjoint_mut([ai, bi, ci]) {
            Ok([a, b, c]) => (a, b, c),
            Err(OverlappingIndices) => {
                panic!("Indices {ai:?}, {bi:?} and {ci:?} are not disjoint!")
            }
            Err(IndexOutOfBounds) => {
                panic!("Some indices among ({ai:?}, {bi:?}, {ci:?}) are out of bounds")
            }
        }
    }

    /// Binary search for a value.
    ///
    /// # Note
    /// `result.is_ok() => self[result.unwrap()].eq(value)`
    #[cfg_attr(trust_verify, pure)]
    #[inline]
    pub fn binary_search(&self, value: &T) -> Result<I, I>
    where
        T: Ord,
    {
        match self.raw.binary_search(value) {
            Ok(i) => Ok(Idx::new(i)),
            Err(i) => Err(Idx::new(i)),
        }
    }
}

impl<I: Idx, J: Idx> IndexSlice<I, J> {
    /// Invert a bijective mapping, i.e. `invert(map)[y] = x` if `map[x] = y`,
    /// assuming the values in `self` are a permutation of `0..self.len()`.
    ///
    /// # Verified Property
    /// `result.len() == self.len()`
    ///
    /// # Precondition (runtime checked)
    /// `self` must be a permutation of `0..self.len()`
    // FIXME(eddyb) build a better abstraction for permutations, if possible.
    #[cfg_attr(trust_verify, ensures("result.raw.len() == self.raw.len()"))]
    pub fn invert_bijective_mapping(&self) -> IndexVec<J, I> {
        debug_assert_eq!(
            self.iter().map(|x| x.index() as u128).sum::<u128>(),
            (0..self.len() as u128).sum::<u128>(),
            "The values aren't 0..N in input {self:?}",
        );

        let mut inverse = IndexVec::from_elem_n(Idx::new(0), self.len());
        for (i1, &i2) in self.iter_enumerated() {
            inverse[i2] = i1;
        }

        debug_assert_eq!(
            inverse.iter().map(|x| x.index() as u128).sum::<u128>(),
            (0..inverse.len() as u128).sum::<u128>(),
            "The values aren't 0..N in result {self:?}",
        );

        inverse
    }
}

impl<I: Idx, T: fmt::Debug> fmt::Debug for IndexSlice<I, T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.raw, fmt)
    }
}

impl<I: Idx, T, R: IntoSliceIdx<I, [T]>> Index<R> for IndexSlice<I, T> {
    type Output = <R::Output as SliceIndex<[T]>>::Output;

    /// Index into the slice using a typed index or range.
    ///
    /// # Panics
    /// Panics if index is out of bounds.
    #[inline]
    fn index(&self, index: R) -> &Self::Output {
        &self.raw[index.into_slice_idx()]
    }
}

impl<I: Idx, T, R: IntoSliceIdx<I, [T]>> IndexMut<R> for IndexSlice<I, T> {
    /// Mutably index into the slice using a typed index or range.
    ///
    /// # Panics
    /// Panics if index is out of bounds.
    #[inline]
    fn index_mut(&mut self, index: R) -> &mut Self::Output {
        &mut self.raw[index.into_slice_idx()]
    }
}

impl<'a, I: Idx, T> IntoIterator for &'a IndexSlice<I, T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> slice::Iter<'a, T> {
        self.raw.iter()
    }
}

impl<'a, I: Idx, T> IntoIterator for &'a mut IndexSlice<I, T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> slice::IterMut<'a, T> {
        self.raw.iter_mut()
    }
}

impl<I: Idx, T: Clone> ToOwned for IndexSlice<I, T> {
    type Owned = IndexVec<I, T>;

    fn to_owned(&self) -> IndexVec<I, T> {
        IndexVec::from_raw(self.raw.to_owned())
    }

    fn clone_into(&self, target: &mut IndexVec<I, T>) {
        self.raw.clone_into(&mut target.raw)
    }
}

impl<I: Idx, T> Default for &IndexSlice<I, T> {
    #[inline]
    fn default() -> Self {
        IndexSlice::from_raw(Default::default())
    }
}

impl<I: Idx, T> Default for &mut IndexSlice<I, T> {
    #[inline]
    fn default() -> Self {
        IndexSlice::from_raw_mut(Default::default())
    }
}

// SAFETY: `IndexSlice` is `Send` if `T` is `Send` because:
// - The only data is `raw: [T]` which is `Send` when `T: Send`
// - `PhantomData<fn(&I)>` is covariant in `I` and has no runtime data
// - No interior mutability or thread-unsafe access patterns exist
unsafe impl<I: Idx, T> Send for IndexSlice<I, T> where T: Send {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slice_from_raw() {
        let arr = [1, 2, 3, 4, 5];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        assert_eq!(slice.len(), 5);
        assert_eq!(slice[0usize], 1);
        assert_eq!(slice[4usize], 5);
    }

    #[test]
    fn test_slice_empty() {
        let slice: &IndexSlice<usize, i32> = IndexSlice::empty();
        assert!(slice.is_empty());
        assert_eq!(slice.len(), 0);
    }

    #[test]
    fn test_slice_next_index() {
        let arr = [1, 2, 3];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        assert_eq!(slice.next_index(), 3usize);
    }

    #[test]
    fn test_slice_last_index() {
        let arr = [1, 2, 3];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        assert_eq!(slice.last_index(), Some(2usize));

        let empty: &IndexSlice<usize, i32> = IndexSlice::empty();
        assert_eq!(empty.last_index(), None);
    }

    #[test]
    fn test_slice_get() {
        let arr = [1, 2, 3];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        assert_eq!(slice.get(1usize), Some(&2));
        assert_eq!(slice.get(10usize), None);
    }

    #[test]
    fn test_slice_iter_enumerated() {
        let arr = [10, 20, 30];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        let pairs: Vec<_> = slice.iter_enumerated().collect();
        assert_eq!(pairs, vec![(0usize, &10), (1usize, &20), (2usize, &30)]);
    }

    // ========================================================================
    // IntoSliceIdx / Range indexing tests (1.88.0 upgrade)
    // ========================================================================

    #[test]
    fn test_slice_index_single() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        assert_eq!(slice[2usize], 30);
    }

    #[test]
    fn test_slice_index_range() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        let sub: &[i32] = &slice[1usize..4usize];
        assert_eq!(sub, &[20, 30, 40]);
    }

    #[test]
    fn test_slice_index_range_from() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        let sub: &[i32] = &slice[2usize..];
        assert_eq!(sub, &[30, 40, 50]);
    }

    #[test]
    fn test_slice_index_range_to() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        let sub: &[i32] = &slice[..3usize];
        assert_eq!(sub, &[10, 20, 30]);
    }

    #[test]
    fn test_slice_index_range_full() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        let sub: &[i32] = &slice[..];
        assert_eq!(sub, &[10, 20, 30, 40, 50]);
    }

    #[test]
    fn test_slice_index_with_u32_idx() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<u32, i32> = IndexSlice::from_raw(&arr);
        assert_eq!(slice[u32::new(2)], 30);
        let sub: &[i32] = &slice[u32::new(1)..u32::new(4)];
        assert_eq!(sub, &[20, 30, 40]);
    }

    // IntoSliceIdx inclusive range tests (1.88.0 upgrade - Phase 7.4)

    #[test]
    fn test_slice_index_range_inclusive() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        let sub: &[i32] = &slice[1usize..=3usize];
        assert_eq!(sub, &[20, 30, 40]);
    }

    #[test]
    fn test_slice_index_range_to_inclusive() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        let sub: &[i32] = &slice[..=2usize];
        assert_eq!(sub, &[10, 20, 30]);
    }

    #[test]
    fn test_slice_index_range_inclusive_single() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        let sub: &[i32] = &slice[2usize..=2usize];
        assert_eq!(sub, &[30]);
    }

    #[test]
    fn test_slice_index_range_inclusive_mut() {
        let mut arr = [10, 20, 30, 40, 50];
        let slice: &mut IndexSlice<usize, i32> = IndexSlice::from_raw_mut(&mut arr);
        let sub: &mut [i32] = &mut slice[1usize..=3usize];
        sub[0] = 200;
        sub[2] = 400;
        assert_eq!(arr, [10, 200, 30, 400, 50]);
    }

    #[test]
    fn test_slice_index_range_to_inclusive_mut() {
        let mut arr = [10, 20, 30, 40, 50];
        let slice: &mut IndexSlice<usize, i32> = IndexSlice::from_raw_mut(&mut arr);
        let sub: &mut [i32] = &mut slice[..=1usize];
        sub[0] = 100;
        sub[1] = 200;
        assert_eq!(arr, [100, 200, 30, 40, 50]);
    }

    #[test]
    fn test_slice_index_range_inclusive_u32() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<u32, i32> = IndexSlice::from_raw(&arr);
        let sub: &[i32] = &slice[u32::new(1)..=u32::new(3)];
        assert_eq!(sub, &[20, 30, 40]);
    }

    // ========================================================================
    // copy_within tests (1.94.0 upgrade)
    // ========================================================================

    #[test]
    fn test_copy_within_basic() {
        let mut arr = [1, 2, 3, 4, 5];
        let slice: &mut IndexSlice<usize, i32> = IndexSlice::from_raw_mut(&mut arr);
        slice.copy_within(0usize..3usize, 2usize);
        assert_eq!(arr, [1, 2, 1, 2, 3]);
    }

    #[test]
    fn test_copy_within_overlap_forward() {
        let mut arr = [1, 2, 3, 4, 5];
        let slice: &mut IndexSlice<usize, i32> = IndexSlice::from_raw_mut(&mut arr);
        slice.copy_within(1usize..4usize, 2usize);
        assert_eq!(arr, [1, 2, 2, 3, 4]);
    }

    #[test]
    fn test_copy_within_overlap_backward() {
        let mut arr = [1, 2, 3, 4, 5];
        let slice: &mut IndexSlice<usize, i32> = IndexSlice::from_raw_mut(&mut arr);
        slice.copy_within(2usize..5usize, 0usize);
        assert_eq!(arr, [3, 4, 5, 4, 5]);
    }

    #[test]
    fn test_copy_within_empty_range() {
        let mut arr = [1, 2, 3, 4, 5];
        let original = arr;
        let slice: &mut IndexSlice<usize, i32> = IndexSlice::from_raw_mut(&mut arr);
        slice.copy_within(2usize..2usize, 0usize); // Empty range
        assert_eq!(arr, original);
    }

    // ========================================================================
    // Generic get/get_mut tests (1.94.0 upgrade)
    // ========================================================================

    #[test]
    fn test_get_range() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        let sub = slice.get(1usize..4usize);
        assert_eq!(sub, Some(&[20, 30, 40][..]));
    }

    #[test]
    fn test_get_range_out_of_bounds() {
        let arr = [10, 20, 30, 40, 50];
        let slice: &IndexSlice<usize, i32> = IndexSlice::from_raw(&arr);
        let sub = slice.get(3usize..10usize);
        assert!(sub.is_none());
    }

    #[test]
    fn test_get_mut_range() {
        let mut arr = [10, 20, 30, 40, 50];
        let slice: &mut IndexSlice<usize, i32> = IndexSlice::from_raw_mut(&mut arr);
        if let Some(sub) = slice.get_mut(1usize..3usize) {
            sub[0] = 200;
            sub[1] = 300;
        }
        assert_eq!(arr, [10, 200, 300, 40, 50]);
    }
}
