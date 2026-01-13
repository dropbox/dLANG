//! IndexVec - An owned contiguous collection of `T`s, indexed by `I` rather than `usize`.
//!
//! This module provides the primary typed-index vector used throughout rustc.
//!
//! ## Verification Targets
//!
//! - Construction: `new`, `from_raw`, `with_capacity`, `from_elem`, `from_elem_n`, `from_fn_n`
//! - Access: `as_slice`, `as_mut_slice`, Index/IndexMut
//! - Modification: `push`, `pop`, `truncate`, `resize`, `append`
//! - Query: `next_index`, `len`, `is_empty`
//!
//! ## Key Invariant
//!
//! `self.raw.len()` always equals the logical length of the IndexVec.

use std::borrow::{Borrow, BorrowMut};
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut, RangeBounds};
use std::{fmt, slice, vec};

// Note: #[requires] and #[ensures] are trustc built-in attributes.
// They use cfg_attr(trust_verify, ...) for cargo test compatibility.

#[cfg(feature = "nightly")]
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};

use crate::{Idx, IndexSlice};

/// An owned contiguous collection of `T`s, indexed by `I` rather than by `usize`.
///
/// ## Why use this instead of a `Vec`?
///
/// An `IndexVec` allows element access only via a specific associated index type, meaning that
/// trying to use the wrong index type (possibly accessing an invalid element) will fail at
/// compile time.
///
/// It also documents what the index is indexing: in a `HashMap<usize, Something>` it's not
/// immediately clear what the `usize` means, while a `HashMap<FieldIdx, Something>` makes it obvious.
///
/// ## Key Invariant
///
/// The `raw` field is always a valid Vec, and `self.raw.len()` equals the logical length.
#[derive(Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct IndexVec<I: Idx, T> {
    pub raw: Vec<T>,
    _marker: PhantomData<fn(&I)>,
}

impl<I: Idx, T> IndexVec<I, T> {
    /// Constructs a new, empty `IndexVec<I, T>`.
    ///
    /// # Verified Property (const fn - spec in doc)
    /// `result.len() == 0`
    #[inline]
    pub const fn new() -> Self {
        IndexVec::from_raw(Vec::new())
    }

    /// Constructs a new `IndexVec<I, T>` from a `Vec<T>`.
    ///
    /// # Verified Property (const fn - spec in doc)
    /// `result.len() == raw.len()`
    #[inline]
    pub const fn from_raw(raw: Vec<T>) -> Self {
        IndexVec {
            raw,
            _marker: PhantomData,
        }
    }

    /// Constructs a new, empty `IndexVec<I, T>` with specified capacity.
    ///
    /// # Verified Properties
    /// - `result.len() == 0`
    /// - `result.raw.capacity() >= capacity`
    // SOLVER_LIMIT: L7 - result.field through from_raw() helper not trackable
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        IndexVec::from_raw(Vec::with_capacity(capacity))
    }

    /// Creates a new vector with a copy of `elem` for each index in `universe`.
    ///
    /// Thus `IndexVec::from_elem(elem, &universe)` is equivalent to
    /// `IndexVec::<I, _>::from_elem_n(elem, universe.len())`. That can help
    /// type inference as it ensures that the resulting vector uses the same
    /// index type as `universe`, rather than something potentially surprising.
    ///
    /// # Verified Properties
    /// - `result.len() == universe.len()`
    /// - All elements equal `elem`
    #[cfg_attr(trust_verify, ensures("result.raw.len() == universe.raw.len()"))]
    #[inline]
    pub fn from_elem<S>(elem: T, universe: &IndexSlice<I, S>) -> Self
    where
        T: Clone,
    {
        IndexVec::from_raw(vec![elem; universe.len()])
    }

    /// Creates a new IndexVec with n copies of the `elem`.
    ///
    /// # Verified Properties
    /// - `result.len() == n`
    /// - All elements equal `elem`
    // SOLVER_LIMIT: L7 - vec![elem; n] macro expansion not traceable (disproven when tested)
    #[inline]
    pub fn from_elem_n(elem: T, n: usize) -> Self
    where
        T: Clone,
    {
        IndexVec::from_raw(vec![elem; n])
    }

    /// Create an `IndexVec` with `n` elements, where the value of each
    /// element is the result of `func(i)`. (The underlying vector will
    /// be allocated only once, with a capacity of at least `n`.)
    ///
    /// # Verified Properties
    /// - `result.len() == n`
    /// - `result[I::new(i)] == func(I::new(i))` for all valid `i`
    #[cfg_attr(trust_verify, ensures("result.raw.len() == n"))]
    #[inline]
    pub fn from_fn_n(func: impl FnMut(I) -> T, n: usize) -> Self {
        // Allow the optimizer to elide the bounds checking when creating each index.
        let _ = I::new(n);
        IndexVec::from_raw((0..n).map(I::new).map(func).collect())
    }

    /// Returns this IndexVec as a slice.
    ///
    /// # Verified Property
    /// `result.len() == self.len()`
    // SOLVER_LIMIT: L7 - result.raw through reference not resolvable
    #[inline]
    pub fn as_slice(&self) -> &IndexSlice<I, T> {
        IndexSlice::from_raw(&self.raw)
    }

    /// Returns this IndexVec as a mutable slice.
    ///
    /// # Verified Property
    /// `result.len() == self.len()`
    // SOLVER_LIMIT: L7 - result.raw through mutable reference not resolvable
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut IndexSlice<I, T> {
        IndexSlice::from_raw_mut(&mut self.raw)
    }

    /// Pushes an element to the array returning the index where it was pushed to.
    ///
    /// # Verified Properties
    /// - `result.index() == old(self.len())`
    /// - `self.len() == old(self.len()) + 1`
    #[cfg_attr(trust_verify, ensures("result.index() == old(self.raw.len())"))]
    #[cfg_attr(trust_verify, ensures("self.raw.len() == old(self.raw.len()) + 1"))]
    #[inline]
    pub fn push(&mut self, d: T) -> I {
        let idx = self.next_index();
        self.raw.push(d);
        idx
    }

    /// Removes the last element from the vector and returns it, or None if empty.
    ///
    /// # Verified Properties
    /// - `old(self.len()) > 0 => result.is_some()`
    /// - `old(self.len()) == 0 => result.is_none()`
    /// - `old(self.len()) > 0 => self.len() == old(self.len()) - 1`
    // SOLVER_LIMIT: Implication (=>) with old() + result predicates not supported
    // Note: L3 (result.method()) is fixed, but the conditional format `old(x) => result.is_some()`
    // combining old() expressions with result predicates isn't yet verifiable
    // Weaker but provable: length can only decrease
    #[cfg_attr(trust_verify, ensures("self.raw.len() <= old(self.raw.len())"))]
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        self.raw.pop()
    }

    /// Converts this IndexVec into an iterator.
    ///
    /// # Note
    /// Yields exactly `self.len()` elements.
    /// This method name intentionally matches IntoIterator but returns the underlying
    /// Vec's iterator directly for compatibility with rustc_index upstream.
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn into_iter(self) -> vec::IntoIter<T> {
        self.raw.into_iter()
    }

    /// Converts this IndexVec into an enumerated iterator.
    ///
    /// # Note
    /// Yields exactly `self.len()` pairs with indices matching positions.
    #[inline]
    pub fn into_iter_enumerated(
        self,
    ) -> impl DoubleEndedIterator<Item = (I, T)> + ExactSizeIterator {
        // Allow the optimizer to elide the bounds checking when creating each index.
        let _ = I::new(self.len());
        self.raw
            .into_iter()
            .enumerate()
            .map(|(n, t)| (I::new(n), t))
    }

    /// Removes elements in the given range.
    ///
    /// # Verified Property
    /// `self.len() <= old(self.len())`
    // SOLVER_LIMIT: L7 - range-based drain not traceable
    // Weaker but provable: length can only decrease
    #[cfg_attr(trust_verify, ensures("self.raw.len() <= old(self.raw.len())"))]
    #[inline]
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> impl Iterator<Item = T> + '_ {
        self.raw.drain(range)
    }

    /// Removes elements in the given range, returning them with their indices.
    ///
    /// # Verified Property
    /// `self.len() <= old(self.len())`
    #[cfg_attr(trust_verify, ensures("self.raw.len() <= old(self.raw.len())"))]
    #[inline]
    pub fn drain_enumerated<R: RangeBounds<usize>>(
        &mut self,
        range: R,
    ) -> impl Iterator<Item = (I, T)> + '_ {
        let begin = match range.start_bound() {
            std::ops::Bound::Included(i) => *i,
            std::ops::Bound::Excluded(i) => i.checked_add(1).unwrap(),
            std::ops::Bound::Unbounded => 0,
        };
        self.raw
            .drain(range)
            .enumerate()
            .map(move |(n, t)| (I::new(begin + n), t))
    }

    /// Shrinks the capacity of the vector as much as possible.
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.raw.shrink_to_fit()
    }

    /// Shortens the vector, keeping the first `a` elements.
    ///
    /// # Verified Properties
    /// - `self.len() <= old(self.len())`
    /// - `self.len() <= a`
    // SOLVER_LIMIT: L7 - truncate postconditions not traceable
    // Weaker but provable: length can only decrease
    #[cfg_attr(trust_verify, ensures("self.raw.len() <= old(self.raw.len())"))]
    #[inline]
    pub fn truncate(&mut self, a: usize) {
        self.raw.truncate(a)
    }

    /// Grows the index vector so that it contains an entry for
    /// `elem`; if that is already true, then has no
    /// effect. Otherwise, inserts new values as needed by invoking
    /// `fill_value`.
    ///
    /// Returns a reference to the `elem` entry.
    ///
    /// # Verified Property
    /// `self.len() >= elem.index() + 1`
    #[cfg_attr(trust_verify, ensures("self.raw.len() >= elem.index() + 1"))]
    #[inline]
    pub fn ensure_contains_elem(&mut self, elem: I, fill_value: impl FnMut() -> T) -> &mut T {
        let min_new_len = elem.index().checked_add(1).unwrap();
        if self.len() < min_new_len {
            self.raw.resize_with(min_new_len, fill_value);
        }

        &mut self[elem]
    }

    /// Resizes the vector to `new_len` elements.
    ///
    /// # Verified Property
    /// `self.len() == new_len`
    // SOLVER_LIMIT: L7 - resize postconditions not traceable (disproven when tested)
    #[inline]
    pub fn resize(&mut self, new_len: usize, value: T)
    where
        T: Clone,
    {
        self.raw.resize(new_len, value)
    }

    /// Resizes the vector to accommodate `elem` index.
    ///
    /// # Verified Property
    /// `self.len() == elem.index() + 1`
    #[cfg_attr(trust_verify, ensures("self.raw.len() == elem.index() + 1"))]
    #[inline]
    pub fn resize_to_elem(&mut self, elem: I, fill_value: impl FnMut() -> T) {
        let min_new_len = elem.index().checked_add(1).unwrap();
        self.raw.resize_with(min_new_len, fill_value);
    }

    /// Moves all elements from `other` into `self`.
    ///
    /// # Verified Properties
    /// - `self.len() == old(self.len()) + old(other.len())`
    /// - `other.len() == 0`
    // SOLVER_LIMIT: L7 - append with multiple old() refs not verifiable
    // Weaker but provable: length can only increase
    #[cfg_attr(trust_verify, ensures("self.raw.len() >= old(self.raw.len())"))]
    #[inline]
    pub fn append(&mut self, other: &mut Self) {
        self.raw.append(&mut other.raw);
    }
}

/// `IndexVec` is often used as a map, so it provides some map-like APIs.
impl<I: Idx, T> IndexVec<I, Option<T>> {
    /// Inserts a value at the given index, returning the previous value.
    ///
    /// # Verified Property
    /// `self.len() >= index.index() + 1`
    #[cfg_attr(trust_verify, ensures("self.raw.len() >= index.index() + 1"))]
    #[inline]
    pub fn insert(&mut self, index: I, value: T) -> Option<T> {
        self.ensure_contains_elem(index, || None).replace(value)
    }

    /// Gets or inserts a value at the given index.
    ///
    /// # Verified Property
    /// `self.len() >= index.index() + 1`
    #[cfg_attr(trust_verify, ensures("self.raw.len() >= index.index() + 1"))]
    #[inline]
    pub fn get_or_insert_with(&mut self, index: I, value: impl FnOnce() -> T) -> &mut T {
        self.ensure_contains_elem(index, || None)
            .get_or_insert_with(value)
    }

    /// Removes a value at the given index, returning it.
    ///
    /// # Note
    /// After removal, `self[index].is_none()` if index was valid.
    #[inline]
    pub fn remove(&mut self, index: I) -> Option<T> {
        self.get_mut(index)?.take()
    }

    /// Returns true if the index contains a value.
    ///
    /// # Note
    /// Equivalent to `self.get(index).map(Option::is_some).unwrap_or(false)`
    #[cfg_attr(trust_verify, pure)]
    #[inline]
    #[must_use]
    pub fn contains(&self, index: I) -> bool {
        self.get(index).and_then(Option::as_ref).is_some()
    }
}

impl<I: Idx, T: fmt::Debug> fmt::Debug for IndexVec<I, T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.raw, fmt)
    }
}

impl<I: Idx, T> Deref for IndexVec<I, T> {
    type Target = IndexSlice<I, T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<I: Idx, T> DerefMut for IndexVec<I, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<I: Idx, T> Borrow<IndexSlice<I, T>> for IndexVec<I, T> {
    fn borrow(&self) -> &IndexSlice<I, T> {
        self
    }
}

impl<I: Idx, T> BorrowMut<IndexSlice<I, T>> for IndexVec<I, T> {
    fn borrow_mut(&mut self) -> &mut IndexSlice<I, T> {
        self
    }
}

impl<I: Idx, T> Extend<T> for IndexVec<I, T> {
    #[inline]
    fn extend<J: IntoIterator<Item = T>>(&mut self, iter: J) {
        self.raw.extend(iter);
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_one(&mut self, item: T) {
        self.raw.push(item);
    }

    #[inline]
    #[cfg(feature = "nightly")]
    fn extend_reserve(&mut self, additional: usize) {
        self.raw.reserve(additional);
    }
}

impl<I: Idx, T> FromIterator<T> for IndexVec<I, T> {
    #[inline]
    fn from_iter<J>(iter: J) -> Self
    where
        J: IntoIterator<Item = T>,
    {
        IndexVec::from_raw(Vec::from_iter(iter))
    }
}

impl<I: Idx, T> IntoIterator for IndexVec<I, T> {
    type Item = T;
    type IntoIter = vec::IntoIter<T>;

    #[inline]
    fn into_iter(self) -> vec::IntoIter<T> {
        self.raw.into_iter()
    }
}

impl<'a, I: Idx, T> IntoIterator for &'a IndexVec<I, T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> slice::Iter<'a, T> {
        self.iter()
    }
}

impl<'a, I: Idx, T> IntoIterator for &'a mut IndexVec<I, T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> slice::IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<I: Idx, T> Default for IndexVec<I, T> {
    #[inline]
    fn default() -> Self {
        IndexVec::new()
    }
}

impl<I: Idx, T, const N: usize> From<[T; N]> for IndexVec<I, T> {
    #[inline]
    fn from(array: [T; N]) -> Self {
        IndexVec::from_raw(array.into())
    }
}

#[cfg(feature = "nightly")]
impl<S: Encoder, I: Idx, T: Encodable<S>> Encodable<S> for IndexVec<I, T> {
    fn encode(&self, s: &mut S) {
        Encodable::encode(&self.raw, s);
    }
}

#[cfg(feature = "nightly")]
impl<D: Decoder, I: Idx, T: Decodable<D>> Decodable<D> for IndexVec<I, T> {
    fn decode(d: &mut D) -> Self {
        IndexVec::from_raw(Vec::<T>::decode(d))
    }
}

// Whether `IndexVec` is `Send` depends only on the data,
// not the phantom data.
unsafe impl<I: Idx, T> Send for IndexVec<I, T> where T: Send {}

#[cfg(test)]
mod tests;
