//! # rustc-index-verified
//!
//! Formally verified version of `rustc_index` with mathematical specifications.
//!
//! This crate provides the same functionality as `rustc_index`, but with
//! formal specifications (`#[requires]`, `#[ensures]`) that are verified
//! using tRust/trustc.
//!
//! ## Verification Status
//!
//! See `docs/VERIFICATION_STATUS.md` for current verification progress.

// Match upstream rustc_index attributes (1.94.0-dev baseline)
// tidy-alphabetical-start
#![cfg_attr(all(feature = "nightly", test), feature(stmt_expr_attributes))]
#![cfg_attr(feature = "nightly", feature(extend_one, step_trait, test))]
#![cfg_attr(feature = "nightly", feature(new_range_api))]
// tidy-alphabetical-end

// For standalone builds without nightly feature, still need step_trait for interval.rs
#![cfg_attr(not(feature = "nightly"), feature(step_trait))]

pub mod bit_set;
#[cfg(feature = "nightly")]
pub mod interval;
// Also available without nightly for standalone development
#[cfg(not(feature = "nightly"))]
pub mod interval;

mod idx;
mod slice;
mod vec;

pub use idx::{Idx, IntoSliceIdx};
#[cfg(feature = "nightly")]
pub use rustc_index_macros::newtype_index;
pub use slice::IndexSlice;
#[doc(no_inline)]
pub use vec::IndexVec;

// Also re-export bit_set types for convenience (backwards compatibility)
pub use bit_set::{
    BitIter, BitMatrix, BitRelations, ChunkedBitIter, ChunkedBitSet, DenseBitSet, FiniteBitSet,
    FiniteBitSetTy, GrowableBitSet, MixedBitIter, MixedBitSet, SparseBitMatrix,
};

/// Type size assertion macro (matches upstream rustc_index exactly)
///
/// The first argument is a type and the second argument is its expected size.
///
/// <div class="warning">
///
/// Emitting hard errors from size assertions like this is generally not
/// recommended, especially in libraries, because they can cause build failures if the layout
/// algorithm or dependencies change. Here in rustc we control the toolchain and layout algorithm,
/// so the former is not a problem. For the latter we have a lockfile as rustc is an application and
/// precompiled library.
///
/// Short version: Don't copy this macro into your own code. Use a `#[test]` instead.
///
/// </div>
#[macro_export]
#[cfg(not(feature = "rustc_randomized_layouts"))]
macro_rules! static_assert_size {
    ($ty:ty, $size:expr) => {
        const _: [(); $size] = [(); ::std::mem::size_of::<$ty>()];
    };
}

#[macro_export]
#[cfg(feature = "rustc_randomized_layouts")]
macro_rules! static_assert_size {
    ($ty:ty, $size:expr) => {
        // no effect other than using the statements.
        // struct sizes are not deterministic under randomized layouts
        const _: (usize, usize) = ($size, ::std::mem::size_of::<$ty>());
    };
}

/// Convenience macro for creating an `IndexVec` from a list of elements.
///
/// Similar to `vec![]` but produces an `IndexVec`.
///
/// # Examples
/// ```ignore
/// let v: IndexVec<usize, i32> = indexvec![1, 2, 3];
/// let v: IndexVec<usize, i32> = indexvec![0; 10]; // 10 zeros
/// ```
#[macro_export]
macro_rules! indexvec {
    ($expr:expr; $n:expr) => {
        IndexVec::from_raw(vec![$expr; $n])
    };
    ($($expr:expr),* $(,)?) => {
        IndexVec::from_raw(vec![$($expr),*])
    };
}
