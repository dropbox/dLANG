//! Drop-in Compatibility Test
//!
//! This test verifies that rustc-index-verified provides the same public API
//! as upstream rustc_index. It tests:
//!
//! 1. All public types exist with correct names
//! 2. All public methods exist with correct signatures
//! 3. Type relationships (impls, derives) match upstream
//!
//! If this test compiles and passes, our crate is API-compatible.

use rustc_index_verified::{
    // interval types (from interval module since they're not re-exported at root)
    interval::{IntervalSet, SparseIntervalMatrix},
    // bit_set types
    BitMatrix,
    BitRelations,
    ChunkedBitSet,
    DenseBitSet,
    FiniteBitSet,
    GrowableBitSet,
    // Core types from lib.rs exports
    Idx,
    IndexSlice,
    IndexVec,
    MixedBitSet,
    SparseBitMatrix,
};

// Test Idx trait is public and usable
#[allow(dead_code)]
fn test_idx_trait_helper<I: Idx>(idx: usize) -> usize {
    // Idx requires these methods
    let val: I = I::new(idx);
    val.index()
}

// Ensure BitRelations is usable as a bound.
#[allow(dead_code)]
fn test_bit_relations_trait_helper<T, Rhs>(lhs: &mut T, rhs: &Rhs)
where
    T: BitRelations<Rhs>,
{
    let _ = (lhs, rhs);
}

// Test u32 implements Idx
#[test]
fn test_u32_idx() {
    let idx: u32 = Idx::new(42);
    assert_eq!(idx.index(), 42);
}

// Test IndexVec API
#[test]
fn test_indexvec_api() {
    // Construction
    let mut vec: IndexVec<u32, String> = IndexVec::new();
    assert!(vec.is_empty());

    // push returns the index
    let idx = vec.push(String::from("hello"));
    assert_eq!(idx, 0u32);
    assert_eq!(vec.len(), 1);

    // Indexing
    assert_eq!(&vec[0u32], "hello");

    // from_fn_n
    let vec2: IndexVec<u32, usize> = IndexVec::from_fn_n(|i: u32| i.index(), 5);
    assert_eq!(vec2.len(), 5);

    // Iteration
    for (idx, _val) in vec.iter_enumerated() {
        let _: u32 = idx;
    }
}

// Test IndexSlice API (via IndexVec)
#[test]
fn test_indexslice_api() {
    let vec: IndexVec<u32, i32> = IndexVec::from_fn_n(|i: u32| i.index() as i32, 10);
    let slice: &IndexSlice<u32, i32> = &vec;

    assert_eq!(slice.len(), 10);
    assert!(!slice.is_empty());
    assert_eq!(slice[0u32], 0);
    assert_eq!(slice[9u32], 9);
}

// Test DenseBitSet API
#[test]
fn test_bitset_api() {
    let mut set: DenseBitSet<u32> = DenseBitSet::new_empty(100);
    assert!(set.is_empty());
    assert_eq!(set.domain_size(), 100);

    // insert returns whether it was new
    assert!(set.insert(42u32));
    assert!(!set.insert(42u32)); // already present

    assert!(set.contains(42u32));
    assert_eq!(set.count(), 1);

    // remove returns whether it was present
    assert!(set.remove(42u32));
    assert!(!set.remove(42u32));
}

// Test GrowableBitSet API
#[test]
fn test_growable_bitset_api() {
    let mut set: GrowableBitSet<u32> = GrowableBitSet::new_empty();
    set.insert(100u32);
    set.ensure(200);
    assert!(set.contains(100u32));
}

// Test ChunkedBitSet API
#[test]
fn test_chunked_bitset_api() {
    let mut set: ChunkedBitSet<u32> = ChunkedBitSet::new_empty(1000);
    set.insert(500u32);
    assert!(set.contains(500u32));
    assert_eq!(set.count(), 1);
}

// Test BitMatrix API
#[test]
fn test_bitmatrix_api() {
    let mut matrix: BitMatrix<u32, u32> = BitMatrix::new(10, 20);
    assert_eq!(matrix.rows().count(), 10);

    assert!(matrix.insert(5u32, 15u32));
    assert!(matrix.contains(5u32, 15u32));
}

// Test SparseBitMatrix API
#[test]
fn test_sparse_bitmatrix_api() {
    let mut matrix: SparseBitMatrix<u32, u32> = SparseBitMatrix::new(20);

    assert!(matrix.insert(5u32, 15u32));
    assert!(matrix.contains(5u32, 15u32));
    assert!(!matrix.contains(5u32, 16u32));
}

// Test IntervalSet API
#[test]
fn test_intervalset_api() {
    let mut set: IntervalSet<u32> = IntervalSet::new(100);

    set.insert_range(10u32..20u32);
    assert!(set.contains(15u32));
    assert!(!set.contains(5u32));
    assert!(!set.contains(25u32));
}

// Test SparseIntervalMatrix API
#[test]
fn test_sparse_interval_matrix_api() {
    let mut matrix: SparseIntervalMatrix<u32, u32> = SparseIntervalMatrix::new(100);

    matrix.insert_range(5u32, 10u32..20u32);
    assert!(matrix.contains(5u32, 15u32));
    assert!(!matrix.contains(5u32, 5u32));
}

// Test BitRelations trait
#[test]
fn test_bit_relations() {
    let mut set1: DenseBitSet<u32> = DenseBitSet::new_empty(100);
    let mut set2: DenseBitSet<u32> = DenseBitSet::new_empty(100);
    test_bit_relations_trait_helper(&mut set1, &set2);

    set1.insert(1u32);
    set1.insert(2u32);
    set2.insert(2u32);
    set2.insert(3u32);

    // Union: set1 |= set2
    let changed = set1.union(&set2);
    assert!(changed);
    assert!(set1.contains(1u32));
    assert!(set1.contains(2u32));
    assert!(set1.contains(3u32));

    // Subtract
    let mut set3: DenseBitSet<u32> = DenseBitSet::new_empty(100);
    set3.insert(1u32);
    set3.insert(2u32);
    let mut set4: DenseBitSet<u32> = DenseBitSet::new_empty(100);
    set4.insert(2u32);
    set3.subtract(&set4);
    assert!(set3.contains(1u32));
    assert!(!set3.contains(2u32));
}

#[test]
fn test_bit_relations_chunked_and_mixed() {
    let mut a: ChunkedBitSet<u32> = ChunkedBitSet::new_empty(2050);
    a.insert(0u32);
    a.insert(2048u32);
    a.insert(2049u32);

    let mut b: ChunkedBitSet<u32> = ChunkedBitSet::new_empty(2050);
    b.insert(2049u32);

    let mut sub = a.clone();
    assert!(sub.subtract(&b));
    assert!(sub.contains(0u32));
    assert!(sub.contains(2048u32));
    assert!(!sub.contains(2049u32));

    let mut inter = a.clone();
    assert!(inter.intersect(&b));
    assert!(!inter.contains(0u32));
    assert!(!inter.contains(2048u32));
    assert!(inter.contains(2049u32));

    let mut m_small: MixedBitSet<u32> = MixedBitSet::new_empty(100);
    m_small.insert(1u32);
    m_small.insert(2u32);
    let mut m_small_other: MixedBitSet<u32> = MixedBitSet::new_empty(100);
    m_small_other.insert(2u32);
    assert!(m_small.subtract(&m_small_other));
    assert!(m_small.contains(1u32));
    assert!(!m_small.contains(2u32));

    let mut m_large: MixedBitSet<u32> = MixedBitSet::new_empty(2050);
    m_large.insert(2048u32);
    m_large.insert(2049u32);
    let mut m_large_other: MixedBitSet<u32> = MixedBitSet::new_empty(2050);
    m_large_other.insert(2049u32);
    assert!(m_large.subtract(&m_large_other));
    assert!(m_large.contains(2048u32));
    assert!(!m_large.contains(2049u32));
}

// Test FiniteBitSet API
#[test]
fn test_finite_bitset_api() {
    let mut set: FiniteBitSet<u32> = FiniteBitSet::new_empty();
    set.set(5);
    assert!(set.contains(5).unwrap_or(false));
    set.clear(5);
    assert!(!set.contains(5).unwrap_or(true));
}

// Test static_assert_size macro exists
#[test]
fn test_static_assert_size_macro() {
    // This should compile - the macro should be available
    rustc_index_verified::static_assert_size!(u32, 4);
    rustc_index_verified::static_assert_size!(u64, 8);
}

// Verify that types can be used in generic contexts
fn generic_idx_user<I: Idx>(_vec: &IndexVec<I, i32>) {}
fn generic_bitset_user<T: Idx>(_set: &DenseBitSet<T>) {}

#[test]
fn test_generic_usage() {
    let vec: IndexVec<u32, i32> = IndexVec::from_fn_n(|_: u32| 0, 5);
    generic_idx_user(&vec);

    let set: DenseBitSet<u32> = DenseBitSet::new_empty(10);
    generic_bitset_user(&set);
}

// Test that IndexVec implements expected traits
#[test]
fn test_indexvec_traits() {
    let vec: IndexVec<u32, i32> = IndexVec::from_fn_n(|_: u32| 0, 5);

    // Clone
    let _cloned = vec.clone();

    // Debug
    let _debug = format!("{:?}", vec);

    // Index and IndexMut
    let mut vec2 = vec.clone();
    let _: &i32 = &vec2[0u32];
    let _: &mut i32 = &mut vec2[0u32];
}

// Test that BitSet implements expected traits
#[test]
fn test_bitset_traits() {
    let set: DenseBitSet<u32> = DenseBitSet::new_empty(10);

    // Clone
    let _cloned = set.clone();

    // Debug
    let _debug = format!("{:?}", set);
}
