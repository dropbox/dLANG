use super::*;

#[test]
fn dense_bitset_basic_ops() {
    let mut bs: DenseBitSet<usize> = DenseBitSet::new_empty(100);
    assert_eq!(bs.domain_size(), 100);
    assert!(bs.is_empty());

    assert!(bs.insert(42));
    assert!(bs.contains(42));
    assert!(!bs.insert(42));

    assert!(bs.remove(42));
    assert!(!bs.contains(42));
    assert!(!bs.remove(42));
}

#[test]
fn dense_bitset_union_subtract_intersect() {
    let mut a: DenseBitSet<usize> = DenseBitSet::new_empty(64);
    let mut b: DenseBitSet<usize> = DenseBitSet::new_empty(64);

    a.insert(1);
    a.insert(3);
    b.insert(3);
    b.insert(5);

    assert!(a.union(&b));
    assert!(a.contains(1));
    assert!(a.contains(3));
    assert!(a.contains(5));

    assert!(a.subtract(&b));
    assert!(a.contains(1));
    assert!(!a.contains(3));
    assert!(!a.contains(5));

    assert!(a.intersect(&b));
    assert!(a.is_empty());
}

#[test]
fn dense_bitset_union_not() {
    let mut a: DenseBitSet<usize> = DenseBitSet::new_empty(64);
    let mut b: DenseBitSet<usize> = DenseBitSet::new_empty(64);

    a.insert(10);
    a.insert(20);
    b.insert(20);

    a.union_not(&b);
    assert!(a.contains(10));
    assert!(a.contains(20));
    assert!(a.contains(0));
}

#[test]
fn mixed_bitset_selects_representation() {
    let small: MixedBitSet<usize> = MixedBitSet::new_empty(100);
    assert!(matches!(small, MixedBitSet::Small(_)));

    let large: MixedBitSet<usize> = MixedBitSet::new_empty(3000);
    assert!(matches!(large, MixedBitSet::Large(_)));
}

#[test]
fn chunked_bitset_basic_ops() {
    let mut bs: ChunkedBitSet<usize> = ChunkedBitSet::new_empty(3000);
    assert_eq!(bs.domain_size(), 3000);
    assert!(bs.is_empty());

    assert!(bs.insert(2049));
    assert!(bs.contains(2049));
    assert!(bs.remove(2049));
    assert!(!bs.contains(2049));

    bs.assert_valid();
    let _ = bs.chunks();
}

#[test]
fn growable_bitset_basic_ops() {
    let mut bs: GrowableBitSet<usize> = GrowableBitSet::new_empty();
    assert!(bs.is_empty());

    assert!(bs.insert(100));
    assert!(bs.contains(100));
    assert_eq!(bs.len(), 1);
    assert!(bs.remove(100));
    assert!(!bs.contains(100));
}
