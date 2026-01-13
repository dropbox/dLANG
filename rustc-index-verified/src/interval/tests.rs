//! Tests for IntervalSet and SparseIntervalMatrix.
//!
//! These tests verify the baseline behavior matches upstream rustc_index.

use super::*;

#[test]
fn insert_collapses() {
    let mut set = IntervalSet::<u32>::new(10000);
    set.insert_range(9831..=9837);
    set.insert_range(43..=9830);
    assert_eq!(set.iter_intervals().collect::<Vec<_>>(), vec![43..9838]);
}

#[test]
fn contains() {
    let mut set = IntervalSet::new(300);
    set.insert(0u32);
    assert!(set.contains(0));
    set.insert_range(0..10);
    assert!(set.contains(9));
    assert!(!set.contains(10));
    set.insert_range(10..11);
    assert!(set.contains(10));
}

#[test]
fn insert() {
    for i in 0..30usize {
        let mut set = IntervalSet::new(300);
        for j in i..30usize {
            set.insert(j);
            for k in i..j {
                assert!(set.contains(k));
            }
        }
    }

    let mut set = IntervalSet::new(300);
    set.insert_range(0..1u32);
    assert!(set.contains(0), "{:?}", set.map);
    assert!(!set.contains(1));
    set.insert_range(1..1);
    assert!(set.contains(0));
    assert!(!set.contains(1));

    let mut set = IntervalSet::new(300);
    set.insert_range(4..5u32);
    set.insert_range(5..10);
    assert_eq!(set.iter().collect::<Vec<_>>(), [4, 5, 6, 7, 8, 9]);
    set.insert_range(3..7);
    assert_eq!(set.iter().collect::<Vec<_>>(), [3, 4, 5, 6, 7, 8, 9]);

    let mut set = IntervalSet::new(300);
    set.insert_range(0..10u32);
    set.insert_range(3..5);
    assert_eq!(
        set.iter().collect::<Vec<_>>(),
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    );

    let mut set = IntervalSet::new(300);
    set.insert_range(0..10u32);
    set.insert_range(0..3);
    assert_eq!(
        set.iter().collect::<Vec<_>>(),
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    );

    let mut set = IntervalSet::new(300);
    set.insert_range(0..10u32);
    set.insert_range(0..10);
    assert_eq!(
        set.iter().collect::<Vec<_>>(),
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    );

    let mut set = IntervalSet::new(300);
    set.insert_range(0..10u32);
    set.insert_range(5..10);
    assert_eq!(
        set.iter().collect::<Vec<_>>(),
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    );

    let mut set = IntervalSet::new(300);
    set.insert_range(0..10u32);
    set.insert_range(5..13);
    assert_eq!(
        set.iter().collect::<Vec<_>>(),
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    );
}

#[test]
fn insert_range() {
    #[track_caller]
    fn check<R>(range: R)
    where
        R: RangeBounds<usize> + Clone + IntoIterator<Item = usize> + std::fmt::Debug,
    {
        let mut set = IntervalSet::new(300);
        set.insert_range(range.clone());
        for i in set.iter() {
            assert!(range.contains(&i));
        }
        for i in range.clone() {
            assert!(
                set.contains(i),
                "A: {} in {:?}, inserted {:?}",
                i,
                set,
                range
            );
        }
        set.insert_range(range.clone());
        for i in set.iter() {
            assert!(range.contains(&i), "{} in {:?}", i, set);
        }
        for i in range.clone() {
            assert!(
                set.contains(i),
                "B: {} in {:?}, inserted {:?}",
                i,
                set,
                range
            );
        }
    }
    check(10..10);
    check(10..100);
    check(10..30);
    check(0..5);
    check(0..250);
    check(200..250);

    check(10..=10);
    check(10..=100);
    check(10..=30);
    check(0..=5);
    check(0..=250);
    check(200..=250);

    for i in 0..30 {
        for j in i..30 {
            check(i..j);
            check(i..=j);
        }
    }
}

#[test]
fn insert_range_dual() {
    let mut set = IntervalSet::<u32>::new(300);
    set.insert_range(0..3);
    assert_eq!(set.iter().collect::<Vec<_>>(), [0, 1, 2]);
    set.insert_range(5..7);
    assert_eq!(set.iter().collect::<Vec<_>>(), [0, 1, 2, 5, 6]);
    set.insert_range(3..4);
    assert_eq!(set.iter().collect::<Vec<_>>(), [0, 1, 2, 3, 5, 6]);
    set.insert_range(3..5);
    assert_eq!(set.iter().collect::<Vec<_>>(), [0, 1, 2, 3, 4, 5, 6]);
}

#[test]
fn last_set_before_adjacent() {
    let mut set = IntervalSet::<u32>::new(300);
    set.insert_range(0..3);
    set.insert_range(3..5);
    assert_eq!(set.last_set_in(0..3), Some(2));
    assert_eq!(set.last_set_in(0..5), Some(4));
    assert_eq!(set.last_set_in(3..5), Some(4));
    set.insert_range(2..5);
    assert_eq!(set.last_set_in(0..3), Some(2));
    assert_eq!(set.last_set_in(0..5), Some(4));
    assert_eq!(set.last_set_in(3..5), Some(4));
}

#[test]
fn last_set_in() {
    fn easy(set: &IntervalSet<usize>, needle: impl RangeBounds<usize>) -> Option<usize> {
        let mut last_leq = None;
        for e in set.iter() {
            if needle.contains(&e) {
                last_leq = Some(e);
            }
        }
        last_leq
    }

    #[track_caller]
    fn cmp(set: &IntervalSet<usize>, needle: impl RangeBounds<usize> + Clone + std::fmt::Debug) {
        assert_eq!(
            set.last_set_in(needle.clone()),
            easy(set, needle.clone()),
            "{:?} in {:?}",
            needle,
            set
        );
    }
    let mut set = IntervalSet::new(300);
    cmp(&set, 50..=50);
    set.insert(64);
    cmp(&set, 64..=64);
    set.insert(64 - 1);
    cmp(&set, 0..=64 - 1);
    cmp(&set, 0..=5);
    cmp(&set, 10..100);
    set.insert(100);
    cmp(&set, 100..110);
    cmp(&set, 99..100);
    cmp(&set, 99..=100);

    for i in 0..=30 {
        for j in i..=30 {
            for k in 0..30 {
                let mut set = IntervalSet::new(100);
                cmp(&set, ..j);
                cmp(&set, i..);
                cmp(&set, i..j);
                cmp(&set, i..=j);
                set.insert(k);
                cmp(&set, ..j);
                cmp(&set, i..);
                cmp(&set, i..j);
                cmp(&set, i..=j);
            }
        }
    }
}

#[test]
fn test_new_empty() {
    let set = IntervalSet::<u32>::new(100);
    assert!(set.is_empty());
    assert!(!set.contains(0));
    assert!(!set.contains(50));
    assert!(!set.contains(99));
}

#[test]
fn test_clear() {
    let mut set = IntervalSet::<u32>::new(100);
    set.insert(10);
    set.insert(20);
    assert!(!set.is_empty());
    set.clear();
    assert!(set.is_empty());
    assert!(!set.contains(10));
    assert!(!set.contains(20));
}

#[test]
fn test_insert_all() {
    let mut set = IntervalSet::<u32>::new(100);
    set.insert_all();
    for i in 0..100u32 {
        assert!(set.contains(i), "should contain {}", i);
    }
}

#[test]
fn test_first_unset_in() {
    let mut set = IntervalSet::<u32>::new(100);

    // Empty set: first unset is the start of range
    assert_eq!(set.first_unset_in(0..10), Some(0));
    assert_eq!(set.first_unset_in(5..10), Some(5));

    // Insert some values
    set.insert_range(0..5);
    assert_eq!(set.first_unset_in(0..10), Some(5));
    assert_eq!(set.first_unset_in(0..5), None); // all set
    assert_eq!(set.first_unset_in(3..10), Some(5));

    // Insert more
    set.insert_range(7..10);
    assert_eq!(set.first_unset_in(0..10), Some(5));
    assert_eq!(set.first_unset_in(5..10), Some(5));
    assert_eq!(set.first_unset_in(6..10), Some(6));
    assert_eq!(set.first_unset_in(7..10), None); // all set
}

#[test]
fn test_superset() {
    let mut a = IntervalSet::<u32>::new(100);
    let mut b = IntervalSet::<u32>::new(100);

    // Empty sets
    assert!(a.superset(&b));
    assert!(b.superset(&a));

    // a contains more
    a.insert_range(0..10);
    assert!(a.superset(&b));
    assert!(!b.superset(&a));

    // b is subset
    b.insert_range(2..5);
    assert!(a.superset(&b));
    assert!(!b.superset(&a));

    // b has element not in a
    b.insert(50);
    assert!(!a.superset(&b));
    assert!(!b.superset(&a));
}

#[test]
fn test_union() {
    let mut a = IntervalSet::<u32>::new(100);
    let mut b = IntervalSet::<u32>::new(100);

    a.insert_range(0..10);
    b.insert_range(5..15);

    let changed = a.union(&b);
    assert!(changed);

    // Check union contains all
    for i in 0..15 {
        assert!(a.contains(i), "should contain {}", i);
    }
    assert!(!a.contains(15));

    // Union again should not change
    let changed2 = a.union(&b);
    assert!(!changed2);
}

// Tests for SparseIntervalMatrix
#[test]
fn test_sparse_matrix_new() {
    let matrix = SparseIntervalMatrix::<u32, u32>::new(100);
    assert!(matrix.row(0).is_none());
    assert!(matrix.row(10).is_none());
}

#[test]
fn test_sparse_matrix_insert() {
    let mut matrix = SparseIntervalMatrix::<u32, u32>::new(100);

    matrix.insert(0, 5);
    assert!(matrix.contains(0, 5));
    assert!(!matrix.contains(0, 6));
    assert!(!matrix.contains(1, 5));

    matrix.insert(1, 10);
    assert!(matrix.contains(1, 10));
}

#[test]
fn test_sparse_matrix_insert_range() {
    let mut matrix = SparseIntervalMatrix::<u32, u32>::new(100);

    matrix.insert_range(0, 5..15);
    for i in 5..15 {
        assert!(matrix.contains(0, i), "row 0 should contain {}", i);
    }
    assert!(!matrix.contains(0, 4));
    assert!(!matrix.contains(0, 15));
}

#[test]
fn test_sparse_matrix_union_rows() {
    let mut matrix = SparseIntervalMatrix::<u32, u32>::new(100);

    matrix.insert_range(0, 0..10);
    matrix.insert_range(1, 5..15);

    let changed = matrix.union_rows(0, 1);
    assert!(changed);

    // Row 1 should have union
    for i in 0..15 {
        assert!(matrix.contains(1, i), "row 1 should contain {}", i);
    }

    // Row 0 unchanged
    for i in 0..10 {
        assert!(matrix.contains(0, i), "row 0 should contain {}", i);
    }
    assert!(!matrix.contains(0, 10));
}

#[test]
fn test_sparse_matrix_insert_all_into_row() {
    let mut matrix = SparseIntervalMatrix::<u32, u32>::new(100);

    matrix.insert_all_into_row(0);

    for i in 0..100 {
        assert!(matrix.contains(0, i), "row 0 should contain {}", i);
    }
    assert!(!matrix.contains(1, 0)); // Other rows unaffected
}

// ============================================================================
// Tests for append (1.94.0 upgrade)
// ============================================================================

#[test]
fn test_append_to_empty() {
    let mut set = IntervalSet::<u32>::new(100);
    set.append(5);
    assert!(set.contains(5));
    assert!(!set.contains(4));
    assert!(!set.contains(6));
}

#[test]
fn test_append_adjacent() {
    let mut set = IntervalSet::<u32>::new(100);
    set.append(5);
    set.append(6); // Adjacent, should extend
    set.append(7); // Adjacent, should extend
    assert!(set.contains(5));
    assert!(set.contains(6));
    assert!(set.contains(7));
    // Should be a single interval
    assert_eq!(set.iter_intervals().count(), 1);
    assert_eq!(set.iter_intervals().next(), Some(5..8));
}

#[test]
fn test_append_gap() {
    let mut set = IntervalSet::<u32>::new(100);
    set.append(5);
    set.append(10); // Gap, should create new interval
    assert!(set.contains(5));
    assert!(set.contains(10));
    assert!(!set.contains(7));
    // Should be two intervals
    assert_eq!(set.iter_intervals().count(), 2);
}

#[test]
fn test_append_duplicate() {
    let mut set = IntervalSet::<u32>::new(100);
    set.append(5);
    set.append(5); // Duplicate, should be no-op
    assert!(set.contains(5));
    assert_eq!(set.iter_intervals().count(), 1);
}

#[test]
#[should_panic(expected = "assertion failed: *last_end <= point")]
fn test_append_out_of_order() {
    let mut set = IntervalSet::<u32>::new(100);
    set.append(10);
    set.append(5); // Out of order, should panic
}

// ============================================================================
// Tests for disjoint (1.94.0 upgrade)
// ============================================================================

#[test]
fn test_disjoint_empty_sets() {
    let a = IntervalSet::<u32>::new(100);
    let b = IntervalSet::<u32>::new(100);
    assert!(a.disjoint(&b));
    assert!(b.disjoint(&a));
}

#[test]
fn test_disjoint_one_empty() {
    let mut a = IntervalSet::<u32>::new(100);
    let b = IntervalSet::<u32>::new(100);
    a.insert_range(10..20);
    assert!(a.disjoint(&b));
    assert!(b.disjoint(&a));
}

#[test]
fn test_disjoint_no_overlap() {
    let mut a = IntervalSet::<u32>::new(100);
    let mut b = IntervalSet::<u32>::new(100);
    a.insert_range(0..10);
    b.insert_range(20..30);
    assert!(a.disjoint(&b));
    assert!(b.disjoint(&a));
}

#[test]
fn test_disjoint_adjacent() {
    let mut a = IntervalSet::<u32>::new(100);
    let mut b = IntervalSet::<u32>::new(100);
    a.insert_range(0..10);
    b.insert_range(10..20); // Adjacent but disjoint (exclusive end)
    assert!(a.disjoint(&b));
    assert!(b.disjoint(&a));
}

#[test]
fn test_not_disjoint_overlap() {
    let mut a = IntervalSet::<u32>::new(100);
    let mut b = IntervalSet::<u32>::new(100);
    a.insert_range(0..15);
    b.insert_range(10..20);
    assert!(!a.disjoint(&b));
    assert!(!b.disjoint(&a));
}

#[test]
fn test_not_disjoint_single_point() {
    let mut a = IntervalSet::<u32>::new(100);
    let mut b = IntervalSet::<u32>::new(100);
    a.insert(10);
    b.insert(10);
    assert!(!a.disjoint(&b));
    assert!(!b.disjoint(&a));
}

#[test]
fn test_not_disjoint_subset() {
    let mut a = IntervalSet::<u32>::new(100);
    let mut b = IntervalSet::<u32>::new(100);
    a.insert_range(0..30);
    b.insert_range(10..20);
    assert!(!a.disjoint(&b));
    assert!(!b.disjoint(&a));
}

#[test]
fn test_disjoint_multiple_intervals() {
    let mut a = IntervalSet::<u32>::new(100);
    let mut b = IntervalSet::<u32>::new(100);
    a.insert_range(0..10);
    a.insert_range(30..40);
    b.insert_range(15..25);
    b.insert_range(50..60);
    assert!(a.disjoint(&b));
    assert!(b.disjoint(&a));
}

#[test]
fn test_not_disjoint_multiple_intervals() {
    let mut a = IntervalSet::<u32>::new(100);
    let mut b = IntervalSet::<u32>::new(100);
    a.insert_range(0..10);
    a.insert_range(30..40);
    b.insert_range(15..25);
    b.insert_range(35..45); // Overlaps with a's 30..40
    assert!(!a.disjoint(&b));
    assert!(!b.disjoint(&a));
}
