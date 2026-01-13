use super::*;

#[test]
fn test_vec_new() {
    let vec: IndexVec<usize, i32> = IndexVec::new();
    assert_eq!(vec.len(), 0);
    assert!(vec.is_empty());
}

#[test]
fn test_vec_from_raw() {
    let vec: IndexVec<usize, i32> = IndexVec::from_raw(vec![1, 2, 3]);
    assert_eq!(vec.len(), 3);
    assert_eq!(vec[0usize], 1);
    assert_eq!(vec[2usize], 3);
}

#[test]
fn test_vec_from_elem_n() {
    let vec: IndexVec<usize, i32> = IndexVec::from_elem_n(42, 5);
    assert_eq!(vec.len(), 5);
    for i in 0..5usize {
        assert_eq!(vec[i], 42);
    }
}

#[test]
fn test_vec_from_fn_n() {
    let vec: IndexVec<usize, usize> = IndexVec::from_fn_n(|i| i * 2, 4);
    assert_eq!(vec.len(), 4);
    assert_eq!(vec[0usize], 0);
    assert_eq!(vec[1usize], 2);
    assert_eq!(vec[2usize], 4);
    assert_eq!(vec[3usize], 6);
}

#[test]
fn test_vec_push() {
    let mut vec: IndexVec<usize, i32> = IndexVec::new();
    let idx0 = vec.push(10);
    let idx1 = vec.push(20);
    let idx2 = vec.push(30);

    assert_eq!(idx0, 0usize);
    assert_eq!(idx1, 1usize);
    assert_eq!(idx2, 2usize);
    assert_eq!(vec.len(), 3);
    assert_eq!(vec[idx0], 10);
    assert_eq!(vec[idx1], 20);
    assert_eq!(vec[idx2], 30);
}

#[test]
fn test_vec_pop() {
    let mut vec: IndexVec<usize, i32> = IndexVec::from_raw(vec![1, 2, 3]);
    assert_eq!(vec.pop(), Some(3));
    assert_eq!(vec.pop(), Some(2));
    assert_eq!(vec.pop(), Some(1));
    assert_eq!(vec.pop(), None);
}

#[test]
fn test_vec_truncate() {
    let mut vec: IndexVec<usize, i32> = IndexVec::from_raw(vec![1, 2, 3, 4, 5]);
    vec.truncate(3);
    assert_eq!(vec.len(), 3);
    assert_eq!(vec[2usize], 3);
}

#[test]
fn test_vec_resize() {
    let mut vec: IndexVec<usize, i32> = IndexVec::from_raw(vec![1, 2]);
    vec.resize(5, 0);
    assert_eq!(vec.len(), 5);
    assert_eq!(vec[4usize], 0);
}

#[test]
fn test_vec_append() {
    let mut vec1: IndexVec<usize, i32> = IndexVec::from_raw(vec![1, 2]);
    let mut vec2: IndexVec<usize, i32> = IndexVec::from_raw(vec![3, 4]);
    vec1.append(&mut vec2);

    assert_eq!(vec1.len(), 4);
    assert_eq!(vec2.len(), 0);
    assert_eq!(vec1[3usize], 4);
}

#[test]
fn test_vec_next_index() {
    let vec: IndexVec<usize, i32> = IndexVec::from_raw(vec![1, 2, 3]);
    assert_eq!(vec.next_index(), 3usize);
}

#[test]
fn test_vec_ensure_contains_elem() {
    let mut vec: IndexVec<usize, i32> = IndexVec::new();
    let elem_ref = vec.ensure_contains_elem(5usize, || 0);
    *elem_ref = 42;

    assert_eq!(vec.len(), 6);
    assert_eq!(vec[5usize], 42);
}

#[test]
fn test_vec_into_iter_enumerated() {
    let vec: IndexVec<usize, i32> = IndexVec::from_raw(vec![10, 20, 30]);
    let pairs: Vec<_> = vec.into_iter_enumerated().collect();
    assert_eq!(pairs, vec![(0usize, 10), (1usize, 20), (2usize, 30)]);
}

#[test]
fn test_option_vec_insert() {
    let mut vec: IndexVec<usize, Option<i32>> = IndexVec::new();
    assert_eq!(vec.insert(3usize, 42), None);
    assert_eq!(vec.len(), 4);
    assert_eq!(vec[3usize], Some(42));
    assert_eq!(vec.insert(3usize, 100), Some(42));
    assert_eq!(vec[3usize], Some(100));
}

#[test]
fn test_option_vec_contains() {
    let mut vec: IndexVec<usize, Option<i32>> = IndexVec::from_elem_n(None, 5);
    assert!(!vec.contains(2usize));
    vec[2usize] = Some(42);
    assert!(vec.contains(2usize));
}

#[test]
fn test_option_vec_remove() {
    let mut vec: IndexVec<usize, Option<i32>> = IndexVec::from_raw(vec![Some(1), Some(2), Some(3)]);
    assert_eq!(vec.remove(1usize), Some(2));
    assert_eq!(vec[1usize], None);
    assert_eq!(vec.remove(1usize), None);
}
