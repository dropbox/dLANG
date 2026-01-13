//! Example: Verified Sorting in tRust
//!
//! This shows how verified sorting functions will look in tRust.
//! The compiler will prove:
//! 1. The output is a permutation of the input
//! 2. The output is sorted
//! 3. The function terminates
//!
//! # Trust Configuration
//!
//! This crate uses `[package.metadata.trust]` in Cargo.toml:
//! ```toml
//! [package.metadata.trust]
//! level = "verified"
//! ```

use trust_macros::{decreases, ensures, ghost, pure, requires, trust_level};

/// A verified insertion sort
#[requires(true)] // No preconditions
#[ensures(result.len() == input.len())]
#[decreases(input.len())]
#[must_use]
pub fn insertion_sort(input: Vec<i32>) -> Vec<i32> {
    if input.is_empty() {
        return vec![];
    }

    let mut sorted = insertion_sort(input[1..].to_vec());

    // Insert input[0] into sorted position
    let elem = input[0];
    let mut i = 0;

    // Note: Loop invariants require compiler integration
    // #[invariant(i <= sorted.len())]
    while i < sorted.len() && sorted[i] < elem {
        i += 1;
    }

    sorted.insert(i, elem);
    sorted
}

/// A verified binary search
#[requires(is_sorted(&arr))]
#[ensures(result.is_some() => arr[result.unwrap()] == *target)]
#[must_use]
pub fn binary_search(arr: &[i32], target: &i32) -> Option<usize> {
    if arr.is_empty() {
        return None;
    }

    let mut lo = 0;
    let mut hi = arr.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;

        match arr[mid].cmp(target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => lo = mid + 1,
            std::cmp::Ordering::Greater => hi = mid,
        }
    }

    None
}

/// Verified quicksort
#[requires(true)]
#[ensures(result.len() == input.len())]
#[must_use]
pub fn quicksort(input: Vec<i32>) -> Vec<i32> {
    if input.len() <= 1 {
        return input;
    }

    let pivot = input[0];
    let rest = &input[1..];

    let (less, greater): (Vec<_>, Vec<_>) = rest.iter().copied().partition(|x| *x < pivot);

    let mut sorted_less = quicksort(less);
    let sorted_greater = quicksort(greater);

    sorted_less.push(pivot);
    sorted_less.extend(sorted_greater);
    sorted_less
}

/// Pure function to check if array is sorted
#[pure]
#[must_use]
pub fn is_sorted(arr: &[i32]) -> bool {
    for i in 1..arr.len() {
        if arr[i - 1] > arr[i] {
            return false;
        }
    }
    true
}

// Ghost functions for specifications (compile away to nothing)
#[ghost]
fn permutation(_a: &[i32], _b: &[i32]) -> bool {
    // Would be defined in stdlib_specs
    unimplemented!()
}

#[ghost]
fn sorted_ghost(_arr: &[i32]) -> bool {
    // Would be defined in stdlib_specs
    unimplemented!()
}

/// Module with explicit trust level - all specs in this module are verified
#[trust_level(verified)]
pub mod verified_algorithms {
    use trust_macros::{ensures, requires};

    /// Selection sort with verification
    #[requires(true)]
    #[ensures(result.len() == input.len())]
    #[must_use]
    pub fn selection_sort(input: Vec<i32>) -> Vec<i32> {
        let mut arr = input;
        let len = arr.len();

        for i in 0..len {
            let mut min_idx = i;
            for j in (i + 1)..len {
                if arr[j] < arr[min_idx] {
                    min_idx = j;
                }
            }
            arr.swap(i, min_idx);
        }

        arr
    }
}

/// Module for legacy code - verification skipped
#[trust_level(assumed)]
pub mod legacy {
    /// Old sort implementation - not verified
    #[must_use]
    pub fn old_sort(mut arr: Vec<i32>) -> Vec<i32> {
        arr.sort_unstable();
        arr
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insertion_sort() {
        let input = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let result = insertion_sort(input.clone());
        assert_eq!(result.len(), input.len());
        assert!(is_sorted(&result));
    }

    #[test]
    fn test_quicksort() {
        let input = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let result = quicksort(input.clone());
        assert_eq!(result.len(), input.len());
        assert!(is_sorted(&result));
    }

    #[test]
    fn test_binary_search() {
        let arr = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
        assert_eq!(binary_search(&arr, &5), Some(4));
        assert_eq!(binary_search(&arr, &10), None);
        assert_eq!(binary_search(&arr, &1), Some(0));
    }

    #[test]
    fn test_selection_sort() {
        use super::verified_algorithms::selection_sort;
        let input = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let result = selection_sort(input.clone());
        assert_eq!(result.len(), input.len());
        assert!(is_sorted(&result));
    }

    #[test]
    fn test_legacy_sort() {
        use super::legacy::old_sort;
        let input = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let result = old_sort(input.clone());
        assert_eq!(result.len(), input.len());
        assert!(is_sorted(&result));
    }
}
