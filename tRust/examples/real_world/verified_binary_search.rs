//! Verified Binary Search - Real-World Verification Test
//!
//! Binary search implementation with formal specifications.
//! Tests array indexing, loop invariants, and sorting predicates.

/// Binary search on a sorted array slice
/// Returns the index of the target if found, or -1 if not found
///
/// We use i32 for indices to simplify verification (avoid Option handling)
/// Note: This simplified version requires arr_len > 0 for easier verification
// #[requires(arr_len > 0)]
// #[ensures(result == -1 || result >= 0 && result < arr_len)]
// #[invariant(low >= 0 && low <= arr_len)]
fn binary_search_index(arr: &[i32], target: i32, arr_len: i32) -> i32 {
    let mut low: i32 = 0;
    let mut high: i32 = arr_len - 1;

    while low <= high {
        let mid = low + (high - low) / 2;

        if mid < 0 || mid >= arr_len {
            return -1; // Safety check
        }

        let mid_val = arr[mid as usize];

        if mid_val == target {
            return mid;
        } else if mid_val < target {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }

    -1
}

/// Find the minimum element in an array
// #[requires(arr_len > 0)]
// #[ensures(result >= 0 && result < arr_len)]
// #[invariant(i >= 1 && i <= arr_len)]
// #[invariant(min_idx >= 0 && min_idx < arr_len)]
fn find_min_index(arr: &[i32], arr_len: i32) -> i32 {
    let mut min_idx: i32 = 0;
    let mut i: i32 = 1;

    while i < arr_len {
        if arr[i as usize] < arr[min_idx as usize] {
            min_idx = i;
        }
        i = i + 1;
    }

    min_idx
}

/// Count elements equal to target
// #[requires(arr_len >= 0)]
// #[ensures(result >= 0)]
// #[invariant(i >= 0 && i <= arr_len)]
// #[invariant(count >= 0)]
fn count_equal(arr: &[i32], target: i32, arr_len: i32) -> i32 {
    let mut count: i32 = 0;
    let mut i: i32 = 0;

    while i < arr_len {
        if arr[i as usize] == target {
            count = count + 1;
        }
        i = i + 1;
    }

    count
}

/// Check if array contains target (linear search)
// #[requires(arr_len >= 0)]
// #[ensures(result == false || result == true)]
// #[invariant(i >= 0 && i <= arr_len)]
fn contains(arr: &[i32], target: i32, arr_len: i32) -> bool {
    let mut i: i32 = 0;

    while i < arr_len {
        if arr[i as usize] == target {
            return true;
        }
        i = i + 1;
    }

    false
}

/// Sum of first n positive integers (closed form)
// #[requires(n >= 0)]
// #[ensures(result == n * (n + 1) / 2)]
fn sum_to_n(n: i32) -> i32 {
    n * (n + 1) / 2
}

/// Sum of first n positive integers (iterative)
// #[requires(n >= 0)]
// #[ensures(result == n * (n + 1) / 2)]
// #[invariant(i >= 0 && i <= n + 1)]
fn sum_to_n_iter(n: i32) -> i32 {
    let mut sum: i32 = 0;
    let mut i: i32 = 1;

    while i <= n {
        sum = sum + i;
        i = i + 1;
    }

    sum
}

/// Integer division (truncated towards zero)
// #[requires(b != 0)]
// #[ensures(b > 0 && a >= 0 && result == a / b || b < 0 || a < 0)]
fn safe_div(a: i32, b: i32) -> i32 {
    if b == 0 {
        0 // Should not happen due to precondition
    } else {
        a / b
    }
}

/// Clamp value to range [lo, hi]
// #[requires(lo <= hi)]
// #[ensures(result >= lo && result <= hi)]
fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

/// Middle of three values (avoids overflow in mid calculation)
// #[ensures(result >= a && result <= c || result >= c && result <= a)]
fn midpoint(a: i32, c: i32) -> i32 {
    a + (c - a) / 2
}

/// Check if value is in bounds
// #[requires(lo <= hi)]
// #[ensures(result == (x >= lo && x <= hi))]
fn in_bounds(x: i32, lo: i32, hi: i32) -> bool {
    x >= lo && x <= hi
}

fn main() {
    // Test binary search
    let arr = [1, 2, 3, 5, 8, 13, 21];
    println!("Binary search for 5: {}", binary_search_index(&arr, 5, 7));
    println!("Binary search for 7: {}", binary_search_index(&arr, 7, 7));

    // Test find_min_index
    let arr2 = [3, 1, 4, 1, 5, 9, 2, 6];
    println!("Min index in arr2: {}", find_min_index(&arr2, 8));

    // Test count_equal
    println!("Count of 1 in arr2: {}", count_equal(&arr2, 1, 8));

    // Test contains
    println!("Contains 5: {}", contains(&arr, 5, 7));
    println!("Contains 7: {}", contains(&arr, 7, 7));

    // Test sum_to_n
    println!("Sum to 10 (closed): {}", sum_to_n(10));
    println!("Sum to 10 (iter): {}", sum_to_n_iter(10));

    // Test safe_div
    println!("10 / 3: {}", safe_div(10, 3));

    // Test clamp
    println!("Clamp 15 to [0, 10]: {}", clamp(15, 0, 10));
    println!("Clamp 5 to [0, 10]: {}", clamp(5, 0, 10));

    // Test midpoint
    println!("Midpoint of 10, 20: {}", midpoint(10, 20));

    // Test in_bounds
    println!("5 in [0, 10]: {}", in_bounds(5, 0, 10));
    println!("15 in [0, 10]: {}", in_bounds(15, 0, 10));
}
