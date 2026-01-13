// Level 3 Test: Collections
// Tests: Vec, HashMap, BTreeMap, HashSet, BTreeSet, VecDeque

use std::collections::{HashMap, BTreeMap, HashSet, BTreeSet, VecDeque};

fn main() {
    // Vec
    println!("=== Vec ===");
    let mut v: Vec<i32> = vec![1, 2, 3, 4, 5];
    println!("initial: {:?}", v);
    v.push(6);
    println!("after push(6): {:?}", v);
    let popped = v.pop();
    println!("pop: {:?}, vec: {:?}", popped, v);
    v.insert(0, 0);
    println!("after insert(0, 0): {:?}", v);
    let removed = v.remove(3);
    println!("remove(3): {}, vec: {:?}", removed, v);
    println!("len: {}, capacity: {}", v.len(), v.capacity());
    println!("first: {:?}, last: {:?}", v.first(), v.last());
    println!("get(2): {:?}, get(100): {:?}", v.get(2), v.get(100));

    // Vec iteration
    print!("iter: ");
    for x in &v {
        print!("{} ", x);
    }
    println!();

    // Vec sorting
    let mut unsorted = vec![3, 1, 4, 1, 5, 9, 2, 6];
    unsorted.sort();
    println!("sorted: {:?}", unsorted);
    unsorted.reverse();
    println!("reversed: {:?}", unsorted);

    // HashMap
    println!("\n=== HashMap ===");
    let mut map: HashMap<&str, i32> = HashMap::new();
    map.insert("one", 1);
    map.insert("two", 2);
    map.insert("three", 3);
    println!("get 'two': {:?}", map.get("two"));
    println!("get 'four': {:?}", map.get("four"));
    println!("contains 'one': {}", map.contains_key("one"));
    println!("len: {}", map.len());

    // HashMap iteration (sorted for determinism)
    let mut entries: Vec<_> = map.iter().collect();
    entries.sort_by_key(|&(k, _)| *k);
    print!("entries: ");
    for (k, v) in entries {
        print!("({}, {}) ", k, v);
    }
    println!();

    // BTreeMap (ordered)
    println!("\n=== BTreeMap ===");
    let mut btree: BTreeMap<i32, &str> = BTreeMap::new();
    btree.insert(3, "three");
    btree.insert(1, "one");
    btree.insert(4, "four");
    btree.insert(1, "ONE"); // overwrite
    btree.insert(5, "five");
    print!("ordered entries: ");
    for (k, v) in &btree {
        print!("({}, {}) ", k, v);
    }
    println!();
    println!("first: {:?}", btree.first_key_value());
    println!("last: {:?}", btree.last_key_value());

    // HashSet
    println!("\n=== HashSet ===");
    let mut set: HashSet<i32> = HashSet::new();
    set.insert(1);
    set.insert(2);
    set.insert(3);
    set.insert(2); // duplicate
    println!("len: {}", set.len());
    println!("contains 2: {}", set.contains(&2));
    println!("contains 5: {}", set.contains(&5));

    // Set operations
    let set_a: HashSet<i32> = [1, 2, 3].into_iter().collect();
    let set_b: HashSet<i32> = [2, 3, 4].into_iter().collect();
    let mut union: Vec<_> = set_a.union(&set_b).copied().collect();
    union.sort();
    let mut intersection: Vec<_> = set_a.intersection(&set_b).copied().collect();
    intersection.sort();
    let mut difference: Vec<_> = set_a.difference(&set_b).copied().collect();
    difference.sort();
    println!("union: {:?}", union);
    println!("intersection: {:?}", intersection);
    println!("difference: {:?}", difference);

    // BTreeSet (ordered)
    println!("\n=== BTreeSet ===");
    let btree_set: BTreeSet<i32> = [5, 3, 1, 4, 2].into_iter().collect();
    print!("ordered: ");
    for x in &btree_set {
        print!("{} ", x);
    }
    println!();

    // VecDeque
    println!("\n=== VecDeque ===");
    let mut deque: VecDeque<i32> = VecDeque::new();
    deque.push_back(1);
    deque.push_back(2);
    deque.push_front(0);
    println!("deque: {:?}", deque);
    println!("pop_front: {:?}", deque.pop_front());
    println!("pop_back: {:?}", deque.pop_back());
    println!("after pops: {:?}", deque);
}
