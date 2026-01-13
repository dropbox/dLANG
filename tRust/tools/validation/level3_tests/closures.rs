// Level 3 Test: Closures and iterators
// Tests: Fn, FnMut, FnOnce, iterator adapters, collect

fn main() {
    // Basic closures
    println!("=== Basic Closures ===");
    let add = |a, b| a + b;
    println!("add(2, 3) = {}", add(2, 3));

    let x = 10;
    let add_x = |y| x + y;
    println!("add_x(5) = {}", add_x(5));

    // Closure with explicit types
    let multiply: fn(i32, i32) -> i32 = |a, b| a * b;
    println!("multiply(4, 5) = {}", multiply(4, 5));

    // FnOnce - consumes captured variable
    println!("\n=== FnOnce ===");
    let s = String::from("hello");
    let consume = move || {
        println!("Consuming: {}", s);
        s
    };
    let result = consume();
    println!("Result: {}", result);

    // FnMut - mutates captured variable
    println!("\n=== FnMut ===");
    let mut counter = 0;
    let mut increment = || {
        counter += 1;
        counter
    };
    println!("increment: {}", increment());
    println!("increment: {}", increment());
    println!("increment: {}", increment());

    // Fn - only reads captured variable
    println!("\n=== Fn ===");
    let data = vec![1, 2, 3];
    let get_len = || data.len();
    println!("get_len: {}", get_len());
    println!("get_len again: {}", get_len());

    // Higher-order functions
    println!("\n=== Higher-Order Functions ===");
    fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
        f(x)
    }
    let double = |x| x * 2;
    println!("apply(double, 5) = {}", apply(double, 5));

    fn create_adder(n: i32) -> impl Fn(i32) -> i32 {
        move |x| x + n
    }
    let add5 = create_adder(5);
    println!("add5(10) = {}", add5(10));

    // Iterators
    println!("\n=== Iterators ===");
    let v = vec![1, 2, 3, 4, 5];

    // map
    let doubled: Vec<_> = v.iter().map(|x| x * 2).collect();
    println!("map (*2): {:?}", doubled);

    // filter
    let evens: Vec<_> = v.iter().filter(|&x| x % 2 == 0).copied().collect();
    println!("filter (even): {:?}", evens);

    // filter_map
    let positive_squares: Vec<_> = vec![-2, -1, 0, 1, 2]
        .into_iter()
        .filter_map(|x| if x > 0 { Some(x * x) } else { None })
        .collect();
    println!("filter_map: {:?}", positive_squares);

    // fold
    let sum: i32 = v.iter().fold(0, |acc, x| acc + x);
    println!("fold (sum): {}", sum);

    // reduce
    let product: Option<i32> = v.iter().copied().reduce(|acc, x| acc * x);
    println!("reduce (product): {:?}", product);

    // enumerate
    print!("enumerate: ");
    for (i, x) in v.iter().enumerate() {
        print!("({}, {}) ", i, x);
    }
    println!();

    // zip
    let a = vec![1, 2, 3];
    let b = vec!['a', 'b', 'c'];
    let zipped: Vec<_> = a.iter().zip(b.iter()).collect();
    println!("zip: {:?}", zipped);

    // chain
    let chained: Vec<_> = vec![1, 2].iter().chain(vec![3, 4].iter()).copied().collect();
    println!("chain: {:?}", chained);

    // take/skip
    let taken: Vec<_> = (0..10).take(3).collect();
    println!("take(3): {:?}", taken);
    let skipped: Vec<_> = (0..10).skip(7).collect();
    println!("skip(7): {:?}", skipped);

    // take_while/skip_while
    let taken_while: Vec<_> = (0..10).take_while(|&x| x < 4).collect();
    println!("take_while(<4): {:?}", taken_while);

    // flatten
    let nested = vec![vec![1, 2], vec![3, 4], vec![5]];
    let flat: Vec<_> = nested.iter().flatten().copied().collect();
    println!("flatten: {:?}", flat);

    // any/all
    println!("any(>3): {}", v.iter().any(|&x| x > 3));
    println!("all(>0): {}", v.iter().all(|&x| x > 0));

    // find/position
    println!("find(>3): {:?}", v.iter().find(|&&x| x > 3));
    println!("position(==3): {:?}", v.iter().position(|&x| x == 3));

    // min/max
    println!("min: {:?}", v.iter().min());
    println!("max: {:?}", v.iter().max());

    // count/sum
    println!("count: {}", v.iter().count());
    println!("sum: {}", v.iter().sum::<i32>());

    // partition
    let (evens, odds): (Vec<&i32>, Vec<&i32>) = v.iter().partition(|&&x| x % 2 == 0);
    println!("partition: evens={:?}, odds={:?}", evens, odds);

    // rev
    let reversed: Vec<_> = v.iter().rev().copied().collect();
    println!("rev: {:?}", reversed);
}
