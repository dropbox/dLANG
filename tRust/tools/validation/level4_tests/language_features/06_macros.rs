// Level 4.1: macro_rules! Macros
// Tests declarative macro syntax and patterns

// Basic macro
macro_rules! say_hello {
    () => {
        println!("Hello!")
    };
}

// Macro with arguments
macro_rules! print_val {
    ($val:expr) => {
        println!("Value: {}", $val)
    };
}

// Macro with multiple arguments
macro_rules! min {
    ($a:expr, $b:expr) => {
        if $a < $b { $a } else { $b }
    };
}

// Variadic macro
macro_rules! print_all {
    ($($x:expr),*) => {
        $(println!("{}", $x);)*
    };
}

// Macro with repetition and separator
macro_rules! make_vec {
    ($($x:expr),* $(,)?) => {
        {
            let mut v = Vec::new();
            $(v.push($x);)*
            v
        }
    };
}

// Macro with different fragment types
macro_rules! declare_fn {
    ($name:ident, $ret:ty, $body:expr) => {
        fn $name() -> $ret {
            $body
        }
    };
}

declare_fn!(get_five, i32, 5);
declare_fn!(get_hello, &'static str, "hello");

// Macro with pattern matching
macro_rules! calculate {
    (add $a:expr, $b:expr) => { $a + $b };
    (sub $a:expr, $b:expr) => { $a - $b };
    (mul $a:expr, $b:expr) => { $a * $b };
}

// Recursive macro
macro_rules! count {
    () => { 0 };
    ($head:expr) => { 1 };
    ($head:expr, $($tail:expr),*) => { 1 + count!($($tail),*) };
}

// Macro generating struct
macro_rules! make_struct {
    ($name:ident { $($field:ident: $ty:ty),* $(,)? }) => {
        struct $name {
            $($field: $ty),*
        }
    };
}

make_struct!(Point { x: i32, y: i32 });

// Macro with tt (token tree)
macro_rules! with_tt {
    ($($tt:tt)*) => {
        stringify!($($tt)*)
    };
}

// Nested repetition
macro_rules! nested {
    ($([$($x:expr),*]),*) => {
        vec![$(vec![$($x),*]),*]
    };
}

// Macro exporting expressions
macro_rules! expr_list {
    ($($e:expr),*) => {
        [$($e),*]
    };
}

fn main() {
    // Basic macro
    say_hello!();

    // With argument
    print_val!(42);

    // Multiple arguments
    println!("Min: {}", min!(5, 3));

    // Variadic
    print_all!(1, 2, 3);

    // Make vec
    let v = make_vec![10, 20, 30];
    println!("Vec: {:?}", v);

    // Generated functions
    println!("Five: {}", get_five());
    println!("Hello: {}", get_hello());

    // Pattern matching macro
    println!("Add: {}", calculate!(add 10, 5));
    println!("Sub: {}", calculate!(sub 10, 5));
    println!("Mul: {}", calculate!(mul 10, 5));

    // Recursive macro
    println!("Count: {}", count!(1, 2, 3, 4, 5));

    // Generated struct
    let p = Point { x: 10, y: 20 };
    println!("Point: ({}, {})", p.x, p.y);

    // Token tree
    println!("TT: {}", with_tt!(hello world));

    // Nested repetition
    let nested_vec = nested![[1, 2], [3, 4, 5]];
    println!("Nested: {:?}", nested_vec);

    // Expression list
    let arr = expr_list![1, 2, 3];
    println!("Array: {:?}", arr);

    println!("All macro tests passed!");
}
