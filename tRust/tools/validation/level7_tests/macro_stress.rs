// Macro stress test
macro_rules! nested {
    ($x:expr) => { $x };
    ($x:expr, $($rest:expr),+) => {
        nested!($x) + nested!($($rest),+)
    };
}

macro_rules! recursive_sum {
    ($acc:expr;) => { $acc };
    ($acc:expr; $head:expr $(, $tail:expr)*) => {
        recursive_sum!($acc + $head; $($tail),*)
    };
}

macro_rules! make_fn {
    ($name:ident, $val:expr) => {
        fn $name() -> i32 { $val }
    };
}

make_fn!(one, 1);
make_fn!(two, 2);
make_fn!(three, 3);

macro_rules! count_args {
    () => { 0 };
    ($head:tt $($tail:tt)*) => { 1 + count_args!($($tail)*) };
}

fn main() {
    assert_eq!(nested!(1, 2, 3, 4, 5), 15);
    assert_eq!(recursive_sum!(0; 1, 2, 3, 4, 5), 15);
    assert_eq!(one() + two() + three(), 6);
    assert_eq!(count_args!(a b c d e), 5);
    println!("Macro stress test passed");
}
