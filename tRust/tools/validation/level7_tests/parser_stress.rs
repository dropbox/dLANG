// Parser stress test with unusual but valid syntax
#![allow(unused_parens)]
#![allow(unused_braces)]
fn main() {
    // Nested blocks
    {{{{{let _x = 1;}}}}}

    // Complex expressions
    let _ = (((((1 + 2) * 3) - 4) / 5) % 6);

    // Many closures
    let f = |x| move |y| move |z| x + y + z;
    assert_eq!(f(1)(2)(3), 6);

    // Match with many arms
    let n = 5;
    let _ = match n {
        0 => "zero",
        1 => "one",
        2 => "two",
        3 => "three",
        4 => "four",
        5 => "five",
        6 => "six",
        7 => "seven",
        8 => "eight",
        9 => "nine",
        _ => "many",
    };

    // Complex pattern matching
    let tuple = (Some(1), Some(2), Some(3));
    if let (Some(a), Some(b), Some(c)) = tuple {
        assert_eq!(a + b + c, 6);
    }

    println!("Parser stress test passed");
}
