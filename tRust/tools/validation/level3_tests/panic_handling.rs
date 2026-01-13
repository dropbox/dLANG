// Level 3 Test: Panic handling
// Tests: catch_unwind, panic hooks, Result handling

use std::panic;

fn might_panic(should_panic: bool) -> i32 {
    if should_panic {
        panic!("intentional panic");
    }
    42
}

fn main() {
    // catch_unwind - successful case
    println!("=== catch_unwind ===");
    let result = panic::catch_unwind(|| {
        might_panic(false)
    });
    match result {
        Ok(val) => println!("Success: {}", val),
        Err(_) => println!("Caught panic"),
    }

    // catch_unwind - panic case
    let result = panic::catch_unwind(|| {
        might_panic(true)
    });
    match result {
        Ok(val) => println!("Success: {}", val),
        Err(_) => println!("Caught panic"),
    }

    // Result handling
    println!("\n=== Result Handling ===");
    let ok_result: Result<i32, &str> = Ok(42);
    let err_result: Result<i32, &str> = Err("error message");

    println!("ok.is_ok(): {}", ok_result.is_ok());
    println!("ok.is_err(): {}", ok_result.is_err());
    println!("err.is_ok(): {}", err_result.is_ok());
    println!("err.is_err(): {}", err_result.is_err());

    println!("ok.unwrap(): {}", ok_result.unwrap());
    println!("err.unwrap_or(0): {}", err_result.unwrap_or(0));
    println!("err.unwrap_or_else(|_| 99): {}", err_result.unwrap_or_else(|_| 99));

    // Option handling
    println!("\n=== Option Handling ===");
    let some_val: Option<i32> = Some(42);
    let none_val: Option<i32> = None;

    println!("some.is_some(): {}", some_val.is_some());
    println!("some.is_none(): {}", some_val.is_none());
    println!("none.is_some(): {}", none_val.is_some());
    println!("none.is_none(): {}", none_val.is_none());

    println!("some.unwrap(): {}", some_val.unwrap());
    println!("none.unwrap_or(0): {}", none_val.unwrap_or(0));
    println!("none.unwrap_or_default(): {}", none_val.unwrap_or_default());

    // map/and_then chains
    println!("\n=== Combinators ===");
    let x: Option<i32> = Some(2);
    let mapped = x.map(|v| v * 3).map(|v| v + 1);
    println!("Some(2).map(|v| v*3).map(|v| v+1): {:?}", mapped);

    let chained = x
        .and_then(|v| if v > 0 { Some(v * 10) } else { None })
        .and_then(|v| Some(v + 5));
    println!("chained: {:?}", chained);

    // ? operator simulation
    println!("\n=== Error Propagation ===");
    fn divide(a: i32, b: i32) -> Result<i32, String> {
        if b == 0 {
            Err("division by zero".to_string())
        } else {
            Ok(a / b)
        }
    }

    fn compute(a: i32, b: i32, c: i32) -> Result<i32, String> {
        let x = divide(a, b)?;
        let y = divide(x, c)?;
        Ok(y)
    }

    println!("compute(100, 5, 2): {:?}", compute(100, 5, 2));
    println!("compute(100, 0, 2): {:?}", compute(100, 0, 2));
    println!("compute(100, 5, 0): {:?}", compute(100, 5, 0));

    // Multiple catches
    println!("\n=== Multiple Panics ===");
    for i in 0..3 {
        let result = panic::catch_unwind(move || {
            if i % 2 == 0 {
                i * 10
            } else {
                panic!("odd number: {}", i)
            }
        });
        match result {
            Ok(val) => println!("i={}: success={}", i, val),
            Err(_) => println!("i={}: caught panic", i),
        }
    }

    println!("\nPanic handling complete");
}
