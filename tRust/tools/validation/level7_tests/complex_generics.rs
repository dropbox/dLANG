// Complex generics stress test
use std::marker::PhantomData;
use std::collections::HashMap;

trait Processor<T> {
    type Output;
    fn process(&self, input: T) -> Self::Output;
}

struct Chain<A, B, T, U, V>
where
    A: Processor<T, Output = U>,
    B: Processor<U, Output = V>,
{
    first: A,
    second: B,
    _marker: PhantomData<(T, U, V)>,
}

impl<A, B, T, U, V> Processor<T> for Chain<A, B, T, U, V>
where
    A: Processor<T, Output = U>,
    B: Processor<U, Output = V>,
{
    type Output = V;

    fn process(&self, input: T) -> V {
        self.second.process(self.first.process(input))
    }
}

struct NestedWrapper<T, const N: usize> {
    data: [Option<Box<T>>; N],
}

impl<T: Clone, const N: usize> NestedWrapper<T, N> {
    fn new() -> Self {
        Self { data: std::array::from_fn(|_| None) }
    }
}

type ComplexType<'a> = HashMap<String, Vec<Box<dyn Processor<i32, Output = String> + 'a>>>;

fn main() {
    let _wrapper: NestedWrapper<Vec<String>, 10> = NestedWrapper::new();
    println!("Complex generics compiled successfully");
}
