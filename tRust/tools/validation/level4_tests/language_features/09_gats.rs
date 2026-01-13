// Level 4.1: Generic Associated Types (GATs)
// Tests GATs in traits

// Basic GAT
trait Container {
    type Item<'a> where Self: 'a;

    fn get<'a>(&'a self) -> Self::Item<'a>;
}

struct StringContainer(String);

impl Container for StringContainer {
    type Item<'a> = &'a str where Self: 'a;

    fn get<'a>(&'a self) -> &'a str {
        &self.0
    }
}

// GAT with type parameter
trait Producer {
    type Output<T>;

    fn produce<T: Default>(&self) -> Self::Output<T>;
}

struct VecProducer;

impl Producer for VecProducer {
    type Output<T> = Vec<T>;

    fn produce<T: Default>(&self) -> Vec<T> {
        vec![T::default()]
    }
}

// GAT with multiple parameters
trait Mapper {
    type Mapped<'a, T> where Self: 'a, T: 'a;

    fn map<'a, T>(&'a self, value: T) -> Self::Mapped<'a, T>;
}

struct OptionMapper;

impl Mapper for OptionMapper {
    type Mapped<'a, T> = Option<T> where T: 'a;

    fn map<'a, T>(&'a self, value: T) -> Option<T> {
        Some(value)
    }
}

// Streaming iterator pattern (classic GAT use case)
trait StreamingIterator {
    type Item<'a> where Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

struct WindowIter<'data> {
    data: &'data [i32],
    position: usize,
    window_size: usize,
}

impl<'data> WindowIter<'data> {
    fn new(data: &'data [i32], window_size: usize) -> Self {
        WindowIter { data, position: 0, window_size }
    }
}

impl<'data> StreamingIterator for WindowIter<'data> {
    type Item<'a> = &'a [i32] where Self: 'a;

    fn next<'a>(&'a mut self) -> Option<&'a [i32]> {
        if self.position + self.window_size <= self.data.len() {
            let result = &self.data[self.position..self.position + self.window_size];
            self.position += 1;
            Some(result)
        } else {
            None
        }
    }
}

// GAT with bounds
trait BoundedGat {
    type Value<T: Clone>;

    fn wrap<T: Clone>(&self, val: T) -> Self::Value<T>;
}

struct Wrapper;

impl BoundedGat for Wrapper {
    type Value<T: Clone> = (T, T);

    fn wrap<T: Clone>(&self, val: T) -> (T, T) {
        (val.clone(), val)
    }
}

// GAT returning reference types
trait RefProvider {
    type Ref<'a>: std::fmt::Debug where Self: 'a;

    fn provide<'a>(&'a self) -> Self::Ref<'a>;
}

struct Numbers(Vec<i32>);

impl RefProvider for Numbers {
    type Ref<'a> = &'a [i32] where Self: 'a;

    fn provide<'a>(&'a self) -> &'a [i32] {
        &self.0
    }
}

fn main() {
    // Basic GAT
    let sc = StringContainer("Hello, GATs!".to_string());
    println!("Container: {}", sc.get());

    // GAT with type parameter
    let vp = VecProducer;
    let produced: Vec<i32> = vp.produce();
    println!("Produced: {:?}", produced);

    // GAT with multiple parameters
    let om = OptionMapper;
    let mapped: Option<i32> = om.map(42);
    println!("Mapped: {:?}", mapped);

    // Streaming iterator
    let data = [1, 2, 3, 4, 5];
    let mut iter = WindowIter::new(&data, 3);
    print!("Windows: ");
    while let Some(window) = iter.next() {
        print!("{:?} ", window);
    }
    println!();

    // GAT with bounds
    let w = Wrapper;
    let wrapped: (String, String) = w.wrap("test".to_string());
    println!("Wrapped: {:?}", wrapped);

    // RefProvider
    let nums = Numbers(vec![10, 20, 30]);
    println!("Provided: {:?}", nums.provide());

    println!("All GAT tests passed!");
}
