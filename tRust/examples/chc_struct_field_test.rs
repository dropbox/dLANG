// Regression test: CHC transition encoding must not treat struct fields as
// checked-arithmetic tuple projections.
//
// This file intentionally contains branching control-flow so that the verifier
// takes the CHC path (not the straight-line SP path).
//
// Expected: VERIFIED

#![allow(dead_code)]

pub struct Pair {
    pub a: usize,
    pub b: usize,
}

#[ensures("result.a == x")]
#[ensures("result.b == y")]
pub fn make_pair(flag: bool, x: usize, y: usize) -> Pair {
    if flag {
        Pair { a: x, b: y }
    } else {
        Pair { a: x, b: y }
    }
}

#[ensures("result.a == x")]
#[ensures("result.b == y + 1")]
#[requires("y < 1000")]
pub fn make_pair_offset(flag: bool, x: usize, y: usize) -> Pair {
    if flag {
        Pair { a: x, b: y + 1 }
    } else {
        Pair { a: x, b: y + 1 }
    }
}

fn main() {
    let p = make_pair(true, 10, 20);
    println!("pair = ({}, {})", p.a, p.b);
    let q = make_pair_offset(false, 1, 2);
    println!("pair_offset = ({}, {})", q.a, q.b);
}
