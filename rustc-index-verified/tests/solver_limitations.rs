//! Minimal reproduction cases for solver limitations L1-L13
//! Run with: ~/tRust/bin/trustc tests/solver_limitations.rs --crate-type lib --edition 2021 --cfg trust_verify
//!
//! Status as of 2026-01-05 (Worker #279):
//! - L1: VERIFIED ✓ (fixed in #304)
//! - L2: VERIFIED ✓ (fixed again in #309)
//! - L3: VERIFIED ✓ - automatic pure method inlining (tRust #347-352)
//!   Just mark method with #[pure], no #[pure_returns] needed for simple getters
//! - L4a: VERIFIED ✓
//! - L4b: VERIFIED ✓ (was inconsistent, now works)
//! - L5: VERIFIED ✓ - predicate combinators (tRust #356)
//!   is_some_and(), is_ok_and(), is_err_and(), is_none_or(), is_ok_or(), is_err_or() supported
//!   Also: result.is_some() works directly for Option (no predicate combinator needed)
//! - L5d: VERIFIED ✓ - result.is_some() with old() on mutable self (Worker #257)
//!   This enables pop()-like patterns: `old(v.len()) > 0 ==> result.is_some()`
//! - L5e: DISPROVEN - result.is_some() through struct delegation (Worker #257)
//!   The solver cannot track old(self.len()) when len() delegates to self.raw.len()
//! - L6: VERIFIED ✓
//! - L7: VERIFIED ✓ for direct struct construction (Worker #36)
//! - L7d: VERIFIED ✓ with smallvec! macro (Worker #37)
//! - L7e: VERIFIED ✓ - helper function indirection (tRust #354)
//!   Mark helper with #[pure], verifier extracts implicit postconditions from struct construction
//! - L8: VERIFIED ✓ - nonlinear arithmetic now supported (tRust #339+)
//!   Automatic QF_NIA logic selection when multiplication/division/modulo detected in specs
//!   Example: `#[ensures("result == a * b")]` now verifies
//! - L9: DISPROVEN - associated constants (T::EMPTY, T::DOMAIN_SIZE) not supported
//! - L10: DISPROVEN - trait method identity (generic I::new(n).index() == n) not provable
//! - L11: DISPROVEN - enum variant constants (e.g. `None`) not supported in specs
//!   Workaround: reason about `Option` via predicate combinators like `is_some_and`.
//! - L12: DISPROVEN - `result.method()` postconditions on structs with `PhantomData<T>` can trigger
//!   Z3 encoding failures ("unknown constant unit") in some cases (see ROADMAP.md, Worker #192).
//! - L13: DISPROVEN - postcondition flow through struct field paths (Worker #258)
//!   When function A has postcondition on `self.inner.field` and function B calls A then uses
//!   `self.inner.method()`, the solver cannot connect A's postcondition to B's precondition.
//!   Error: "unknown constant _N_fX.field_name" - the solver loses track of field values through
//!   nested struct access. This blocks GrowableBitSet::{insert,remove} postconditions.

#![allow(dead_code)]

// L1: self in cast - VERIFIED (fixed in tRust #304)
#[cfg_attr(trust_verify, ensures("result == x as usize"))]
pub fn l1_cast(x: u32) -> usize {
    x as usize
}

// L2: result.field - VERIFIED (fixed in tRust #304/#305)
pub struct Simple {
    pub value: usize,
}
#[cfg_attr(trust_verify, ensures("result.value == 42"))]
pub fn l2_field() -> Simple {
    Simple { value: 42 }
}

// L3: result.method() - VERIFIED with automatic pure method inlining (tRust #347-352)
// Just mark the method with #[pure] - the verifier automatically extracts the return value from MIR.
// #[pure_returns] is still available as explicit fallback but rarely needed for simple getters.
pub struct Wrap(pub usize);
impl Wrap {
    #[cfg_attr(trust_verify, pure)]
    pub fn get(&self) -> usize {
        self.0
    }
}
#[cfg_attr(trust_verify, ensures("result.get() == 42"))]
pub fn l3_method() -> Wrap {
    Wrap(42)
}

// L3 with #[pure] only: Tests automatic inlining (no #[pure_returns] needed)
// tRust #347-352 implemented automatic pure method inlining from MIR
pub struct WrapNoAnnotation(pub usize);
impl WrapNoAnnotation {
    #[cfg_attr(trust_verify, pure)]
    pub fn get_no_anno(&self) -> usize {
        self.0
    }
}
#[cfg_attr(trust_verify, ensures("result.get_no_anno() == 42"))]
pub fn l3_method_no_annotation() -> WrapNoAnnotation {
    WrapNoAnnotation(42)
}

// L4a: self.field with Vec - VERIFIED
pub struct VecBox {
    pub items: Vec<i32>,
}
impl VecBox {
    #[cfg_attr(trust_verify, ensures("self.items.len() == old(self.items.len()) + 1"))]
    pub fn push(&mut self, x: i32) {
        self.items.push(x);
    }
}

// L4b: self.field with HashMap - VERIFIED (was inconsistent, now works)
pub struct MapBox {
    pub data: std::collections::HashMap<i32, i32>,
}
impl MapBox {
    #[cfg_attr(trust_verify, ensures("self.data.is_empty()"))]
    pub fn clear(&mut self) {
        self.data.clear();
    }
}

// L5: predicate combinators - VERIFIED (tRust #356)
// Predicate combinators like is_some_and(), is_ok_and() now supported.
// Full closure support not implemented, but these common patterns work.
#[cfg_attr(trust_verify, ensures("result.is_some_and(|x| x > 0)"))]
pub fn l5_predicate_combinator() -> Option<i32> {
    Some(42)
}

// L5b: result.is_some() without predicate combinator - VERIFIED (Worker #255)
// Plain is_some() also works when the Option is directly constructed
#[cfg_attr(trust_verify, ensures("result.is_some()"))]
pub fn l5b_option_is_some() -> Option<i32> {
    Some(42)
}

// L5c: result.is_some() with conditional - VERIFIED (Worker #255)
#[cfg_attr(trust_verify, ensures("v > 0 ==> result.is_some()"))]
#[cfg_attr(trust_verify, ensures("v == 0 ==> !result.is_some()"))]
pub fn l5c_option_conditional(v: usize) -> Option<usize> {
    if v > 0 {
        Some(v)
    } else {
        None
    }
}

// L5d: result.is_some() with old() on mutable self - VERIFIED (Worker #257)
// This proves pop()-like patterns can now be verified with is_some() postconditions
#[cfg_attr(trust_verify, ensures("old(v.len()) > 0 ==> result.is_some()"))]
pub fn l5d_option_with_old(v: &mut Vec<i32>) -> Option<i32> {
    v.pop()
}

// L5e: result.is_some() through struct delegation - DISPROVEN (Worker #257)
// The solver cannot track old(self.len()) when len() delegates to self.raw.len()
// This blocks IndexVec::pop() postconditions even though L5d works for direct Vec::pop()
pub struct WrapVec {
    pub raw: Vec<i32>,
}
impl WrapVec {
    #[cfg_attr(trust_verify, pure)]
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    #[cfg_attr(trust_verify, pure)]
    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    #[cfg_attr(trust_verify, ensures("old(self.len()) > 0 ==> result.is_some()"))]
    pub fn pop(&mut self) -> Option<i32> {
        self.raw.pop()
    }
}

// L6: deep path (3 levels) - VERIFIED
pub struct L1 {
    pub l2: L2,
}
pub struct L2 {
    pub l3: L3,
}
pub struct L3 {
    pub v: usize,
}
#[cfg_attr(trust_verify, ensures("result.l2.l3.v == 42"))]
pub fn l6_deep() -> L1 {
    L1 {
        l2: L2 { l3: L3 { v: 42 } },
    }
}

// L7: result.field with same name as parameter - REGRESSION TEST
// This pattern temporarily regressed in rustc-index-verified (Worker #32-35),
// but verifies again as of Worker #36 (tRust #309, kani_fast 736e57c).
pub struct BitSetLike {
    pub domain_size: usize,
    pub words: Vec<usize>,
}
#[cfg_attr(trust_verify, ensures("result.domain_size == domain_size"))]
pub fn l7_same_name(domain_size: usize) -> BitSetLike {
    let num_words = domain_size.div_ceil(64);
    BitSetLike {
        domain_size,
        words: vec![0; num_words],
    }
}

// L7b: simpler version without computation
#[cfg_attr(trust_verify, ensures("result.domain_size == domain_size"))]
pub fn l7b_same_name_simple(domain_size: usize) -> BitSetLike {
    BitSetLike {
        domain_size,
        words: Vec::new(),
    }
}

// L7c: with generic type parameter (like BitSet<T>)
pub struct GenericSet<T> {
    pub domain_size: usize,
    pub words: Vec<usize>,
    pub _marker: std::marker::PhantomData<T>,
}
#[cfg_attr(trust_verify, ensures("result.domain_size == domain_size"))]
pub fn l7c_generic<T>(domain_size: usize) -> GenericSet<T> {
    let num_words = domain_size.div_ceil(64);
    GenericSet {
        domain_size,
        words: vec![0; num_words],
        _marker: std::marker::PhantomData,
    }
}

// L7d: with smallvec (exact BitSet pattern) - VERIFIED (Worker #37)
// NOTE: This requires smallvec dependency
#[cfg(feature = "smallvec_test")]
pub mod smallvec_test {
    use smallvec::{smallvec, SmallVec};
    pub struct SmallVecSet<T> {
        pub domain_size: usize,
        pub words: SmallVec<[usize; 2]>,
        pub _marker: std::marker::PhantomData<T>,
    }
    #[cfg_attr(trust_verify, ensures("result.domain_size == domain_size"))]
    pub fn l7d_smallvec<T>(domain_size: usize) -> SmallVecSet<T> {
        let num_words = (domain_size + 63) / 64;
        SmallVecSet {
            domain_size,
            words: smallvec![0; num_words],
            _marker: std::marker::PhantomData,
        }
    }
}

// L7e: helper function indirection - VERIFIED (tRust #354)
// Pure struct constructors now generate implicit postconditions.
// Mark the helper with #[pure] and the verifier extracts field->param mappings.
pub struct HelperResult {
    pub value: usize,
}
#[cfg_attr(trust_verify, pure)]
fn helper_new(v: usize) -> HelperResult {
    HelperResult { value: v }
}
#[cfg_attr(trust_verify, ensures("result.value == v"))]
pub fn l7e_helper_indirection(v: usize) -> HelperResult {
    helper_new(v)
}

// L8: nonlinear arithmetic - VERIFIED (tRust #339+)
// Multiplication in specs now works with automatic QF_NIA logic selection.
// Simple multiplication specs verify; complex expressions with Vec allocation may still be tricky.
#[cfg_attr(trust_verify, requires("a >= 0 && a <= 1000"))]
#[cfg_attr(trust_verify, requires("b >= 0 && b <= 1000"))]
#[cfg_attr(trust_verify, ensures("result == a * b"))]
pub fn l8_multiply(a: i64, b: i64) -> i64 {
    a * b
}

// L8b: division in specs - VERIFIED (tRust #339+)
#[cfg_attr(trust_verify, requires("b != 0"))]
#[cfg_attr(trust_verify, ensures("result == a / b"))]
pub fn l8b_divide(a: i64, b: i64) -> i64 {
    a / b
}

// L8c: modulo in specs - VERIFIED (tRust #339+)
#[cfg_attr(trust_verify, requires("b != 0"))]
#[cfg_attr(trust_verify, ensures("result == a % b"))]
pub fn l8c_modulo(a: i64, b: i64) -> i64 {
    a % b
}

// L9: associated constants - DISPROVEN
pub trait AssocConst {
    const C: usize;
}

pub struct Assoc42;
impl AssocConst for Assoc42 {
    const C: usize = 42;
}

#[cfg_attr(trust_verify, ensures("result == T::C"))]
pub fn l9_assoc_const<T: AssocConst>() -> usize {
    T::C
}

// L10: trait method identity for generic trait methods - DISPROVEN
pub trait IdxLike: Copy {
    fn new(idx: usize) -> Self;
    fn index(self) -> usize;
}

impl IdxLike for usize {
    fn new(idx: usize) -> Self {
        idx
    }
    fn index(self) -> usize {
        self
    }
}

#[cfg_attr(trust_verify, ensures("result == x"))]
pub fn l10_trait_method_identity<I: IdxLike>(x: usize) -> usize {
    I::new(x).index()
}

// L11: enum variant constants in specs - DISPROVEN
#[cfg_attr(trust_verify, ensures("result == None"))]
pub fn l11_option_none_constant() -> Option<i32> {
    None
}

// L11 workaround: avoid `None` in the spec - VERIFIED
#[cfg_attr(trust_verify, ensures("!result.is_some_and(|_| true)"))]
pub fn l11_option_none_workaround() -> Option<i32> {
    None
}

// L12: PhantomData + result.method() postconditions - DISPROVEN (Z3 encoding failure)
pub struct PhantomEmpty<T> {
    pub words: Vec<usize>,
    pub _marker: std::marker::PhantomData<T>,
}
impl<T> PhantomEmpty<T> {
    #[cfg_attr(trust_verify, pure)]
    pub fn is_empty(&self) -> bool {
        self.words.is_empty()
    }
}

#[cfg_attr(trust_verify, ensures("result.is_empty()"))]
pub fn l12_phantomdata_result_method<T>() -> PhantomEmpty<T> {
    PhantomEmpty {
        words: Vec::new(),
        _marker: std::marker::PhantomData,
    }
}

// L12 workaround: reason about fields directly (no result.method() call)
#[cfg_attr(trust_verify, ensures("result.words.is_empty()"))]
pub fn l12_phantomdata_workaround<T>() -> PhantomEmpty<T> {
    PhantomEmpty {
        words: Vec::new(),
        _marker: std::marker::PhantomData,
    }
}

// L13: postcondition flow through struct field paths - DISPROVEN (Worker #258)
// The solver cannot flow postconditions from an inner method to an outer method's
// precondition when accessing through nested struct fields.
// This blocks GrowableBitSet::{insert,remove} verification.
pub struct InnerBitSet {
    pub domain_size: usize,
}
impl InnerBitSet {
    #[cfg_attr(trust_verify, requires("elem < self.domain_size"))]
    #[cfg_attr(trust_verify, ensures("result == true"))]
    pub fn insert(&mut self, elem: usize) -> bool {
        assert!(elem < self.domain_size);
        true // simplified
    }
}

pub struct OuterGrowable {
    pub inner: InnerBitSet,
}
impl OuterGrowable {
    // ensure() establishes postcondition on self.inner.domain_size
    #[cfg_attr(trust_verify, ensures("self.inner.domain_size >= min_size"))]
    pub fn ensure(&mut self, min_size: usize) {
        if self.inner.domain_size < min_size {
            self.inner.domain_size = min_size;
        }
    }

    // L13: Cannot verify - solver can't connect ensure() postcondition to inner.insert() precondition
    // Error: "unknown constant _N_fX.domain_size"
    // The ensure() postcondition establishes `self.inner.domain_size >= elem + 1`
    // but the solver can't prove `elem < self.inner.domain_size` for the inner.insert() call.
    // Uncomment the ensures attribute to reproduce the DISPROVEN result:
    // #[cfg_attr(trust_verify, ensures("result == true"))]
    pub fn insert(&mut self, elem: usize) -> bool {
        self.ensure(elem + 1);
        self.inner.insert(elem)
    }
}

// Baseline (must always work)
#[cfg_attr(trust_verify, ensures("result == x"))]
pub fn baseline(x: usize) -> usize {
    x
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_all() {
        assert_eq!(l1_cast(42), 42);
        assert_eq!(l2_field().value, 42);
        assert_eq!(l3_method().get(), 42);
        assert_eq!(l3_method_no_annotation().get_no_anno(), 42);
        assert_eq!(l6_deep().l2.l3.v, 42);
        assert_eq!(baseline(5), 5);
    }

    #[test]
    fn test_l5_option_is_some() {
        assert!(l5b_option_is_some().is_some());
        assert!(l5c_option_conditional(5).is_some());
        assert!(l5c_option_conditional(0).is_none());
    }

    #[test]
    fn test_l5d_option_with_old() {
        let mut v = vec![1, 2, 3];
        assert!(l5d_option_with_old(&mut v).is_some());
        assert_eq!(v.len(), 2);
        let mut empty: Vec<i32> = vec![];
        assert!(l5d_option_with_old(&mut empty).is_none());
    }

    #[test]
    fn test_l5e_struct_delegation() {
        // L5e tests struct delegation - DISPROVEN by solver but runtime behavior is correct
        let mut wv = WrapVec { raw: vec![1, 2, 3] };
        assert!(wv.pop().is_some());
        assert_eq!(wv.len(), 2);
        let mut empty_wv = WrapVec { raw: vec![] };
        assert!(empty_wv.pop().is_none());
    }

    #[test]
    fn test_l7_regression_cases() {
        let bs = l7_same_name(100);
        assert_eq!(bs.domain_size, 100);

        let bs_simple = l7b_same_name_simple(50);
        assert_eq!(bs_simple.domain_size, 50);

        let gs: GenericSet<u32> = l7c_generic(200);
        assert_eq!(gs.domain_size, 200);
    }

    #[test]
    fn test_l7e_helper_indirection() {
        let hr = l7e_helper_indirection(42);
        assert_eq!(hr.value, 42);
    }

    #[test]
    fn test_l8_multiply() {
        assert_eq!(l8_multiply(3, 4), 12);
        assert_eq!(l8_multiply(0, 100), 0);
        assert_eq!(l8_multiply(100, 0), 0);
    }

    #[test]
    fn test_l8b_divide() {
        assert_eq!(l8b_divide(17, 5), 3);
        assert_eq!(l8b_divide(15, 3), 5);
        assert_eq!(l8b_divide(-17, 5), -3);
    }

    #[test]
    fn test_l8c_modulo() {
        assert_eq!(l8c_modulo(17, 5), 2);
        assert_eq!(l8c_modulo(15, 3), 0);
        assert_eq!(l8c_modulo(-17, 5), -2);
    }

    #[test]
    fn test_l12_phantomdata_helpers() {
        let pe: PhantomEmpty<u32> = l12_phantomdata_result_method();
        assert!(pe.is_empty());

        let pe2: PhantomEmpty<u32> = l12_phantomdata_workaround();
        assert!(pe2.words.is_empty());
    }

    #[test]
    fn test_l13_struct_field_postcondition_flow() {
        // L13: struct field postcondition flow - DISPROVEN by solver but runtime behavior is correct
        let mut og = OuterGrowable {
            inner: InnerBitSet { domain_size: 0 },
        };
        // ensure(5) sets inner.domain_size to 5, then insert(4) should work
        assert!(og.insert(4));
        assert_eq!(og.inner.domain_size, 5);
    }
}
