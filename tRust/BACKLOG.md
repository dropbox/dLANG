# tRust Backlog: All Relevant Rust Issues

Complete inventory of rust-lang/rust issues that tRust could address or benefit from.

---

## Category 1: Bounds Check Elimination (CRITICAL for tRust)

tRust's core value prop: proofs eliminate runtime checks. These are direct targets.

| Issue | Title |
|-------|-------|
| #149480 | Array indexed by exhaustive match still generates bounds checks |
| #146988 | Adding an `assert!` prevents bounds check elision |
| #144522 | Range of index variables forgotten in an `else if` |
| #127553 | Missed bounds check elimination |
| #100308 | rustc fails to detect variable bounds |
| #92327 | Potential optimization: Bounds check hoisting |
| #81253 | Array bound tests with for loop that get removed with while loops |

---

## Category 2: Borrow Checker Limitations (tRust specs can prove these)

| Issue | Title |
|-------|-------|
| #150465 | regression: "the parameter type `T` may not live long enough" in `offset_of!` |
| #148897 | Strange behavior of borrow checker |
| #148854 | Lifetime bounds of Drop aren't checked properly |
| #148532 | Borrow checker wrongly counts mutable references |
| #148463 | Function arguments in nontrivial pattern can be reassigned with different lifetime |
| #148389 | `async fn` can assign to argument to change its lifetime |
| #147875 | Local variable deallocated out of order in the panic path? |
| #147694 | Detect attempt to reuse buffer with extended borrows |
| #147108 | Detect need for partial `self` borrows in methods |
| #147089 | Incorrect borrow checker error |
| #146590 | Uninhabited types have strange borrow-checking behavior |
| #146062 | member constraints involving external regions are scuffed |
| #145347 | "due to current limitations in the borrow checker" is often not a current limitation |
| #145237 | Match guard can both move and static-promote a single constant |
| #145032 | Consuming a value with destructuring pattern doesn't end borrows for drop-check |
| #144635 | Very slow `EverInitializedPlaces` analysis on async fn with many awaits |
| #142766 | `super let` with `&mut [T; 0]` in `const` has inconsistent borrow-checking |
| #142039 | nested mutable reference error |
| #139930 | `rustc` thinks that two non-intersecting borrows intersect |
| #139670 | strange cannot move out of a mutable reference error |
| #138408 | Lifetime must be 'static, but why? |
| #138194 | How can `let y;` and `let y: _;` be different to the borrow checker? |
| #137878 | Too conservative lifetime check in match arm with if condition |
| #136726 | "implementation is not general enough" even if only `'static` is used |
| #136245 | Borrow checker does not release a mutable borrow when condition is false |
| #133539 | Cannot return value from loop when temporary mutable access occurs before |
| #133054 | Large arrays of enum variants causes polonius to have massive performance issues |
| #131008 | GAT `type Assoc<T: ?Sized>` implicitly requires `Self` to be `'static` |
| #130584 | "Reference to data owned by current function" for a function owning no data |
| #129694 | Moving mutable borrows in/out of inferred types results in wrong compiler error |
| #128933 | Allow exactly one mutable reference even after multiple immutable reference |
| #127215 | `*x == *y` for trait objects produce move error |
| #126565 | diagnostic refers to the wrong object's lifetime |
| #125217 | fixed-by-polonius loops/functions have very bad diagnostics |
| #121601 | Borrow checker fails to pick up existing region bounds |
| #119291 | Compiling fails as a sync function but succeeds in async function |
| #115390 | Unable to use match with borrowed value which will be mutated and returned |
| #114168 | Borrow checker bug when matching select().await with &mut references |
| #113322 | Spurious reborrowing errors when returning lifetimes referencing mutable borrows |
| #111298 | Borrow checking can be affected by seemingly irrelevant statements |
| #110759 | refuse to borrow when no other reference exists technically |
| #110362 | "left.extend_from_slice(right.strip_prefix(&mut left[n..]).unwrap())" doesn't compile |
| #110351 | "&mut v[v[0]..]" doesn't compile |
| #97901 | Can't return reference to passed-in referent that is assigned in a loop |
| #94767 | A confusing compile error about lifetime of mutable reference after reborrowed |
| #92038 | Returning the result of reborrowing in pattern matching causes compilation error |
| #91363 | Inserting a conditional `break` in working code causes strange borrowck error |
| #89966 | Fully-qualifying a `From::from` call adds an implicit reborrow |

---

## Category 3: Const Generics (Required for Refinement Types)

| Issue | Title |
|-------|-------|
| #149660 | Resolve error in const params doesn't do fuzzy search for consts |
| #149214 | Type of const generic can't be associated type |
| #149203 | `Self` not allowed in type of const generics even when concrete |
| #148596 | ICE: expected type for `<closure_kind>/#2` |
| #148377 | Support fn() types as const generic parameters |
| #147103 | `thread_local!` doesn't like types whose definitions cannot be written more than once |
| #146962 | Const generics do not accept exhaustive trait impls |
| #145376 | Compiler doesn't allow creating u8 slices when using const generics |
| #145133 | Trait solver fails to see trait is implemented for all values of const param |
| #144021 | `generic_const_exprs` doesn't evaluate `size_of::<T>()` if T is generic |
| #137626 | Tracking Issue for `feature(generic_const_parameter_types)` |
| #132980 | Tracking Issue for Generic Constant Arguments MVP |
| #129766 | Next-gen Trait Solver does not implement Generic Const Expressions |
| #128028 | Tracking Issue for unsized const parameter types |
| #126609 | rustc hangs / infinite loop with generic_const_exprs and specialization |
| #124531 | `#![feature(generic_const_exprs)]` does not compile stable code related to lifetimes |
| #116585 | `std::mem::transmute` doesn't compile even though both types are same size |
| #114406 | `generic_const_exprs` and generics inferring lead to false impls |
| #111276 | "unconstrained generic constant" when adding numbers |
| #101849 | Addition does not commute in generic_const_exprs |
| #98210 | Error: The type of const parameters must not depend on other generic parameters |
| #95174 | Tracking Issue for more complex const parameter types |
| #92827 | Tracking issue for associated const equality |
| #80976 | Additional bounds are required for const generics using associated constants |
| #80528 | Support `_` for const inference with const generics |

---

## Category 4: Async (Required for Temporal Verification)

| Issue | Title |
|-------|-------|
| #150378 | ICE: broken MIR Unsize coercion (async block !Sync) |
| #149407 | Send bound on RPITIT async method causes spurious lifetime errors |
| #149235 | Implementation is not general enough error with no context |
| #148391 | Diagnostics incorrectly states that async closure implements `Fn` |
| #148389 | `async fn` can assign to argument to change its lifetime |
| #147041 | Async function generates potentially panicking code |
| #146547 | Disjoint capture in async blocks requires mut for Copy field modifications |
| #145127 | Cannot combine `async fn`-in-traits with `AsyncFn{,Mut}` closures |
| #144391 | dead value causes `async` future to not be `Send` |
| #144344 | Rust does not correctly handle async recursion with nice errors |
| #143429 | Incorrect rejection of async code on type not living long enough |
| #142572 | segmentation fault when using async_drop feature |
| #140987 | Making trait method `async` causes inference failure |
| #140728 | Polymorphic recursion in async fn gives "queries overflow the depth limit" |
| #140725 | stack overflow while compiling async recursion |
| #137698 | Migrating from `Fn -> impl Future` to `AsyncFn` breaks Send |
| #135468 | Async function calls not optimized out |
| #135062 | Missing `Send` on "recursive" `Future` |
| #134101 | rustc doesn't infer that the future of a recursive `async fn` is `Send` |
| #132050 | Repeated calls to the same `async` fn can cause stack overflow |
| #130935 | Outlives requirements are not implied in the return type of `async fn` |
| #130596 | `Send` bound of trait object make unexpected async block is not general enough |
| #130113 | Bogus "implementation of trait is not general enough" with async |
| #129347 | #[inline(never)] does not work for async functions |
| #129105 | Misleading help suggests `Sync` bound when shareable reference is passed across await |
| #128095 | rustc fails to prove `Send`ness for an `async` block where a `!Send` value is dropped before await |
| #126551 | Async code causes error "implementation of `FnOnce` is not general enough" |
| #126550 | Extremely un-informative error when a future captures the environment |
| #126482 | Tracking Issue for async drop codegen |
| #126350 | `async_closure`: error: implementation of `AsyncFnOnce` is not general enough |
| #126044 | Bug when using `.flatten()` method with `Item = &'a T` in async |
| #123392 | Tracking Issue for `context_ext` |
| #123072 | Recursive async functions don't internally implement auto traits |
| #122332 | recursive async function using `Box::new` results in cycle error |
| #121093 | Async callback argument causes nonsensical error message |
| #116680 | Non-Send values that are assigned but not used across await still mark Future non-Send |
| #116048 | Changing async function body causes caller to fail |
| #115327 | Slow compilation of async fn that creates a vector with many Strings |
| #114947 | async fn lifetime eliding satisfies HRTB where explicit does not |
| #114177 | Weirdness around async function with "implementation of FnOnce is not general enough" |
| #114046 | Higher ranked lifetime error when trying to see that a future is send |
| #112456 | ICE: "forcing query with already existing `DepNode`" with many async calls |
| #112175 | Unclear error message when using recursive future with tokio::spawn |
| #111852 | error: `X` does not live long enough doesn't provide enough context |
| #111546 | `.await` does not perform autoref or autoderef |
| #110339 | "Implementation not general enough" with async and projection |
| #110338 | Tracking issue for incorrect lifetime bound errors in async |

---

## Category 5: MIR Optimizations (Cleaner MIR = Simpler VC Generation)

| Issue | Title |
|-------|-------|
| #149920 | ICE `invalid immediate for given destination place` |
| #149898 | Circularly defined GAT is somehow allowed and ICEs Miri |
| #149748 | ICE: `statement with overlapping memory` |
| #141649 | Missed optimization: multiple instances of small struct don't reuse stack |
| #141313 | GVN misunderstands aliasing, can create overlapping assignments |
| #139422 | Ensure we can optimize out does-nothing `drop`s |
| #138544 | Simple `Option` use should optimize out fully in MIR |
| #137086 | MIR passes do not take into account if an operation is convergent |
| #132898 | ReferencePropagation introduces UB |
| #127336 | Miscompilation of a program projecting field of an extern type |
| #123670 | Figure out the interaction of GVN and function/vtable pointers |
| #122828 | Evaluating constants in MIR optimizations introduces const eval errors |
| #121354 | Very slow 80 minutes release build, due mir_pass_scalar_replacement |
| #117970 | Suboptimal order of tests in `match` |
| #116541 | Missed optimization: RVO isn't applied |
| #116521 | Conditions for successful RVO/NRVO |
| #111442 | Tracking issue for MIR simplification opportunities |
| #111005 | NRVO miropt is unsound |
| #106147 | MIR inlining introduces trait solver overflows |
| #99504 | Very inefficient code generated for async functions setup |
| #97092 | FakeRead is semantically meaningful to miri (but gets optimized away) |
| #93707 | Could the compiler automatically re-use `Box` allocations? |
| #91688 | Local value numbering for MIR |
| #88793 | Missing MIR optimization: Replace matches with loads if possible |
| #87950 | Optimization of iteration over enums |
| #83193 | remove redundant clones via mir opt? |
| #83101 | Inline generators before state machine conversion |
| #80630 | Rust insufficiently optimizes loop { match { } } state machines |
| #79531 | Padding for well-aligned values is not used for niche value optimization |

---

## Category 6: Codegen / Performance (Proof-Driven Optimization Targets)

| Issue | Title |
|-------|-------|
| #150470 | Better codegen with `#[unsafe(no_mangle)]`, worse optimization with specific integers |
| #150325 | Suboptimal code generation for array element replace/overwrite |
| #150235 | Regression: iter_mut().nth().next() retains unwrap panic path |
| #149762 | Redundant memory stores with mut parameters in by-value returns |
| #149727 | Optimization of deinitialization became worse in nightly |
| #149672 | Different codegen between index and iterator |
| #149293 | Using array references instead of slices can hurt performance |
| #149230 | LLVM not optimizing out heap allocations when using custom allocator |
| #148461 | Bad codegen with inlined functions returning `Result` with niche |
| #147646 | Unable to induce constant float folding via `assert_eq!(x, 0.0)` |
| #147459 | Extra instructions in `as_chunks` remainder loop |
| #146844 | MIR optimization produces worse code by losing provenance information |
| #146555 | Adding generic incur in penalty? |
| #146497 | 4000% performance regression with target-cpu=x86-64-v3 and fat LTO |
| #146336 | failed deinterleaving autovectorization |
| #146270 | `Vec::into_iter().flatten().collect()` doesn't reuse allocation |
| #146081 | Transitioning to superset enum variant causes unnecessary copy |
| #146056 | Trivial move creates unnecessary copy |
| #145248 | Very bad SIMD code generation for simple Euler integration |
| #144684 | Slice iterator advancement can become unidiomatic |
| #144118 | `iter_mut` is slightly slower than code with manual for loop |
| #144005 | Missed optimizations with strided slice access autovectorization |
| #143966 | zip(chain(...)) with iterators optimizes very poorly |
| #143959 | Conditional `char` counter not recognized as never-overflowing |
| #143513 | Regression in inlining performance from 1.82.0 |
| #143050 | Slow indirect function calls with 16-byte by-pointer enum argument |
| #142951 | Missed optimization: re-checking enum variants after `mem::replace` |
| #142710 | Missed optimization: comparing array to zero is not vectorized |
| #142519 | Function no longer auto-vectorizes in 1.87.0 |
| #142469 | Redundant memset in convolution kernel |
| #141915 | i32.clamp() produces worse code than min().max() |
| #141853 | A moderate rustc/gcc performance difference |
| #141720 | rustc_session: be more precise about -Z plt=yes on x86-64? |
| #141360 | Performance problem in for loops with step_by(run-time-variable) |
| #141297 | Slow and memory-intensive compilation with debug symbols |
| #141144 | Inlining leaves extra assembly |
| #140873 | removing needless `.collect()` in iterator chain reduces performance |
| #140167 | Bad codegen for comparing struct of two 16bit ints |
| #139851 | Simpler Logic Produces More Complex Output Than Equivalent Expression |
| #139784 | Significantly different assembly output for logically equivalent code |
| #139733 | assert_eq! of trivially-equal enums with 2 non-empty variants not optimized |
| #139655 | `is_char_boundary` not elided when impl `pop` in terms of `truncate` |
| #139415 | Optimization regression: array argument somehow produces null check? |
| #139160 | Intrinsics wrappers not being inlined |
| #138953 | f32 += f32 * u32 is faster in a loop than f32 += f32 |
| #138497 | Removing trailing zeros of a NonZero |
| #138373 | Allow emitting more enums as SSA values |
| #137568 | Emit `dereferenceable` assumptions for slices |
| #137335 | Inefficient code generation with target-feature AVX2 |
| #136972 | Suboptimal codegen for match from enum to almost-same-value usize |
| #136218 | Missed optimization: big immutable locals are not promoted to constants |
| #136216 | Missed `match` optimization of riscv |
| #135980 | u128 manual byte-reading is not optimized, in contrast to u64 |
| #135798 | Basic wrapping arithmetic on pointers is pessimized compared to integers |
| #135241 | Performance regression on toy problem, but not for opt-level=1 |
| #133822 | enums with disjoint ranges should emit more precise `llvm.range` metadata |
| #133082 | Performance regression between 1.78 and 1.79 |
| #132763 | `isqrt` treated as a `black_box` |
| #132636 | Regression in performance (poor codegen) between 1.81 and 1.82 |
| #132628 | Inefficient implementation of `PartialEq` for nested (fieldless) enums |
| #131987 | Codegen depends on let-variable ordering for unclear reasons |
| #130421 | Suboptimal codegen for a function that should fold to a constant |
| #128921 | Missing optimization for integer `modulo` operation in `loop` edge case |
| #127384 | Three-way `match` compare mapping to immediates lowered to memory table |
| #127376 | Return branches not correctly merged in size-optimized x86-64 assembly |
| #127250 | Chains of checked_add could get better codegen |

---

## Category 7: Compile Time (Critical for tRust Iteration Speed)

| Issue | Title |
|-------|-------|
| #150061 | Exponential compile time and high memory usage with nested const evaluation |
| #149945 | Avoid monomorphizing intrinsic fallback bodies that the backend does not need |
| #148335 | `const` in `async fn` is evaluated twice when used across crates |
| #146935 | Performance degradation when enabling `wgpu` dep |
| #146895 | `cargo doc` in large workspace is 10 times slower on nightly |
| #145864 | rustc final stages extremely slow for large programs, with msvc builds |
| #145527 | Some crates hang when building with opt-level=3 |
| #144635 | Very slow `EverInitializedPlaces` analysis on async fn with many awaits |
| #141006 | `lemmy_db_views_modlog_combined` has a weird performance regression |
| #140454 | [Polonius] Timeout while compiling handcrafted example |
| #140004 | Exponential compile time increase when nesting async closures in 1.86 |
| #138828 | Slow coherence checking and type checking |
| #137680 | Dumps unbounded amounts of data in diagnostics (27M in three lines) |
| #137678 | 1 million item array spends inordinate time on error path of typechecking |
| #137636 | Polynomial slowdown in `impl Trait` composition |
| #137560 | Incremental compilation on Windows is slow because of hard links |
| #137496 | Runaway builds: the build hangs for 2 hours without producing output |
| #137005 | Experiment with using `HashMap::with_capacity` throughout compiler |
| #135849 | Trait implementation causes `Object File Too Large` error |
| #134404 | Large files containing many tokens of `const` data compile very slowly |
| #133945 | Compiling `#[derive(Debug)] enum` + `dbg!` is quadratic with enum variants |
| #133354 | rustc hangs with gordian knot of trait bounds |
| #133054 | Large arrays of enum variants causes polonius to have massive performance issues |
| #132991 | Exponential time complexity for parser combinator with RPITIT |
| #132775 | Rustdoc: Very long doc compile times (95%+ taken by render_html) |
| #132064 | regression: crate compiles much slower with 1.82 |
| #131411 | Compiling `cranelift-codegen` with `-Z next-solver` is very slow |
| #131231 | Compile time regression with the new trait solver and diesel |
| #129844 | rustc consumes > 50GB memory, completes eventually but stuck on something |
| #129776 | Too long compile time with implementing a trait function |
| #129713 | Very long compilation time on Apple Silicon platform |
| #128538 | 100% CPU usage when running doc tests |
| #125994 | Very bad performance of `cargo check` on generic code |
| #125267 | Exponential time complexity when type checking code with equality constraints |
| #124653 | Ludicrous build time for `keshvar` crate in `release` mode |
| #121354 | Very slow 80 minutes release build |
| #120647 | cargo check is > O(n) per number of unchanged files |
| #119503 | exponential compile times for simple function compositions |

---

## Category 8: High Priority Bugs (May Affect tRust)

| Issue | Title |
|-------|-------|
| #149774 | Not using anon consts for uses of const parameters caused us to accept more code |
| #148948 | rustc does not always update the mtime of all its outputs |
| #148854 | Lifetime bounds of Drop aren't checked properly |
| #148423 | `derive(PartialEq)` on enums is unsound with user-defined attribute macros |
| #148349 | Overflow evaluating well-formedness requirement with empty trait bound |
| #148273 | catch_unwind doesn't catch non-C++ exceptions on wasm |
| #147964 | regression: the method `as_ref` exists for reference |
| #147265 | Rust 1.90 compiler optimization (O2, O3) triggers UB with Box::from_raw() |
| #147014 | rustdoc: Since 1.87 we permit shebangs in doctests that have a `main` fn |
| #146965 | SignatureMismatch ICE |
| #146813 | 1.90 regression: Cycle detected when type checking |
| #144351 | Potentially-observable store gets elided: asm block does not act as a compiler fence |
| #144312 | Patterns sometimes ignores lifetimes |
| #143411 | Destructor of packed structs can move dangling references |
| #143047 | const-eval can construct uninhabited values or other unconstructable values |
| #141713 | Incoherent (?) Lifetime HRTB on associated type results in unsoundness in stable |
| #141313 | GVN misunderstands aliasing, can create overlapping assignments (again) |
| #134375 | aarch64-unknown-none-softfloat: ABI unsoundness when enabling "neon" feature |
| #132673 | Hang after encountering overflow errors for huge types |
| #131960 | Regression: geoarrow crate does not compile in release mode on 1.82 |
| #131488 | Implementation of trait "not general enough" in nightly, works fine on stable |
| #129893 | -Csoft-float flag is unsound |
| #126747 | Undefined behavior from stack overflow on wasm32 targets |
| #118223 | x86-64 assembler silently truncates 64-bit address |
| #116573 | Inlining causes miscompilation of code that mixes target features |

---

## Category 9: Confusing Diagnostics (For AI Error Parsing)

| Issue | Title |
|-------|-------|
| #149725 | Expose dlopen error when failing to load a proc-macro |
| #149546 | Private field can cause confusion with identically named field on deref target |
| #148009 | `use`ing inherent method/const gives misleading error |
| #147389 | Potentially valid code doesn't compile - a silly error message |
| #146208 | E0308 Fallback to blanket impl due to lack of ?Sized creates puzzling type error |
| #146126 | rustc flags the wrong line for an ambiguous `.into` |
| #145558 | Lifetimes on functions suppress helpful error hint |
| #143950 | E0599 for incorrect boxing of closure is confusing |
| #143455 | Diagnostic talks about and prints entire function type on private function |
| #142446 | Doc-test reports "expected item, found keyword let" when actual problem different |
| #141872 | Baffling suggestion labelled "help: try introducing a local generic parameter here" |
| #141436 | Forgetting a right angle bracket gives: "error: `Fn` traits cannot take lifetimes" |
| #141336 | type inference failure confusing diagnostic let Some(x) = None for [u8] |
| #141234 | wrong span for E0277 |
| #141081 | Confusing error when using non-`XID_Start` characters in lifetime names |
| #136994 | `Trait::nonexistent` treats `Trait` as a type, resulting in bad errors |
| #136902 | Confusing diagnostic when the error value converted by `?` fails to satisfy `'static` |
| #136528 | Better errors for polymorphic recursion |
| #134390 | Better error reporting for `T: ?Sized` types when `impl Receiver for MyType<T>` |
| #134087 | Unhelpful diagnostic on `=` to `:` typo mentioning return type notation |
| #133716 | Confusing diagnostics with nested precise capturing RPIT |
| #133316 | `if` and `else` have incompatible types in a `let` statement |
| #132655 | Misleading error messages when using the wrong macro fragment specifiers |
| #132643 | LUB coercions works for a function but fails for a closure |
| #132165 | Misleading diagnostic output for typecheck failures involving type inference |
| #131821 | A out-of-air lifetime that may not live long vs. the implementation is not general |
| #130891 | Unable to match non_exhaustive enum tuple variants with rest pattern |
| #130588 | Incorrect diagnostic "pattern requires `..` due to inaccessible fields" |
| #130584 | "Reference to data owned by current function" for a function owning no data |
| #130326 | Assignment into Deref is allowed and creates irrelevant errors |
| #130032 | Cycle errors lead to confusing errors referencing rustc-dev-guide |
| #129792 | Point at unit structs in type errors when they are the pattern of a let binding |
| #129273 | E0050 emitted unexpectedly on missing `:` |
| #129269 | anyhow Result + collect = misleading error messages |

---

## Summary Statistics

| Category | Count | Priority for tRust |
|----------|-------|-------------------|
| Bounds Check Elimination | 7 | CRITICAL |
| Borrow Checker | 75+ | HIGH |
| Const Generics | 50+ | HIGH |
| Async | 70+ | HIGH |
| MIR Optimizations | 30+ | MEDIUM |
| Codegen/Performance | 70+ | MEDIUM |
| Compile Time | 40+ | MEDIUM |
| High Priority Bugs | 25+ | AS NEEDED |
| Confusing Diagnostics | 35+ | LOW |

**Total: ~400+ issues tracked**

---

## Quick Links

- [Bounds checks](https://github.com/rust-lang/rust/issues?q=is%3Aissue+is%3Aopen+bounds+check+label%3AI-slow)
- [Borrow checker](https://github.com/rust-lang/rust/labels/A-borrow-checker)
- [Const generics](https://github.com/rust-lang/rust/labels/A-const-generics)
- [Async](https://github.com/rust-lang/rust/labels/A-async-await)
- [MIR opt](https://github.com/rust-lang/rust/labels/A-mir-opt)
- [Slow/perf](https://github.com/rust-lang/rust/labels/I-slow)
- [Compile time](https://github.com/rust-lang/rust/labels/I-compiletime)
