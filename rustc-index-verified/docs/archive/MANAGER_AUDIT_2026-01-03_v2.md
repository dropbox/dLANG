# MANAGER AUDIT REPORT v2: rustc-index-verified
**Date**: 2026-01-03 (updated)
**Auditor**: MANAGER
**Last Worker**: #174
**Previous Audit**: reports/MANAGER_AUDIT_2026-01-03.md

---

## Executive Summary

**STATUS: 1.88.0 UPGRADE INCOMPLETE - LARGER SCOPE THAN PREVIOUSLY IDENTIFIED**

Re-audit reveals **additional critical gap**: `IntoSliceIdx` trait with 9+ implementations is entirely missing. This trait enables range-based indexing on `IndexSlice` (e.g., `slice[start..end]`).

**Total gaps identified**: 4 critical/high issues

---

## Verified Claims (RE-CONFIRMED)

| Claim | Status | Evidence |
|-------|--------|----------|
| 56/56 functions VERIFIED | **CONFIRMED** | `trustc cargo check` = 56 VERIFIED |
| 173 tests passing | **CONFIRMED** | `cargo test` (148+17+6+2) |
| Clippy clean | **CONFIRMED** | no warnings |
| Stage1 compiler available | **CONFIRMED** | exists |

---

## Gap Analysis (COMPREHENSIVE)

### Gap 1: MixedBitSet Missing BitRelations (CRITICAL)

**Severity**: CRITICAL
**Impact**: MixedBitSet cannot use standard `union()`/`subtract()` API

Upstream 1.88.0:
```rust
impl<T: Idx> BitRelations<MixedBitSet<T>> for MixedBitSet<T> {
    fn union(&mut self, other: &MixedBitSet<T>) -> bool;
    fn subtract(&mut self, other: &MixedBitSet<T>) -> bool;
    fn intersect(&mut self, _other: &MixedBitSet<T>) -> bool; // unimplemented!()
}
```

**Our implementation**: MISSING

### Gap 2: IntoSliceIdx Trait Missing (CRITICAL - NEW FINDING)

**Severity**: CRITICAL
**Impact**: IndexSlice cannot support range-based indexing

Upstream 1.88.0 has in `idx.rs`:
```rust
pub trait IntoSliceIdx<I, T: ?Sized> {
    type Output: SliceIndex<T>;
    fn into_slice_idx(self) -> Self::Output;
}
```

With **9-10 implementations** for:
- `I: Idx` (single element)
- `Range<I>`, `RangeFrom<I>`, `RangeTo<I>`
- `RangeInclusive<I>`, `RangeToInclusive<I>`
- `RangeFull`
- Plus nightly `core::range::*` variants

**Our implementation**: COMPLETELY MISSING

**Consequence**: Our `IndexSlice` only has `Index<I>` (single element), not generic `Index<R: IntoSliceIdx>` (ranges).

Upstream 1.88.0 `slice.rs`:
```rust
impl<I: Idx, T, R: IntoSliceIdx<I, [T]>> Index<R> for IndexSlice<I, T>
```

Our `slice.rs`:
```rust
impl<I: Idx, T> Index<I> for IndexSlice<I, T>  // Single element only!
```

### Gap 3: Missing Unit Tests (HIGH)

**Severity**: HIGH
**Count**: 0 tests for new features

Missing tests:
- MixedBitSet (all methods)
- MixedBitIter
- BitSet::contains_any()
- BitSet::union_not()
- IntoSliceIdx (after implemented)

### Gap 4: Missing Verification Specs (MEDIUM)

**Severity**: MEDIUM

No `#[cfg_attr(trust_verify, ...)]` on:
- MixedBitSet methods
- BitSet::contains_any()
- BitSet::union_not()
- IntoSliceIdx impls (after implemented)

---

## Upstream 1.88.0 vs Our Implementation

### bit_set.rs Comparison

| Feature | Upstream 1.88.0 | Ours | Status |
|---------|-----------------|------|--------|
| DenseBitSet alias | ✓ | ✓ | OK |
| MixedBitSet enum | ✓ | ✓ | OK |
| MixedBitSet::union() | ✓ | ✗ | **MISSING** |
| MixedBitSet::subtract() | ✓ | ✗ | **MISSING** |
| BitRelations<MixedBitSet> | ✓ | ✗ | **MISSING** |
| contains_any() | ✓ | ✓ | OK |
| union_not() | ✓ | ✓ | OK |
| SparseBitSet | ✗ (removed) | deprecated | OK |
| HybridBitSet | ✗ (removed) | deprecated | OK |
| GrowableBitSet | ✓ | ✓ | OK |
| CHUNK_BITS private | ✓ | ✓ | OK |
| Chunk private | ✓ | ✓ | OK |

### idx.rs Comparison

| Feature | Upstream 1.88.0 | Ours | Status |
|---------|-----------------|------|--------|
| Idx trait | ✓ | ✓ | OK |
| IntoSliceIdx trait | ✓ | ✗ | **MISSING** |
| 9+ IntoSliceIdx impls | ✓ | ✗ | **MISSING** |

### slice.rs Comparison

| Feature | Upstream 1.88.0 | Ours | Status |
|---------|-----------------|------|--------|
| Index<I> | ✓ | ✓ | OK |
| Index<R: IntoSliceIdx> | ✓ | ✗ | **MISSING** |
| IndexMut<R: IntoSliceIdx> | ✓ | ✗ | **MISSING** |

---

## Work Required (REVISED)

### Phase A: Complete MixedBitSet BitRelations (1 AI commit)

```rust
impl<T: Idx> BitRelations<MixedBitSet<T>> for MixedBitSet<T> {
    fn union(&mut self, other: &MixedBitSet<T>) -> bool {
        match (self, other) {
            (MixedBitSet::Small(s), MixedBitSet::Small(o)) => s.union(o),
            (MixedBitSet::Large(s), MixedBitSet::Large(o)) => s.union(o),
            _ => panic!("MixedBitSet size mismatch"),
        }
    }
    fn subtract(&mut self, other: &MixedBitSet<T>) -> bool {
        match (self, other) {
            (MixedBitSet::Small(s), MixedBitSet::Small(o)) => s.subtract(o),
            (MixedBitSet::Large(s), MixedBitSet::Large(o)) => s.subtract(o),
            _ => panic!("MixedBitSet size mismatch"),
        }
    }
    fn intersect(&mut self, _other: &MixedBitSet<T>) -> bool {
        unimplemented!("implement if/when necessary")
    }
}
```

### Phase B: Add IntoSliceIdx (2-3 AI commits)

1. Add `IntoSliceIdx` trait to `idx.rs`
2. Add 9+ implementations for range types
3. Update `IndexSlice` Index/IndexMut impls to use generic `R: IntoSliceIdx`
4. Update `IndexVec` if needed

### Phase C: Add Unit Tests (1 AI commit)

Tests for:
- MixedBitSet (basic ops, union, subtract, iter)
- contains_any (empty, single, range, cross-word)
- union_not (basic, excess bits)
- IntoSliceIdx range indexing

### Phase D: Add Verification Specs (1 AI commit)

Add specs to new methods where solver supports.

---

## Estimated Effort

| Phase | Work | AI Commits |
|-------|------|------------|
| A | MixedBitSet BitRelations | 1 |
| B | IntoSliceIdx trait + impls | 2-3 |
| C | Unit tests | 1 |
| D | Verification specs | 1 |
| **Total** | | **5-6** |

---

## Decision Point: Scope of 1.88.0 Upgrade

**Option 1**: Complete full 1.88.0 parity (5-6 commits)
- Includes IntoSliceIdx (range-based indexing)
- Full API compatibility with upstream

**Option 2**: Minimal fix (1-2 commits)
- Only add MixedBitSet BitRelations
- Defer IntoSliceIdx to future work
- Document limitation

**Recommendation**: Option 1 - IntoSliceIdx is a significant usability feature for downstream consumers.

---

## Worker Directive

**Next Worker (#175)**:

```
PRIORITY 1: Add impl BitRelations<MixedBitSet<T>> for MixedBitSet<T>
- Copy exact implementation from upstream
- Add unit tests for union/subtract

PRIORITY 2: Add IntoSliceIdx trait and impls
- Add trait to idx.rs
- Add implementations for all range types
- Update IndexSlice Index/IndexMut impls

PRIORITY 3: Update ROADMAP.md
- Change status from COMPLETE to IN_PROGRESS
- Add 1.88.0 upgrade checklist

Run tests and verification after each change.
```

---

## Appendix: Evidence

```bash
# Confirmed missing BitRelations
$ grep -n "impl.*BitRelations.*MixedBitSet" src/bit_set.rs
# (no output)

# Confirmed missing IntoSliceIdx
$ grep -n "IntoSliceIdx" src/*.rs
# (no output)

# Our Index impl (single element only)
$ grep "impl.*Index.*for IndexSlice" src/slice.rs
impl<I: Idx, T> Index<I> for IndexSlice<I, T> {

# Verified trustc still works
$ TRUST_SKIP_AUTO_CHECKS=1 ... cargo check 2>&1 | grep -c VERIFIED
56
```
