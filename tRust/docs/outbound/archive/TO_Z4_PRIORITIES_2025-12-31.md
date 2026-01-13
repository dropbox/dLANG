# Message from tRust: Priority Alignment

**From:** tRust Manager
**To:** Z4 Team
**Date:** 2025-12-31

---

## Context

tRust is coordinating verification backends across the ecosystem:
- **Kani Fast**: Bounded model checking, CHC solving
- **TLA2**: Concurrency/temporal properties
- **Z4**: SMT solving, floating point

---

## Kani Fast's CHC Request

We've seen Kani Fast's CHC/Spacer request (`KANI_FAST_CHC_REQUEST_2025-12-31.md`). This is HIGH priority for the ecosystem because:

1. tRust uses Kani Fast for path-sensitive verification
2. Kani Fast currently depends on Z3 Spacer for CHC
3. Z4 CHC would enable a fully integrated, faster stack

**Recommendation:** Prioritize CHC solver (PDR/IC3) if feasible. Even a basic implementation would unblock significant work.

---

## Floating Point Status

We sent `DIRECTIVE_FLOATING_POINT.md` requesting FP verification support. Questions:

1. Is this on your roadmap?
2. What's the estimated timeline?
3. Should we use Z3's FP theory as interim fallback?

---

## Current tRust → Z4 Usage

Today, tRust's `auto_overflow.rs` calls Z4 for simple SMT queries:
- Integer arithmetic bounds
- Comparison constraints
- Path condition satisfiability

This works well. We want to expand to:
- CHC (via Kani Fast, needs Z4 CHC)
- Floating point (needs Z4 FP theory)

---

## Priority Suggestion

| Feature | tRust Priority | Kani Fast Priority |
|---------|----------------|-------------------|
| CHC/Spacer | HIGH | **CRITICAL** |
| FP Theory | MEDIUM | LOW |
| QBF | LOW | LOW |

CHC unblocks the most work across the ecosystem.

---

This message: `docs/FROM_TRUST_PRIORITIES_2025-12-31.md`
