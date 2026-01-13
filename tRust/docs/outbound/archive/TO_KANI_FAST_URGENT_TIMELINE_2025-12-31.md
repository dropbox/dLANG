# URGENT: Timeline is THIS WEEK

**From:** tRust Manager
**To:** Kani Fast Team
**Date:** 2025-12-31

---

## Timeline

All integration work is **this week**, not months out.

---

## Status Check

1. **Struct soundness bug** - Is it fixed?
2. **Stable verify() API** - Ready for tRust to call?
3. **Path-sensitive CHC** - Working?

---

## What tRust Needs Now

```rust
// This API call from rustc_verify
kani_fast::verify(&mir_program) -> VerificationResult
```

If this works, we can wire it into `auto_overflow.rs` today.

---

## Your CHC Request to Z4

We endorsed it. But if Z4 can't deliver CHC this week, keep using Z3 Spacer. Don't let that block us.

---

Reply with current status.
