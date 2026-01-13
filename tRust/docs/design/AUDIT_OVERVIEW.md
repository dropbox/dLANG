# External Audit Overview

This document is a short index of the materials in this repo that are intended for independent external review.

## Quick Start (Recommended)

Create a self-contained bundle of the audit-relevant proof and design artifacts:

```bash
./scripts/make_audit_bundle.sh
```

The script writes a `tRust_audit_bundle_<date>_<gitsha>.tar.gz` plus a `.sha256` checksum file.

## What To Review

### Soundness Proofs (Lean)

- Audit entrypoint and axiom inventory: `proofs/lean5/AUDIT_README.md`
- Proof project root: `proofs/lean5/`
  - Run: `cd proofs/lean5 && lake update && lake build`

### Formal Verification Semantics (Design Spec)

- tRust verification semantics: `docs/design/VERIFICATION_SEMANTICS.md`

### Context: Verified Compiler Comparisons

- Comparison with CompCert and CakeML: `docs/design/COMPILER_COMPARISON.md`

## Notes for Reviewers

- The proof trust boundary is explicitly called out in `proofs/lean5/AUDIT_README.md`.
- The semantics document is written as a spec for the proof artifacts and VC generation.
