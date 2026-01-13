/-
  MIR Semantics Formalization for tRust (Lean5)

  This is the umbrella module; implementation is split across:
  - `MirSemantics/Syntax.lean`      - Core MIR datatypes
  - `MirSemantics/Semantics.lean`   - Evaluators + executable semantics
  - `MirSemantics/Lemmas.lean`      - Semantics lemmas
  - `MirSemantics/WP.lean`          - WP/WLP definitions + proofs
  - `MirSemantics/SMT.lean`         - SMT interface formalization (N2.3)
  - `MirSemantics/Soundness.lean`   - End-to-end soundness theorem (N2.4)
-/

import MirSemantics.Syntax
import MirSemantics.Semantics
import MirSemantics.Lemmas
import MirSemantics.WP
import MirSemantics.SMT
import MirSemantics.Soundness

