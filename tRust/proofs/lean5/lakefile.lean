import Lake
open Lake DSL

package tRustProofs where
  moreServerArgs := #[
    "-K", "maxRecDepth=2048",
    "-K", "maxHeartbeats=200000"
  ]

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_lib TRustProofs where
  srcDir := "."
  roots := #[`MirSemantics]
