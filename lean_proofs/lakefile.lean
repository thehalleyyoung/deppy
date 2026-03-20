import Lake
open Lake DSL

package «deppy-proofs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «DeppyProofs» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"
