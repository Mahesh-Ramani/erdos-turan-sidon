import Lake
open Lake DSL

package «erdos-turan-sidon» where
  name := "erdos-turan-sidon"
  version := "0.1.0"
  keywords := #["mathematics", "combinatorics", "sidon-sets", "additive-combinatorics",
                "formalization", "mathlib"]
  description := "Lean 4 formalization of the Erdős–Turán Sidon set construction"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «ErdosTuranSidon» where
  roots := #[`ErdosTuranSidon.Basic]
