import Lake

open Lake DSL

package «unique-continuation-planar» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "bbe0b90a7cf0517db0578139aaab7f152edbc45e"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

require «schoenflies-lean» from git
  "https://github.com/alonamaloh/schoenflies-lean.git" @ "05a43d29cde026618777db3d4e4316204ccca237"

/-- The comparator audit surface (`Audit/*/Challenge.lean`, `Audit/*/Solution.lean` and
`Audit/Support/`).  Not a default target: it builds only on demand (`lake build Audit`), so the
ordinary build of `UCPlanar` is unchanged. -/
lean_lib «Audit» where
  globs := #[.submodules `Audit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

@[default_target]
lean_lib «UCPlanar» where
  globs := #[.andSubmodules `UCPlanar]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]
