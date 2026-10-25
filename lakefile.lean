import Lake

open Lake DSL

package «unique-continuation-planar» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "014ab660fc93c018b804942b26f73893b62a59c5"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

require «schoenflies-lean» from git
  "https://github.com/alonamaloh/schoenflies-lean.git" @ "05a43d29cde026618777db3d4e4316204ccca237"

/-- The comparator audit surface (`UCPlanarAudit/*/Challenge.lean`,
`UCPlanarAudit/*/SolutionBasic.lean`, `UCPlanarAudit/*/Solution.lean` and
`UCPlanarAudit/Support/`).  Not a default target: it builds only on demand
(`lake build UCPlanarAudit`), so the ordinary build of `UCPlanar` is unchanged. -/
lean_lib «UCPlanarAudit» where
  globs := #[.submodules `UCPlanarAudit]
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
