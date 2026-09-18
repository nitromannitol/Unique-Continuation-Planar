import Lake

open Lake DSL

package «unique-continuation-planar» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "b617769368d5cd11b5b2b43a16e72ff674da0a06"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

require «schoenflies-lean» from git
  "https://github.com/alonamaloh/schoenflies-lean.git" @ "05a43d29cde026618777db3d4e4316204ccca237"

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
