# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory, against the statements of this repository and the pinned Lattice-Probability, on a local machine (Linux 6.17), with the Lean kernel and the independent `nanoda` kernel both enabled (every committed `comparator.json` sets `"enable_nanoda": true`).

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18; Linux 5.15, Landlock ABI 1 in best-effort mode) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

A pass means the comparator printed `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

## `Counterexample`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (40 s) |

## `Liouville`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (394 s) |

## `UniformlyBounded`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (263 s) |

## `ZeroCase`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (392 s) |

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator UCPlanarAudit/<Pair>/comparator.json
```
