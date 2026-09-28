# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory on 2026-09-24, at commit `767bf10`, on a local machine. Each pair was checked twice: once with the Lean kernel, and once more with the independent `nanoda` kernel enabled (a temporary copy of `comparator.json` with `"enable_nanoda": true`). The committed configurations keep `enable_nanoda` false so that a reproduction needs only three tools.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18; Linux 5.15, Landlock ABI 1 in best-effort mode) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `Counterexample` | passed (80 s) | passed (48 s) |
| `Liouville` | passed (233 s) | passed (300 s) |
| `UniformlyBounded` | passed (171 s) | passed (281 s) |
| `ZeroCase` | passed (171 s) | passed (268 s) |

A pass means the comparator printed `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator Audit/<Pair>/comparator.json
```

## Run of 2026-09-27

Every pair was run again on 2026-09-27, at commit `1f0410f`, against the current
statements and the published Lattice-Probability pin, on a second local machine
(Linux 6.17), with the same tool revisions as above.

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `Counterexample` | passed (39 s) | passed (39 s) |
| `Liouville` | passed (167 s) | passed (286 s) |
| `UniformlyBounded` | passed (186 s) | passed (403 s) |
| `ZeroCase` | passed (167 s) | passed (209 s) |
