# Independent refute-first audit — Unique-Continuation-Planar

Date: 2026-10-03.  Auditor: an independent instance, refute-first, read-only with respect to the
audited material.  Repo: `~/lean/Unique-Continuation-Planar`, `main` at the pinned commit, clean tree.

**Result: not refuted.  No FAIL.**  The paper pin, all 11 frozen hashes, the
axiom closures and the repo gates pass.  The 8 `SEALED` nodes are promoted to
`PROVED`; the 3 cited inputs `X-002`, `X-003`, `X-007` remain `FROZEN`.

## What was checked, and how

1. **Paper pin.** `sha256(paper/ucplanar.tex)` recomputed independently = `0a97204b…b311`, equal
   to `source_pin.sha256`.
2. **Frozen hashes.** The bytes strictly between the markers (one leading newline dropped),
   hashed by an independent script: **11/11 equal** to
   `frozen_sha256`.
3. **Axiom closures.** `tools/check_axioms.py` prints `#print axioms` for every export:
   **11 clean, 0 on `sorryAx`, 0 unresolved**.  The three topology/analysis
   inputs are assumed only through the explicit `h` binders the sealed statements display.
4. **Gates.** `check_manifest` OK (11 nodes, 132 declarations indexed);
   `check_constants` every existential constant bound before every paper parameter;
   `paper_anchors` anchors resolved; `check_warnings` a warning-free 9004-job build;
   `certificate --check` matches.
5. **Correspondence.** The clause readings and the formulation deltas (the two classical plane
   inputs carried as hypotheses) are recorded in the source headers and `CORRESPONDENCE.md`.

## Per-node table (8 `SEALED` nodes)

| id | export | paper | hash | ax |
|---|---|---|---|---|
| `N-005` | `UCPlanar.Frozen.counterexample` | ucplanar.tex:368-373 | ✔ | std |
| `N-004` | `UCPlanar.Frozen.topological` | ucplanar.tex:222-231 | ✔ | std |
| `N-003` | `UCPlanar.Frozen.zeroCase` | ucplanar.tex:187-190 | ✔ | std |
| `N-002` | `UCPlanar.Frozen.uniformlyBounded` | ucplanar.tex:175-181 | ✔ | std |
| `N-007` | `UCPlanar.Frozen.polynomialApproximation` | ucplanar.tex:427-434 | ✔ | std |
| `N-006` | `UCPlanar.Frozen.threeBall` | ucplanar.tex:457-469 | ✔ | std |
| `N-008` | `UCPlanar.Frozen.periodicLowerBound` | ucplanar.tex:411-422 | ✔ | std |
| `N-001` | `UCPlanar.Frozen.liouville` | ucplanar.tex:161-167 | ✔ | std |

## Refute-first scope and limits

The statements are existence and exponential-bound results (`∃ ε, n₀, …`), so no finite
simulation refutes the constants; the attempt is against the shape and the paper reading.
`theorem:counterexample` is an explicit construction and was read against its lines.  The
three `FROZEN` inputs — Janiszewski's theorem (`X-002`), unicoherence of the sphere (`X-003`)
and the discrete Moser estimate (`X-007`) — are cited classical results; they are assumed only
through displayed hypotheses and are left for the ground-up proof programme.

## Conclusion

The 8 `SEALED` nodes are proved with clean closures, the frozen surface is pinned,
and the gates pass.  The audit licenses their promotion to `PROVED`.
