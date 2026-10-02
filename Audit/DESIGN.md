# Comparator design memo: vocabulary, bridges, deltas

This memo records how the four comparator pairs are built, for whoever checks
or extends them.  The files are `Audit/<Thm>/Challenge.lean`,
`Audit/<Thm>/Solution.lean`, `Audit/Support/Vocabulary.lean` (the
Mathlib-only copy of the vocabulary), `Audit/Support/Bridge.lean` (the
transports), `Audit/Support/Statements.lean` and
`Audit/StatementRegression.lean` (the local statement check).

## 0. Solution architecture

The comparator checks that the solution theorem has the same elaborated type
as the challenge theorem, constant by constant through the whole dependency
closure.  So the vocabulary constants must elaborate in the solution exactly
as in the challenge.  As in the comparator pattern of the `CoarseGraining` and
`Superdiffusion` repositories, the vocabulary is therefore compiled in a module
that imports **only Mathlib** (`Audit/Support/Vocabulary.lean`, the analogue
of their per-challenge `SolutionBasic.lean`), and `Solution.lean` imports the
repository, that module, and the bridges, and states the theorem with the
challenge's bytes.

The four challenges share one vocabulary block, byte-identical in each
(`bash Audit/check_standalone.sh --vocabulary`), so one `Vocabulary.lean`
serves all four solutions.  The block contains definitions that a given
challenge does not use (for instance the crossing conductances in the three
challenges on periodic plane graphs); they do not enter that theorem's
dependency closure.

## 1. Definitionally shared vocabulary

Every definition of the vocabulary that is neither a structure nor recursive
is a token-for-token copy of its source, over Mathlib types.  These are
definitionally equal to their counterparts, and the solutions use them
definitionally, with no rewriting:

| Vocabulary | Counterpart |
| --- | --- |
| `Site`, `unit`, `closedBall`, `netLaplacian`, `HarmonicOn` | `LatticeProb.Site`, `LatticeProb.unit`, `LatticeProb.Graph.closedBall`, `LatticeProb.Network.netLaplacian`, `LatticeProb.Network.HarmonicOn` |
| `EPlane`, `Plane`, `planeHomeo` | `Schoenflies.Plane`, `UCPlanar.Plane`, `UCPlanar.Support.planeHomeo` |
| `PlaneEmbedding.trace`, `.IsFace`, `.Incident`, `.FaceBound`, `.arcOf`, `.edgesTrace`, `insideOf` | the repository's, at `toPE E` |
| `PeriodicGraph.square`, `.ball`, `.PeriodicConductance`, `.HasBoundedDensity` | the repository's, at `toPG P` |
| `boundedDensity`, `exceptionalCount`, `UniformlyElliptic` | the repository's |
| `diagonalStep`, `crossingRelation`, `crossingGraph`, `crossingOutgoing`, `crossingConductance` | the repository's |
| `External.EdgeSplitting`, `External.Unicoherence` (at `E`), `External.MoserEstimate` (at `P`) | the repository's, at `toPE E` and `toPG P`: `Bridge.edgeSplitting`, `Bridge.unicoherence`, `Bridge.moserEstimate`, each proved by the hypothesis itself |

These identifications are not asserted: each `exact` in a solution and each
bridge above is checked by the kernel, which unfolds both sides.

## 2. Structure copies and the recursive copy

Four vocabulary declarations are structures, hence new inductive types:
`IsCond`, `PlaneEmbedding`, `PeriodicGraph` and `PeriodicPlaneGraph`.  The
bridges convert them field by field:

- `isCond_iff`: the vocabulary `IsCond G c` and `LatticeProb.Network.IsCond G c`
  are equivalent, in both directions, since the conductance hypothesis occurs
  both as a premise (Theorems 1.1, 1.2, 1.3) and in a conclusion
  (Theorem 5.1);
- `toPE`, `toPG`, `toPPG`: a vocabulary plane embedding, periodic graph and
  periodic plane graph as the repository's, with the same fields.  Only one
  field is not passed through unchanged: `edge_polygonal`, whose type mentions
  the recursive `poly`.

`poly` is recursive, so its copy is a new recursive definition.  `poly_eq`
proves it equal to `Schoenflies.poly` by induction on the vertex list, and
`isPolygonal_iff` transports `IsPolygonal` along it.

## 3. Theorem-level bridges

Each solution applies the theorem of `UCPlanar/MainTheorems.lean` to
`toPPG P` and the transported hypotheses, and closes the goal with `exact`,
converting the `IsCond` premises or conclusion with `isCond_iff`.  Everything
else in the statements (the graph, its local finiteness instance, the balls,
the densities, the harmonicity predicate) is identified definitionally.

## 4. Presentation deltas

None at the level of the displayed statements: each challenge theorem is the
statement of the corresponding theorem of `UCPlanar/MainTheorems.lean`, which
is the frozen statement of `UCPlanar/Frozen/`, with every repository and
library name replaced by its vocabulary copy.

How each statement reads the paper is recorded in
[`CORRESPONDENCE.md`](../CORRESPONDENCE.md) and [`PROOF.md`](../PROOF.md).  The
comparator does not check that reading: it checks that the library proves
exactly the displayed statement, over definitions that can be read without the
library.

## 5. What the comparator does not certify

- The cited results.  The challenges take them as hypotheses, restated in the
  vocabulary.  A proof conditional on a proposition does not show that the
  proposition is a faithful rendering of the cited theorem; that reading is
  the subject of `ASSUMPTIONS.md`.
- The faithfulness of the vocabulary to the paper.  The vocabulary is a copy
  of the definitions the repository uses, so the comparator shows that nothing
  in the statements depends on the library beyond what the vocabulary
  displays; a reader still has to check the vocabulary against the paper.

## 6. Checks beyond the local regression

- **Instance environments.**  The solutions import both the repository
  and the vocabulary, and both declare the local finiteness of a periodic
  graph as an instance (`attribute [instance] PeriodicGraph.locallyFinite`).
  `Audit/StatementRegression.lean` checks that no solution statement picked up
  a repository or library constant, in particular not the repository's
  instance.
- **The comparator's closure check.**  The local regression compares the
  solution types with the challenge-environment types up to the auxiliary proof
  lemmas that a `def` abstracts; the comparator's own closure check is
  stricter, and every pair passes it, with the Lean kernel and again with the
  independent nanoda kernel (see `Audit/COMPARATOR_RUNS.md`).
