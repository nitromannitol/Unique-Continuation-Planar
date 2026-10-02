# Comparator design memo: vocabulary, bridges, deltas

This memo records how the four comparator pairs are built, for whoever checks
or extends them.  Each pair `<Pair>` (`Liouville`, `UniformlyBounded`, `ZeroCase`,
`Counterexample`) has a directory `UCPlanarAudit/<Pair>/` with four files, and one bridge,
`UCPlanarAudit/Support/<Pair>Bridge.lean`.

- `Challenge.lean` imports `Mathlib` and nothing else.  It rebuilds from Mathlib
  primitives every object the theorem mentions, states the theorem, and ends in a single
  `sorry`.  This file is the object of trust: a reader checks what it says, not how it is
  proved.
- `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block of
  `Challenge.lean` (between `VOCABULARY-BEGIN` and `VOCABULARY-END`).  It imports only
  `Mathlib`, so the vocabulary elaborates in the solution exactly as in the challenge.
- `Solution.lean` imports the library together with `SolutionBasic` and the bridge of its
  pair, restates the challenge theorem byte-for-byte, and proves it from the library's
  verified statement.
- `comparator.json` names the challenge module, the solution module, the theorem and the
  permitted axioms (`propext`, `Classical.choice`, `Quot.sound`), with the nanoda kernel
  enabled.

`UCPlanarAudit/Support/<Pair>Bridge.lean` is part of the solution of its pair and imports
that pair's `SolutionBasic` only; no file is shared between two pairs.

## 0. Solution architecture

The comparator checks that the solution theorem has the same elaborated type
as the challenge theorem, constant by constant through the whole dependency
closure.  So the vocabulary constants must elaborate in the solution exactly
as in the challenge.  As in the comparator pattern of the `CoarseGraining` and
`Superdiffusion` repositories, the vocabulary is therefore compiled in a module
that imports **only Mathlib** (`UCPlanarAudit/<Pair>/SolutionBasic.lean`), and
`Solution.lean` imports the repository, that module, and the bridge of its pair, and states
the theorem with the challenge's bytes.

The four challenges share one vocabulary block, byte-identical in each, and
each `SolutionBasic.lean` carries that block
(`bash UCPlanarAudit/check_standalone.sh --vocabulary` compares each challenge with its
`SolutionBasic.lean`).  The block contains definitions that a given challenge does not use
(for instance the crossing conductances in the three challenges on periodic plane graphs);
they do not enter that theorem's dependency closure.

The bridges keep only what their solution uses.  `LiouvilleBridge` carries all the
conversions; `UniformlyBoundedBridge` and `ZeroCaseBridge` omit `moserEstimate`, the cited
result that their theorems do not carry; `CounterexampleBridge` carries `isCond_iff`
alone.

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

## 6. Checks by the comparator

- **Instance environments.**  The solutions import both the repository
  and the vocabulary, and both declare the local finiteness of a periodic
  graph as an instance (`attribute [instance] PeriodicGraph.locallyFinite`).  The
  comparator elaborates the solution statement and the challenge statement and compares them
  constant by constant, so a statement that picked up a repository or library constant, in
  particular the repository's instance, is rejected.
- **No local regression file.**  A local file that elaborated every solution statement in the
  challenge environment would have to import the four per-pair vocabularies at once, and they
  declare the same names.  The comparator itself checks each solution statement against its
  challenge and the closure of each solution against Mathlib, with the Lean kernel and again
  with the independent nanoda kernel; every pair passes (see
  `UCPlanarAudit/COMPARATOR_RUNS.md`).
