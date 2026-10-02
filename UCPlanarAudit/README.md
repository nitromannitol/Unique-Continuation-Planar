# UCPlanarAudit Comparator Surface

This directory contains Mathlib-only comparator challenges for the four main
theorems of the formalization of *Unique continuation on planar graphs*
(Bou-Rabee, Cooperman and Ganguly, Discrete Analysis 2025:16): Theorems 1.1,
1.2 and 1.3 and Theorem 5.1.  Each comparator lives in its own subdirectory:

| Directory | Paper statement | Checked theorem | Library theorem |
| --- | --- | --- | --- |
| `Liouville/` | Theorem 1.1, `theorem:liouville` | `UCPlanarAudit.liouville` | `UCPlanar.liouville` |
| `UniformlyBounded/` | Theorem 1.2, `theorem:uniformly-bounded` | `UCPlanarAudit.uniformlyBounded` | `UCPlanar.uniformlyBounded` |
| `ZeroCase/` | Theorem 1.3, `theorem:zero-case` | `UCPlanarAudit.zeroCase` | `UCPlanar.zeroCase` |
| `Counterexample/` | Theorem 5.1, `theorem:counterexample` | `UCPlanarAudit.counterexample` | `UCPlanar.counterexample` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem, states the theorem, and ends with one
`sorry`, the proof being checked.  The definitions form one vocabulary block,
between `-- VOCABULARY-BEGIN` and `-- VOCABULARY-END`, byte-identical in all
four challenges: lattice sites, graph-metric balls, conductances, the network
Laplacian and harmonic functions; polygonal sets of the Euclidean plane; plane
embeddings, their traces and faces, the drawing of an edge set and the bounded
complementary components of a set; periodic graphs and periodic plane graphs,
with their squares, balls, periodic conductances, bounded-value densities,
exceptional counts and uniform ellipticity; the crossing graph and crossing
conductances of Theorem 5.1; and the three cited results.

## What Is Checked

The theorems are conditional on results the paper cites without proof, and so
are the challenges: each carries, as explicit hypotheses, the cited results
its library theorem uses, restated in the vocabulary.

| Directory | Cited results carried as hypotheses |
| --- | --- |
| `Liouville/` | `External.MoserEstimate` (on `P.toPeriodicGraph` and `c`), `External.EdgeSplitting` and `External.Unicoherence` (on `P.embedding`) |
| `UniformlyBounded/`, `ZeroCase/` | `External.EdgeSplitting` and `External.Unicoherence` (on `P.embedding`) |
| `Counterexample/` | none |

- **`Liouville`** (Theorem 1.1): for a periodic plane graph `P` and a
  conductance `c` invariant under the translation lattice, there is `ε > 0`
  such that every function harmonic on the whole graph, whose density of
  `{|f| ≤ 1}` in the graph-metric balls about some vertex converges to a limit
  at least `1 - ε`, is constant.
- **`UniformlyBounded`** (Theorem 1.2): there is `n₀`, and for each
  ellipticity ratio `Θ > 1` there are `ε₀, A > 0`, such that for conductances
  in `(λ, Θλ)`, `n ≥ n₀`, `ε < ε₀` and `f` harmonic on `B_{2n}` with `|f| > 1`
  on at most `ε |B_{2n}|` vertices of `B_{2n}`, `|f| ≤ exp(A √ε n)` on `B_n`.
- **`ZeroCase`** (Theorem 1.3): there are `ε₀ > 0` and `n₀` such that for
  arbitrary positive conductances, `n ≥ n₀`, `ε < ε₀` and `f` harmonic on
  `B_{2n}` and nonzero on at most `ε |B_{2n}|` vertices of `B_{2n}`, `f`
  vanishes on `B_n`.
- **`Counterexample`** (Theorem 5.1): for positive `a ≠ b` and
  `t > 2 a² b² / ((a - b)² (a + b))` there is `d > 0` such that the crossing
  graph on `ℤ²` with conductances `crossingConductance a b t d` carries a
  harmonic function `f` with `f 0 = 1` and `f x ≠ 0 ↔ x 0 = x 1`.

## Definition Provenance

The challenge definitions are statement-level copies of the definitions the
repository uses to state the theorems, in the namespace `UCPlanarAudit`.

| Challenge declaration | Source |
| --- | --- |
| `Site`, `unit` | `LatticeProb/Site.lean` (Lattice-Probability) |
| `closedBall` | `LatticeProb/Graph/Basic.lean` (Lattice-Probability) |
| `IsCond`, `netLaplacian`, `HarmonicOn` | `LatticeProb/Network/Basic.lean` (Lattice-Probability) |
| `EPlane`, `poly`, `IsPolygonal` | `Schoenflies/Plane.lean`, `Schoenflies/PolyPath.lean`, `Schoenflies/Polygonal.lean` (schoenflies-lean) |
| `Plane`, `planeHomeo`, `PlaneEmbedding`, `PlaneEmbedding.trace`, `.IsFace`, `.Incident`, `.FaceBound` | `UCPlanar/Support/Planar.lean` |
| `PlaneEmbedding.arcOf`, `PlaneEmbedding.edgesTrace` | `UCPlanar/Support/TopoEdgeSet.lean` |
| `insideOf` | `UCPlanar/Support/TopoTransport.lean` |
| `PeriodicGraph`, `PeriodicPlaneGraph`, `PeriodicGraph.square`, `.ball`, `.PeriodicConductance` | `UCPlanar/Support/Periodic.lean` |
| `boundedDensity`, `exceptionalCount`, `UniformlyElliptic` | `UCPlanar/Basic.lean` |
| `PeriodicGraph.HasBoundedDensity` | `UCPlanar/Support/Growth.lean` |
| `diagonalStep`, `crossingRelation`, `crossingGraph`, `crossingOutgoing`, `crossingConductance` | `UCPlanar/Support/CrossingGraph.lean` |
| `External.EdgeSplitting`, `External.Unicoherence`, `External.MoserEstimate` | `UCPlanar/External/{EdgeSplitting,Unicoherence,MoserEstimate}.lean` |

The repository's `open scoped Classical` is reproduced in the same places, so
that the decidability instances inside the copied definitions are the
repository's.

## Solutions

Each pair has the same four files.

| File | Content |
| --- | --- |
| `<Pair>/Challenge.lean` | imports `Mathlib` only; vocabulary block, statement, one `sorry` |
| `<Pair>/SolutionBasic.lean` | imports `Mathlib` only; the vocabulary block of the challenge, copied mechanically |
| `<Pair>/Solution.lean` | imports the library, `<Pair>/SolutionBasic.lean` and `Support/<Pair>Bridge.lean`; the byte-identical statement with its proof |
| `<Pair>/comparator.json` | challenge module, solution module, theorem name, permitted axioms, nanoda enabled |

Each `Solution.lean` proves the byte-identical statement from the corresponding theorem of
`UCPlanar/MainTheorems.lean` through the bridge `Support/<Pair>Bridge.lean`, which converts the
structures of the vocabulary to the repository's field by field (see [`DESIGN.md`](DESIGN.md)).
There is no file shared between two solutions.  The comparator itself checks that each
solution theorem has the statement of its challenge, constant by constant through the whole
dependency closure, and that its closure rests on Mathlib and the permitted axioms alone.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and enable the nanoda replay.  Each challenge elaborates standalone against this repository's
Mathlib toolchain, e.g.

```bash
bash UCPlanarAudit/check_standalone.sh UCPlanarAudit/Liouville/Challenge.lean
bash UCPlanarAudit/check_standalone.sh --vocabulary   # Challenge vs SolutionBasic, per pair
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'` warning per challenge;
the second command checks that the vocabulary block of each challenge is byte-identical to
that of its `SolutionBasic.lean`.  The solutions build with

```bash
lake build UCPlanarAudit
```

Then, with `leanprover/comparator`, `lean4export` (at the toolchain's tag), `landrun` and
`nanoda` built at the pins in [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md), from the repository
root:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator UCPlanarAudit/<Pair>/comparator.json
```

expecting `Your solution is okay!`.

**Status.**  All four solutions build.  `leanprover/comparator` passes on all four pairs, with
the Lean kernel and again with the independent nanoda kernel.  Results and reproduction steps
are in [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md).  The workflow
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) runs the same check
on request.
