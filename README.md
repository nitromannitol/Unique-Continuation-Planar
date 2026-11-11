# Unique continuation on planar graphs

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee, William Cooperman and Shirshendu Ganguly,
> *Unique continuation on planar graphs*,
> Discrete Analysis 2025:16, [doi:10.19086/da.144015](https://doi.org/10.19086/da.144015);
> [arXiv:2309.13728](https://arxiv.org/abs/2309.13728).

The paper's source and the list of its differences from the arXiv version are included under
[`paper/`](paper/). The 4 main theorems of the paper are formalized and proved, in the form in
which the paper states them. Three results that the paper cites from the literature enter as
explicit hypotheses of the theorems that use them: Theorem 1.1 takes three, Theorems 1.2 and
1.3 take two, and Theorem 5.1 takes none; see
[Assumed literature inputs](#assumed-literature-inputs).

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on
two public libraries:
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability) (`LatticeProb`), a
library of lattice probability and potential theory, and the Schoenflies library
[`schoenflies-lean`](https://github.com/alonamaloh/schoenflies-lean), which supplies the planar
Jordan and crosscut theorems.

[![CI](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/comparator.yml)

## What is proved

A periodic planar graph `G = (V, E)` is drawn in the plane so that the drawing is invariant
under translation by a rank-two lattice `𝓛`, with finitely many vertex orbits. Each edge
carries a positive conductance `a`, and the Laplacian is `Δf(u) = Σ_{w∼u} a(u,w)(f(u) − f(w))`.
The classical Liouville theorem says that, when `a` is `𝓛`-invariant, a bounded harmonic
function on `G` is constant. Theorem 1.1 of the paper asks for the bound only on most of the
graph: if `a` is `𝓛`-invariant, there is `ε = ε(a) > 0` such that every `f` with `Δf = 0` on
`G` and

    lim_{n→∞} |{|f| ≤ 1} ∩ B_n| / |B_n|  ≥  1 − ε

is constant, where `B_n` is the graph-metric ball of radius `n` about a fixed origin. The proof
sets an exponential upper bound (Theorem 1.2), which rests on a topological property of the
level sets of planar harmonic functions, against an exponential lower bound (Theorem A.1 of
the appendix). Theorem 1.3 is the same argument for a function that vanishes on most of a ball,
and Theorem 5.1 shows that planarity is needed: it gives non-planar periodic conductances on
`ℤ²` with a harmonic function supported on a diagonal. The model is stated precisely in
[Standing assumptions and scope](#standing-assumptions-and-scope).

The 4 main results, formalized as stated in the paper, are collected in
[`UCPlanar/MainTheorems.lean`](UCPlanar/MainTheorems.lean). Each is proved by `exact` of its
certified counterpart in `UCPlanar/Frozen/`, so the statements displayed there are the
certified ones.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 (label `theorem:liouville`) | `UCPlanar.liouville` | a harmonic function with density at least `1 − ε` of `{\|f\| ≤ 1}` in the balls is constant |
| Theorem 1.2 (label `theorem:uniformly-bounded`) | `UCPlanar.uniformlyBounded` | exponential upper bound on a harmonic function that is large on few vertices |
| Theorem 1.3 (label `theorem:zero-case`) | `UCPlanar.zeroCase` | a harmonic function that vanishes on most of a ball vanishes on the half ball |
| Theorem 5.1 (label `theorem:counterexample`) | `UCPlanar.counterexample` | non-planar periodic conductances on `ℤ²` with a harmonic function supported on a diagonal |

**Theorem 1.1 (Liouville, `theorem:liouville`).** For a periodic plane graph `P` and a
conductance `c` invariant under the translation lattice, there is `ε > 0` such that every
function harmonic on the whole graph whose density of `{|f| ≤ 1}` in the balls `B_n` about
some vertex converges to a limit at least `1 − ε` is constant. Hypotheses: `MoserEstimate`,
`EdgeSplitting`, `Unicoherence`.

**Theorem 1.2 (uniformly bounded, `theorem:uniformly-bounded`).** There is `n₀`, and for each
ellipticity ratio `Θ > 1` there are `ε₀, A > 0`, such that for conductances in `(λ, Θλ)`,
`n ≥ n₀`, `ε < ε₀` and `f` harmonic on `B_{2n}` with `|f| > 1` on at most `ε |B_{2n}|`
vertices, `|f| ≤ exp(A √ε n)` on `B_n`. Hypotheses: `EdgeSplitting`, `Unicoherence`.

**Theorem 1.3 (zero case, `theorem:zero-case`).** There are `ε₀ > 0` and `n₀` such that for
arbitrary positive conductances, `n ≥ n₀`, `ε < ε₀` and `f` harmonic on `B_{2n}` and nonzero
on at most `ε |B_{2n}|` vertices, `f` vanishes on `B_n`. Hypotheses: `EdgeSplitting`,
`Unicoherence`.

**Theorem 5.1 (counterexample, `theorem:counterexample`).** For positive `A₁ ≠ A₂` and
`A₃ > 2 A₁² A₂² / ((A₁ - A₂)² (A₁ + A₂))` there is `A₄ > 0` such that `ℤ²` with the crossing
conductances `𝓔(A₁, A₂, A₃, A₄)` carries a harmonic function `h` with `h(0) = 1` that is
nonzero exactly on the diagonal `{x₁ = x₂}`. No hypotheses.

In Lean, the periodic plane graph is a structure `UCPlanar.PeriodicPlaneGraph V`, conductances
are `LatticeProb.Network.IsCond`, harmonicity is `LatticeProb.Network.HarmonicOn`, and the
limit in Theorem 1.1 is made explicit by `HasBoundedDensity o f ε`.

This repository formalizes every theorem, lemma and proposition of the paper: Theorems 1.1,
1.2 and 1.3, the topological lemma (Lemma 2.1), the non-planar counterexample (Theorem 5.1),
and the exponential lower bound of the appendix with its polynomial approximation lemma and
three-ball proposition (Theorem A.1, Lemma A.2, Proposition A.3).

## Corrections to the published version

The formalization follows `paper/ucplanar.tex`, a corrected text of the paper: it is
[arXiv:2309.13728v2](https://arxiv.org/abs/2309.13728v2) with corrections, and the Lean
statements transcribe the corrected text.
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) lists every difference from the
arXiv version.

## Standing assumptions and scope

1. **Every theorem is about every periodic plane graph.** Theorems 1.1 to 1.3 hold for every
   `P : UCPlanar.PeriodicPlaneGraph V` (`UCPlanar/Support/Periodic.lean`): a connected,
   locally finite graph with a proper coordinate realization, a rank-two translation action
   and finitely many vertex orbits, drawn in the plane with noncrossing polygonal edge arcs,
   translation invariant, with uniform bounds on the size and the diameter of a face. Faces
   are the connected components of the complement of the drawing. Theorem 1.1 holds for every
   conductance `c` that is a conductance of `P.graph` and invariant under the translations, and
   its `ε` depends on `c`. In Theorem 1.2 the conductances are uniformly elliptic with
   ratio `Θ`, and the constants depend on `Θ` and not on `λ`; Theorem 1.3 holds for arbitrary
   positive conductances. Theorem 5.1 is about the explicit conductances
   `UCPlanar.crossingConductance` on `ℤ²`.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit`, no
   `native_decide` and no new `axiom`. The axiom report of each main theorem consists of
   exactly `propext`, `Classical.choice` and `Quot.sound`. The main theorems take 3 cited
   results as explicit hypotheses, listed under
   [Assumed literature inputs](#assumed-literature-inputs); nothing else is assumed.
3. **What is not formalized.** The introduction's survey of related work and applications, the
   remark following Theorem 1.3, and the figures.
4. **Conventions.**
   - Conductances, the Laplacian and harmonicity are those of Lattice-Probability
     (`LatticeProb.Network.IsCond`, `netLaplacian`, `HarmonicOn`). The paper's Laplacian is
     the negative of `netLaplacian`; their zero equations agree.
   - The Lean statement of Theorem 1.1 makes the limit explicit: the density of `{|f| ≤ 1}`
     in `B_n` converges to a real number `d` with `1 − ε ≤ d`.
   - In each frozen statement whose conclusion has a real existential constant, the
     quantifier order is checked mechanically (`tools/check_constants.py`): no radius,
     function, density or conductance parameter is bound before it.
5. **Explicit versus implicit.** The reduction in Step 1 of the zero case, which deletes and
   contracts finite edge-connected components, is not formalized. The statement is proved
   directly for the periodic plane graph, with the surrounding cycles supplied by the cited
   plane inputs.
6. **Statements without a formal counterpart.** Every theorem, lemma and proposition of the
   paper has a registered Lean declaration. The correspondence table in
   [`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps the registered statements to Lean
   declarations node by node, and [`PROOF.md`](PROOF.md) describes the mathematics of the
   proof and the Lean tree.

## Assumed literature inputs

Three results that the paper cites from the literature are stated in Lean as propositions in
`UCPlanar/External/`, and every theorem whose proof uses one takes it as an explicit
hypothesis, so the statement shows exactly which of them it rests on.
[`ASSUMPTIONS.md`](ASSUMPTIONS.md) lists the three with their verbatim Lean statements. They
are **not proved here**. Two further results the paper cites, the classical Liouville theorem
for the periodic network and the discrete Remez inequality, are proved here.

| Hypothesis | Content | Source | Used by |
| --- | --- | --- | --- |
| `UCPlanar.External.EdgeSplitting` (`hES`) | Janiszewski's theorem at a point, for the drawings of two finite edge sets of a plane graph: for disjoint finite edge sets meeting in at most one vertex, a point enclosed by their union is enclosed by one of the two | Newman, *Elements of the Topology of Plane Sets of Points*, Chapter V, Theorem 9.3; Mohar and Thomassen, *Graphs on Surfaces*, Chapter 2; Thomassen, *The Jordan-Schoenflies theorem and the classification of surfaces*, Amer. Math. Monthly 99 (1992) 116-130 | Theorems 1.1, 1.2, 1.3 |
| `UCPlanar.External.Unicoherence` (`hU`) | Unicoherence of the sphere, in the form that the frontier of every bounded face of a connected plane graph is connected | Newman, *Elements of the Topology of Plane Sets of Points*, Chapter VI; Mohar and Thomassen, *Graphs on Surfaces*, Chapter 2; Thomassen, Amer. Math. Monthly 99 (1992) 116-130 | Theorems 1.1, 1.2, 1.3 |
| `UCPlanar.External.MoserEstimate` (`hMos`) | The discrete Moser estimate on a periodic network: for nested squares `Q_r ⊆ Q_s` and `f` harmonic on `Q_s`, the supremum of `\|f\|` over `Q_r` is at most `C / (s − r)` times the `ℓ²` norm of `f` over `Q_s`, with `C` independent of the two scales | Delmotte, *Parabolic Harnack inequality and estimates of Markov chains on graphs*, Rev. Mat. Iberoamericana 15 (1999) 181-232, Proposition 5.3 | Theorem 1.1 |

## Registered statements

The generated summary below comes from [`ledger/manifest.yaml`](ledger/manifest.yaml).

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **11 registered nodes: 3 `FROZEN`, 8 `PROVED`.** 8 theorem(s) are proved and machine-checked: no `sorry`, no axiom added by this development, and an axiom closure of exactly Lean's three standard axioms `propext`, `Classical.choice` and `Quot.sound`. 3 result(s) are cited from the literature and stated as explicit hypotheses rather than proved here, so the theorems that use them are proved conditional on them.

Counts are generated from `ledger/manifest.yaml` by
`python3 tools/sync_docs.py`. Run `python3 tools/check_axioms.py`
to check registered axiom closures.

<!-- STATUS-END -->

Every statement of the paper is registered: one Lean declaration per theorem, lemma or
proposition, and one proposition per cited result that is assumed. A registered statement's
text between the lines `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` is pinned by
the SHA-256 of those bytes in [`ledger/manifest.yaml`](ledger/manifest.yaml), together with the
line range in `paper/ucplanar.tex` and, for the paper's numbered statements, the `\label` it
transcribes; the proof after the end marker may be rewritten freely. In the manifest, a
registered statement is `PROVED` when it is proved with an axiom closure of exactly the three
standard axioms, and `FROZEN` when it is a cited result assumed rather than proved. Every
registered statement is pinned by hash; only the `FROZEN` ones are assumed.

## Guarantees

- **No `sorry`.** The library has none, and `tools/check_manifest.py` rejects any `sorry`
  outside a registered `DRAFT_SORRY` node, of which there is none. The 4 comparator challenges
  under [`UCPlanarAudit/`](UCPlanarAudit/) each contain one intentional statement-level
  `sorry`, which the corresponding solution file proves.
- **Standard axioms only.** The axiom report of each of the 4 main theorems lists exactly
  `propext`, `Classical.choice` and `Quot.sound`.
  [`UCPlanar/Meta/AxiomsAudit.lean`](UCPlanar/Meta/AxiomsAudit.lean) prints the reports, and
  `python3 tools/check_axioms.py` checks the axiom closure of every registered statement. The
  cited results are hypotheses, not axioms.
- **Builds from a clean checkout.** In continuous integration, `lake build` of a fresh
  checkout completes 9,004 jobs without error, and the build fails on any warning or `sorry`
  warning.
- **Independent check of the statements.** Each of the 4 main theorems is restated in
  [`UCPlanarAudit/`](UCPlanarAudit/) using mathlib alone, with no project or library
  definitions, one challenge file per theorem
  ([`Liouville`](UCPlanarAudit/Liouville/Challenge.lean),
  [`UniformlyBounded`](UCPlanarAudit/UniformlyBounded/Challenge.lean),
  [`ZeroCase`](UCPlanarAudit/ZeroCase/Challenge.lean) and
  [`Counterexample`](UCPlanarAudit/Counterexample/Challenge.lean)). Each challenge rebuilds the
  model from mathlib primitives (lattice sites, graph balls, conductances, the network
  Laplacian and harmonic functions as in Lattice-Probability; polygonal sets as in the
  Schoenflies library; plane embeddings, faces, periodic plane graphs and their density
  notions; the crossing conductances of Theorem 5.1; and the cited results it assumes). The
  solution file proves the byte-identical statement from the library through the bridge of its
  pair in `UCPlanarAudit/Support/`, over a mathlib-only copy of the challenge's vocabulary
  (`SolutionBasic.lean`), and [leanprover/comparator](https://github.com/leanprover/comparator)
  checks that the statement is proved, with only the three standard axioms, through
  independent implementations of the Lean kernel. See
  [`UCPlanarAudit/README.md`](UCPlanarAudit/README.md) and
  [`UCPlanarAudit/COMPARATOR_RUNS.md`](UCPlanarAudit/COMPARATOR_RUNS.md).
- **Pinned toolchain and dependencies.** Lean `v4.32.0`; mathlib at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997`, Lattice-Probability at commit
  `9d44b4d4670df393bb86ac5a4e042f215001cddf` and schoenflies-lean at commit
  `05a43d29cde026618777db3d4e4316204ccca237`, recorded in [`lean-toolchain`](lean-toolchain),
  [`lakefile.lean`](lakefile.lean) and [`lake-manifest.json`](lake-manifest.json) (see
  [Building](#building)).
- **The paper is part of the repository.** The statement map refers to the version in
  [`paper/`](paper/), pinned to the SHA-256
  `0a97204bffb598a59580eb3fc8537af56ab4eb79f76900086cdadc9b6b00b311` of `paper/ucplanar.tex`.

## Size

The library contains 171 Lean files with 25,821 physical lines, on top of mathlib,
Lattice-Probability and schoenflies-lean. The comparator sources (16 files, 3,156 lines) are
counted separately.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

The 2 source dependencies, Lattice-Probability and schoenflies-lean, have no prebuilt cache, so
the first build compiles them as well as the library. `import UCPlanar` loads the whole
development, and `import UCPlanar.MainTheorems` loads the main theorems and what they use.

The dependencies are public repositories, pinned to exact commits in
[`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `9d44b4d4670df393bb86ac5a4e042f215001cddf`.
- schoenflies-lean: `https://github.com/alonamaloh/schoenflies-lean` at
  `05a43d29cde026618777db3d4e4316204ccca237`.

To reproduce the axiom reports and build the comparator libraries:

```bash
lake build UCPlanar.Meta.AxiomsAudit   # print the axioms of the four main theorems
lake build UCPlanarAudit               # the comparator challenges and solutions
```

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`).

| command | what it guarantees |
|---|---|
| `python3 tools/check_manifest.py` | every frozen statement's bytes match its recorded SHA-256 and declaration name, every file under `UCPlanar/Frozen/` belongs to exactly one node, no `axiom`, `admit` or `sorryAx` token occurs in the source tree, and `sorry` occurs only in nodes in state `DRAFT_SORRY` (none is); needs neither Lake nor network |
| `python3 tools/check_axioms.py` | runs `#print axioms` on every registered export; each closure contains only `propext`, `Classical.choice` and `Quot.sound` |
| `python3 tools/check_constants.py` | in each frozen statement whose conclusion has a real existential constant, no radius, function, density or conductance parameter is bound before it |
| `python3 tools/check_warnings.py` | runs `lake build UCPlanar` and fails if the build fails or emits any warning other than the Lake notice about the mathlib URL and the `sorry` warnings expected for `DRAFT_SORRY` nodes (none is registered) |

Also in `tools/`: `paper_anchors.py` checks that the line ranges in the manifest match the
paper's `\label`s (`--fix` repairs them); `sync_docs.py` checks (`--write` regenerates) the
status block of this file and the registered-statements table of `CORRESPONDENCE.md`;
`assumptions.py` regenerates `ASSUMPTIONS.md` (`--check` verifies it is current);
`certificate.py` regenerates `CERTIFICATE.md` (`--check` compares it with the file on disk);
`freeze.py` registers or refreshes a node in the manifest. See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for further building notes.

## Running the comparators

Each comparator pair has a configuration `UCPlanarAudit/<Pair>/comparator.json`, for `<Pair>`
one of `Liouville`, `UniformlyBounded`, `ZeroCase` and `Counterexample`, that permits exactly
`propext`, `Classical.choice` and `Quot.sound` and enables the independent nanoda kernel. The
comparator checks that the solution proves the challenge statement, compares their dependency
closures, and replays the proof with the Lean and NanoDa kernels.

To run one pair locally, build `leanprover/comparator`, `lean4export`, `landrun` and
`nanoda_lib` at the revisions pinned in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) (also recorded in
[`UCPlanarAudit/COMPARATOR_RUNS.md`](UCPlanarAudit/COMPARATOR_RUNS.md)), and from the
repository root run:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator UCPlanarAudit/<Pair>/comparator.json
```

A pair passes when the comparator prints `Your solution is okay!`. The comparator workflow
runs the four pairs one after the other in a single job on GitHub-hosted runners.

There are two continuous-integration workflows: **CI** builds the library, builds the axiom
audit and checks the frozen statements; **Comparator audit** checks all 4 challenge/solution
pairs. Both run on pushes to `main` that change Lean files, `tools/`, `paper/`, `ledger/`,
`formalization.yaml` or the build configuration, and can be started manually from the
[Actions page](https://github.com/nitromannitol/Unique-Continuation-Planar/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
UCPlanar.lean             the root module, importing the whole library
UCPlanar/
  MainTheorems.lean       the main theorems, stated in full
  Frozen/                 the certified statement surface, one frozen statement per file
  External/               the three cited results, each a frozen Prop
  Support/                the definitions and lemmas the frozen statements are proved from:
                          periodic and plane graphs, the topological step, polynomial
                          approximation (Poly/), the three-ball and exponential bounds,
                          the Liouville step, the counterexample, the discrete Remez inequality
  Meta/AxiomsAudit.lean   the axiom report, compiled by `lake build`, not imported by the root
  Basic.lean              bounded density, exceptional count, uniform ellipticity
UCPlanarAudit/            the mathlib-only restatements and their solutions
ASSUMPTIONS.md            the cited results assumed, with their Lean statements (generated)
CORRESPONDENCE.md         paper to Lean, node by node
PROOF.md                  the mathematics of the proof and the Lean tree
CERTIFICATE.md            generated record of the toolchain, the build, each node's axiom
                          closure and the SHA-256 of each frozen statement
ledger/manifest.yaml      one row per registered statement: hash, paper source, state
paper/                    ucplanar.tex, the paper pinned by the SHA-256 in
                          ledger/manifest.yaml; CHANGES_FROM_ARXIV.md, every difference between
                          it and arXiv:2309.13728v2; ucplanar-arxiv.tex, the unmodified arXiv
                          source, with arxiv/ holding its class files, bibliography and figures
tools/                    the checkers and generators listed under Building
.github/workflows/        the CI build and the comparator audit
formalization.yaml        models, tooling, cost, status and review (mathlib-initiative v0.4)
CITATION.cff              citation metadata
CONTRIBUTING.md           building notes and the elaboration policy for new files
lakefile.lean, lake-manifest.json, lean-toolchain   the pinned build
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and
DeepSeek, under the direction of the author. Every proof is checked by the Lean kernel. The
models, tooling, cost and review status are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**.  The paper it formalizes
(arXiv:2309.13728) is joint work of Ahmed Bou-Rabee, William Cooperman and
Shirshendu Ganguly.  If you use this formalization, please cite it using the
metadata in [`CITATION.cff`](CITATION.cff).

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4), the shared library
[`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability),
and the Schoenflies library
[`schoenflies-lean`](https://github.com/alonamaloh/schoenflies-lean) of Álvaro
Begué, which supplies the planar Jordan and crosscut theorems; the comparator
audit in [`UCPlanarAudit/`](UCPlanarAudit/) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).  The paper source in `paper/` is included for
reference and is not covered by the Apache license.
