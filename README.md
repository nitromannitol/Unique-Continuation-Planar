# Unique continuation on planar graphs

[![CI](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/comparator.yml)

A Lean 4 formalization of the paper

> Ahmed Bou-Rabee, William Cooperman and Shirshendu Ganguly,
> [*Unique continuation on planar graphs*](https://arxiv.org/abs/2309.13728),
> Discrete Analysis 2025:16, [doi:10.19086/da.144015](https://doi.org/10.19086/da.144015).

The paper proves a Liouville theorem on periodic planar graphs with periodic edge weights: a
harmonic function that is bounded by 1 on all but a small fraction of the graph is constant. The
key step is a unique continuation result, proved by a topological argument about level sets in
the plane. Every numbered result of the paper is proved in Lean, with no `sorry` and only the
standard axioms, and so are the results that the paper quotes from other works. Nothing is assumed
beyond the setting of the paper, whose corrected text is in [`paper/`](paper/).

## The paper

A *periodic planar graph* `G` is a connected, locally finite graph drawn in the plane with
polygonal edges, so that the drawing is invariant under translation by a lattice `𝓛 ≅ ℤ²` and has
finitely many orbits of vertices and edges. The square, hexagonal, triangular and kagome lattices
are examples. Each edge carries a positive weight, the *conductance* `a`, and the Laplacian is
`Δf(u) = Σ_{w∼u} a(u,w)(f(u) − f(w))`. A function is *harmonic* where `Δf = 0`. Let `B_n` be the
ball of radius `n` about a fixed vertex in the graph distance.

When `a` is invariant under `𝓛`, every bounded harmonic function on `G` is constant. The paper
asks for the bound only on most of the graph. Buhovsky, Logunov, Malinnikova and Sodin proved
this on `ℤ²` with unit conductances; the paper extends it to periodic planar graphs with a new,
geometric proof.

- **Theorem 1.1 (Liouville).** If `a` is invariant under `𝓛`, there is `ε > 0` such that every
  harmonic function on `G` with `|f| ≤ 1` on a fraction at least `1 − ε` of the balls `B_n`, in the
  limit, is constant.
- **Theorem 1.2.** A harmonic function on `B_{2n}` with `|f| > 1` on few vertices is at most
  `exp(A √ε n)` on `B_n`. The proof uses that, in the plane, the sets `{f > 0}` and `{f < 0}`
  cannot cross (Lemma 2.1).
- **Theorem 1.3.** A harmonic function on `B_{2n}` that vanishes on most of `B_{2n}` vanishes on
  `B_n`, for any positive conductances.
- **Theorem A.1.** If `a` is invariant under `𝓛`, a nonconstant harmonic function that is bounded
  on most of the graph grows at least exponentially. With Theorem 1.2 this gives Theorem 1.1.
- **Theorem 5.1.** Planarity is needed: there are non-planar periodic conductances on `ℤ²` with a
  harmonic function supported on a diagonal.

Precisely:

**Theorem 1.1.** Let `a` be invariant under `𝓛`. There is `ε = ε(a) > 0` such that every `f` with
`Δf = 0` on `G` and `lim_{n→∞} |{|f| ≤ 1} ∩ B_n| / |B_n| ≥ 1 − ε` is constant.

**Theorem 1.2.** There is `n₀`, and for each ratio `Θ > 1` there are `ε₀, A > 0`, such that for
conductances in `(λ, Θλ)`, `n ≥ n₀`, `ε < ε₀` and `f` harmonic on `B_{2n}` with `|f| > 1` on at most
`ε |B_{2n}|` vertices, `|f| ≤ exp(A √ε n)` on `B_n`.

**Theorem 1.3.** There are `ε₀ > 0` and `n₀` such that for any positive conductances, `n ≥ n₀`,
`ε < ε₀` and `f` harmonic on `B_{2n}` and nonzero on at most `ε |B_{2n}|` vertices, `f = 0` on `B_n`.

**Theorem 5.1.** For positive `A₁ ≠ A₂` and `A₃ > 2 A₁² A₂² / ((A₁ − A₂)² (A₁ + A₂))` there is
`A₄ > 0` such that `ℤ²` with the crossing conductances `𝓔(A₁, A₂, A₃, A₄)` carries a harmonic
function `h` with `h(0) = 1` that is nonzero exactly on the diagonal `{x₁ = x₂}`.

## The main theorems in Lean

| Paper | Lean declaration | File |
| --- | --- | --- |
| Theorem 1.1 | `UCPlanar.Proved.liouville_of_periodic` | [`UCPlanar/Proved/MoserEstimate.lean`](UCPlanar/Proved/MoserEstimate.lean) |
| Theorem 1.2 | `UCPlanar.Proved.uniformlyBounded` | [`UCPlanar/Proved/Main.lean`](UCPlanar/Proved/Main.lean) |
| Theorem 1.3 | `UCPlanar.Proved.zeroCase` | [`UCPlanar/Proved/Main.lean`](UCPlanar/Proved/Main.lean) |
| Theorem 5.1 | `UCPlanar.counterexample` | [`UCPlanar/MainTheorems.lean`](UCPlanar/MainTheorems.lean) |

Their only hypotheses are the setting of the paper.

How to read the statements: a periodic plane graph is a `UCPlanar.PeriodicPlaneGraph V`;
conductances are `LatticeProb.Network.IsCond`, and harmonicity is `LatticeProb.Network.HarmonicOn`.
The limit in Theorem 1.1 is made explicit by `UCPlanar.PeriodicGraph.HasBoundedDensity`: the
density of `{|f| ≤ 1}` in `B_n` converges to a number at least `1 − ε`. The paper's Laplacian is the
negative of `LatticeProb.Network.netLaplacian`; the two have the same harmonic functions.

## All numbered results

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `UCPlanar.Proved.liouville_of_periodic` | A harmonic function with `\|f\| ≤ 1` on a density at least `1 − ε` of the balls is constant. |
| Theorem 1.2 | `UCPlanar.Proved.uniformlyBounded` | An exponential upper bound for a harmonic function that is large on few vertices. |
| Theorem 1.3 | `UCPlanar.Proved.zeroCase` | A harmonic function that vanishes on most of `B_{2n}` vanishes on `B_n`. |
| Lemma 2.1 | `UCPlanar.Frozen.topological` | Let `Z ⊆ γ` for a cycle `γ`, and `P`, `M` disjoint sets inside `γ` whose components meet `γ ∖ Z`. If face paths join each point of `Z` to both `P` and `M`, then `\|Z\| ≤ α \|γ\|` for some `α < 1`. |
| Remark 3.1, first sentence | `UCPlanar.Proved.zeroCase_of_sparseShell` | Theorem 1.3 holds with the density hypothesis replaced by a bound on the nonzero vertices near one sphere. |
| Remark 3.1, second sentence | `UCPlanar.Proved.eq_zero_of_sparseShells` | A function harmonic on `G` with that bound for arbitrarily large `n` is zero. |
| Theorem 5.1 | `UCPlanar.counterexample` | Non-planar periodic conductances on `ℤ²` with a harmonic function supported on a diagonal. |
| Theorem A.1 | `UCPlanar.Proved.periodicLowerBound` | A harmonic function bounded on most of every scale from `√N` to `2N`, and at least `2` somewhere in `Q_{√N}`, exceeds `exp(bN)` on `Q_N`. |
| Lemma A.2 | `UCPlanar.Proved.polynomialApproximation` | A harmonic function on `Q_{3R}` is approximated on each lattice orbit by a polynomial of low degree. |
| Proposition A.3 | `UCPlanar.Proved.threeBall` | The three-ball bound `\|f\| ≤ C √M + C exp(−c₀ N) M` on `Q_{2N}`. |

Here `Q_N` is the square `{max(|x|, |y|) ≤ N}` of the plane. Step 1 of the proof of Theorem 1.3
rests on two facts, which are proved as well. A harmonic function is constant on a finite piece
attached at one vertex (`UCPlanar.Proved.stepOne_cutVertex`). A finite piece with two exits can be
replaced by one edge carrying its effective conductance (`UCPlanar.Proved.stepOne_twoExits`).

The proofs use three results from other works: Janiszewski's theorem and the unicoherence of the
sphere, two facts of plane topology, and a discrete Moser estimate (Delmotte 1999, Proposition
5.3). All three are proved in Lean, in the form the paper uses. So are the classical Liouville
theorem for periodic conductances and the discrete Remez inequality (Buhovsky, Logunov,
Malinnikova and Sodin, Corollary 2.2).

## Corrections

The Lean statements follow [`paper/ucplanar.tex`](paper/ucplanar.tex), the text of
[arXiv:2309.13728v2](https://arxiv.org/abs/2309.13728v2) with corrections.
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) lists the 30 changes, each with its
reason; `diff -u paper/ucplanar-arxiv.tex paper/ucplanar.tex` consists of exactly these changes.

- **Statements.** The corrected abstract and the recalled Liouville theorem assume periodic
  conductances, without which they are false. The definition of a periodic planar graph adds the
  hypotheses that the arguments use: connectedness, finitely many orbits, a proper drawing and
  bounded faces. Appendix A assumes periodic conductances throughout, as its proofs use.
- **Lemma 2.1.** The region of hypothesis (2) is the bounded component of the plane minus `γ`. The
  constant depends on the maximum degree as well as on the face size.
- **Theorem 5.1** asks `h(0) = 1`, so that the zero function is excluded. **Theorem A.1** and
  **Proposition A.3** assume harmonicity, and Proposition A.3 an outer square `Q_{kN}` with
  `k ≥ 4` in place of `Q_{4N}`.
- **Remark 3.1.** The printed statement about contours is false; the corrected remark bounds the
  nonzero vertices near one sphere.
- The other changes correct proofs and one figure caption.

## Scope

- **Every periodic plane graph.** Theorems 1.1 to 1.3 hold for every
  `P : UCPlanar.PeriodicPlaneGraph V` ([`UCPlanar/Support/Periodic.lean`](UCPlanar/Support/Periodic.lean)):
  a connected, locally finite graph with a rank-two translation action and finitely many vertex
  orbits, drawn in the plane with noncrossing polygonal edges, with uniform bounds on the size and
  diameter of a face. Faces are the components of the complement of the drawing.
- **Conductances.** In Theorem 1.1 the conductance is invariant under the translations, and `ε`
  depends on it. In Theorem 1.2 the conductances are uniformly elliptic with ratio `Θ`, and the
  constants depend on `Θ` but not on `λ`. Theorem 1.3 holds for any positive conductances.
- **Constants.** In every statement, each real constant is chosen before the radii, the functions
  and the densities, so it is a genuine constant; `tools/check_constants.py` checks this.
- **Step 1 of Theorem 1.3.** The Lean proof of Theorem 1.3 works on `G` itself, without the reduced
  graph of Step 1, so the facts used only to locate the pieces of Step 1 are not formalized.
- **Remark 3.1** asks for harmonicity on `B_{Kn}` for a graph constant `K ≥ 2` in place of
  `B_{2n}`; [`UCPlanar/Proved/ZeroRemark.lean`](UCPlanar/Proved/ZeroRemark.lean) gives the reason.
  For a function harmonic on all of `G` this is no restriction.
- **Not formalized.** The survey of related work and applications in the introduction, and the
  figures.

## Checking the proofs

- **No `sorry`, no `admit`, no new `axiom`.** `tools/check_manifest.py` rejects any `axiom`, `admit`
  or `sorryAx` token and any `sorry` in the library. Each comparator challenge under
  [`UCPlanarAudit/`](UCPlanarAudit/) contains one intentional `sorry` at the statement, which the
  matching solution proves.
- **Standard axioms only.** [`UCPlanar/Meta/AxiomsAudit.lean`](UCPlanar/Meta/AxiomsAudit.lean)
  prints the axioms of the main theorems and of the other results, and `tools/check_axioms.py`
  checks that every declaration listed in [`ledger/manifest.yaml`](ledger/manifest.yaml) depends
  only on `propext`, `Classical.choice` and `Quot.sound`.
- **Pinned statements.** The manifest pins the text of each statement by its SHA-256 hash, with
  the line range and `\label` of `paper/ucplanar.tex` that it transcribes.
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps the statements to the paper, and
  [`PROOF.md`](PROOF.md) describes the mathematics of the proof and the Lean tree.
- **Independent check of the statements.** Each main theorem has a comparator pair in
  `UCPlanarAudit/<Name>Unconditional/`. A `Challenge.lean` restates the theorem with mathlib alone,
  rebuilding every definition it uses, and a `Solution.lean` proves it from the library.
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement is
  proved, with only the standard axioms, through two independent implementations of the Lean
  kernel. Four further pairs restate the forms in [`UCPlanar/MainTheorems.lean`](UCPlanar/MainTheorems.lean),
  which take the quoted results as hypotheses. See [`UCPlanarAudit/README.md`](UCPlanarAudit/README.md).
- **Continuous integration.** The **CI** workflow builds the library without warnings, builds the
  axiom audit and checks the pinned statements against their hashes. The **Comparator audit**
  workflow runs the comparator on the eight pairs.
- **The paper is part of the repository.** `paper/ucplanar.tex` has SHA-256
  `0a97204bffb598a59580eb3fc8537af56ab4eb79f76900086cdadc9b6b00b311`.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

The manifest `ledger/manifest.yaml` pins the text of 17 statements: 14 theorems and 3 results quoted from other works. Every theorem is proved. Every quoted result is proved in Lean, by the declaration that the manifest names. This paragraph is generated from the manifest by `python3 tools/sync_docs.py`.

<!-- STATUS-END -->

The library (`UCPlanar.lean` and `UCPlanar/`) contains 198 Lean files with 29,089 lines, built on
mathlib, Lattice-Probability and schoenflies-lean.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get                     # prebuilt mathlib
lake build                             # the library
lake build UCPlanar.Meta.AxiomsAudit   # the axiom reports
lake build UCPlanarAudit               # the comparator challenges and solutions
```

Lattice-Probability and schoenflies-lean have no prebuilt cache, so the first build compiles them
as well as the library. `import UCPlanar` loads the whole development. The dependencies are public
repositories, pinned in [`lake-manifest.json`](lake-manifest.json):

- Lean `v4.32.0`; mathlib: `https://github.com/leanprover-community/mathlib4` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `9d44b4d4670df393bb86ac5a4e042f215001cddf`.
- schoenflies-lean: `https://github.com/alonamaloh/schoenflies-lean` at
  `05a43d29cde026618777db3d4e4316204ccca237`, which supplies the planar Jordan and crosscut
  theorems.

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`):

| command | what it checks |
|---|---|
| `python3 tools/check_manifest.py` | every pinned statement matches its recorded SHA-256 and declaration name, and no `axiom`, `admit`, `sorryAx` or `sorry` occurs in the source; needs neither Lake nor network |
| `python3 tools/check_axioms.py` | every pinned statement depends only on `propext`, `Classical.choice` and `Quot.sound` |
| `python3 tools/check_constants.py` | in every pinned statement, each real constant is chosen before the radii, functions and densities |
| `python3 tools/check_warnings.py` | `lake build UCPlanar` succeeds with no warning other than the Lake notice about the mathlib URL |
| `python3 tools/sync_docs.py` | the generated paragraph of this file and the generated table of `CORRESPONDENCE.md` agree with the manifest |

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for further notes.

## Running the comparators

Each comparator pair has a configuration `UCPlanarAudit/<Pair>/comparator.json` that permits
exactly `propext`, `Classical.choice` and `Quot.sound` and enables the nanoda kernel. Build
`leanprover/comparator`, `lean4export`, `landrun` and `nanoda_lib` at the revisions pinned in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) (also recorded in
[`UCPlanarAudit/COMPARATOR_RUNS.md`](UCPlanarAudit/COMPARATOR_RUNS.md)), and from the repository
root run

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator UCPlanarAudit/<Pair>/comparator.json
```

A pair passes when the comparator prints `Your solution is okay!`.

## Repository layout

```text
UCPlanar.lean             the root module, importing the whole library
UCPlanar/
  Proved/                 the main theorems and the other results, with every quoted result proved
  MainTheorems.lean       the main theorems in the forms that take the quoted results as hypotheses
  Frozen/                 the pinned statements of the numbered results, one per file
  External/               the statements of the quoted results
  Support/                definitions and lemmas: periodic and plane graphs, the topological step,
                          polynomial approximation, the three-ball and exponential bounds, the
                          Liouville step, the counterexample, the discrete Remez inequality
  Vendored/               plane-topology modules copied from Lattice-Probability, some adapted from
                          Leonardo Bonanno's formalizations; each header names its source
  Meta/AxiomsAudit.lean   the axiom report, compiled by `lake build`, not imported by the root
  Basic.lean              bounded density, exceptional count, uniform ellipticity
UCPlanarAudit/            the mathlib-only restatements and their solutions
ASSUMPTIONS.md            the quoted results and their proofs (generated)
CORRESPONDENCE.md         paper to Lean, statement by statement
PROOF.md                  the mathematics of the proof and the Lean tree
CERTIFICATE.md            generated record of the toolchain, the build, and each statement's axioms
                          and hash
ledger/manifest.yaml      one entry per pinned statement: hash, place in the paper, proof
paper/                    ucplanar.tex, the corrected text; CHANGES_FROM_ARXIV.md; ucplanar-arxiv.tex,
                          the unmodified arXiv source, with arxiv/ holding its class files,
                          bibliography and figures
tools/                    the checkers listed under Building, and the generators of ASSUMPTIONS.md,
                          CERTIFICATE.md and the generated parts of this file and CORRESPONDENCE.md
formalization.yaml        models, tooling, cost, status and review (mathlib-initiative v0.4)
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and DeepSeek,
under the direction of Ahmed Bou-Rabee. Every proof is checked by the Lean kernel. The models,
tooling, cost and review status are recorded in [`formalization.yaml`](formalization.yaml),
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
