# Unique-Continuation-Planar

A machine-checked **Lean 4** formalization of the paper
[*Unique continuation on planar graphs*](https://doi.org/10.19086/da.144015)
(Ahmed Bou-Rabee, William Cooperman and Shirshendu Ganguly, Discrete Analysis
2025:16; arXiv:2309.13728), built on [`mathlib`](https://github.com/leanprover-community/mathlib4),
the shared library [`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability)
(`LatticeProb`), and the Schoenflies library
[`schoenflies-lean`](https://github.com/alonamaloh/schoenflies-lean).

Every theorem, lemma and proposition of the paper is formalized and proved, in
the form in which the paper states it.  Three results that the paper cites from
the literature enter as explicit hypotheses of the theorems that use them.

[![CI](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/Unique-Continuation-Planar/actions/workflows/comparator.yml)

## What is proved

A periodic planar graph `G = (V, E)` is drawn in the plane so that the drawing
is invariant under translation by a rank-two lattice `𝓛`, with finitely many
vertex orbits.  Each edge carries a positive conductance `a`, and the Laplacian
is `Δf(u) = Σ_{w∼u} a(u,w)(f(u) − f(w))`.  The classical Liouville theorem
says that, when `a` is `𝓛`-invariant, a bounded harmonic function on `G` is
constant.  Theorem 1.1 of the
paper asks for the bound only on most of the graph: if `a` is `𝓛`-invariant,
there is `ε = ε(a) > 0` such that every `f` with `Δf = 0` on `G` and

    lim_{n→∞} |{|f| ≤ 1} ∩ B_n| / |B_n|  ≥  1 − ε

is constant, where `B_n` is the graph-metric ball of radius `n` about a fixed
origin.  The proof sets an exponential upper bound (Theorem 1.2), which rests
on a topological property of the level sets of planar harmonic functions,
against an exponential lower bound (Theorem A.1 of the appendix).  Theorem 1.3
is the same argument for a function that vanishes on most of a ball, and
Theorem 5.1 shows that planarity is needed: it gives non-planar periodic
conductances on `ℤ²` with a harmonic function supported on a diagonal.

This repository formalizes **every theorem, lemma and proposition of the
paper**: Theorems 1.1, 1.2 and 1.3, the topological lemma (Lemma 2.1), the
non-planar counterexample (Theorem 5.1), and the exponential lower bound of the
appendix with its polynomial approximation lemma and three-ball proposition
(Theorem A.1, Lemma A.2, Proposition A.3).  Not formalized: the introduction's
survey of related work and applications, the remark following Theorem 1.3, and
the figures.

The four main theorems are stated in full in
[`UCPlanar/MainTheorems.lean`](UCPlanar/MainTheorems.lean), each proved by
`exact` of its certified counterpart in `UCPlanar/Frozen/`, so the statements
displayed there are the certified ones.

* **`UCPlanar.liouville`** (Theorem 1.1, `theorem:liouville`): for a periodic
  plane graph `P` and a conductance `c` invariant under the translation
  lattice, there is `ε > 0` such that every function harmonic on the whole
  graph whose density of `{|f| ≤ 1}` in the balls `B_n` about some vertex
  converges to a limit at least `1 - ε` is constant.  Hypotheses:
  `MoserEstimate`, `EdgeSplitting`, `Unicoherence`.
* **`UCPlanar.uniformlyBounded`** (Theorem 1.2, `theorem:uniformly-bounded`):
  there is `n₀`, and for each ellipticity ratio `Θ > 1` there are
  `ε₀, A > 0`, such that for conductances in `(λ, Θλ)`, `n ≥ n₀`, `ε < ε₀`
  and `f` harmonic on `B_{2n}` with `|f| > 1` on at most `ε |B_{2n}|`
  vertices, `|f| ≤ exp(A √ε n)` on `B_n`.  Hypotheses: `EdgeSplitting`,
  `Unicoherence`.
* **`UCPlanar.zeroCase`** (Theorem 1.3, `theorem:zero-case`): there are
  `ε₀ > 0` and `n₀` such that for arbitrary positive conductances, `n ≥ n₀`,
  `ε < ε₀` and `f` harmonic on `B_{2n}` and nonzero on at most `ε |B_{2n}|`
  vertices, `f` vanishes on `B_n`.  Hypotheses: `EdgeSplitting`,
  `Unicoherence`.
* **`UCPlanar.counterexample`** (Theorem 5.1, `theorem:counterexample`): for
  positive `A₁ ≠ A₂` and `A₃ > 2 A₁² A₂² / ((A₁ - A₂)² (A₁ + A₂))` there is
  `A₄ > 0` such that `ℤ²` with the crossing conductances
  `𝓔(A₁, A₂, A₃, A₄)` carries a harmonic function `h` with `h(0) = 1` that
  is nonzero exactly on the diagonal `{x₁ = x₂}`.  No hypotheses.

**Conditional results.**  Three results that the paper cites from the
literature are stated in Lean as propositions in `UCPlanar/External/`, and every
theorem whose proof uses one takes it as an explicit hypothesis, so the
statement shows exactly which of them it rests on;
[`ASSUMPTIONS.md`](ASSUMPTIONS.md) lists the three with their verbatim Lean
statements.  They are Janiszewski's theorem at a point for the drawings of two
finite edge sets (`EdgeSplitting`), unicoherence of the sphere in the form that
the frontier of a bounded face of a connected plane graph is connected
(`Unicoherence`), and the discrete Moser estimate (`MoserEstimate`).  They are
**not proved here**.  Theorem 1.1 is conditional on all three, Theorems 1.2
and 1.3 on the two plane inputs, and Theorem 5.1 on none.  Two further results
the paper cites, the classical Liouville theorem for the periodic network and
the discrete Remez inequality, are proved here.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **11 registered nodes: 3 `FROZEN`, 8 `SEALED`.** 8 theorem(s) are proved and machine-checked: no `sorry`, no axiom added by this development, and an axiom closure of exactly Lean's three standard axioms `propext`, `Classical.choice` and `Quot.sound`. 3 result(s) are cited from the literature and stated as explicit hypotheses rather than proved here, so the theorems that use them are proved conditional on them.

Counts are generated from `ledger/manifest.yaml` by
`python3 tools/sync_docs.py`. Run `python3 tools/check_axioms.py`
to check registered axiom closures.

<!-- STATUS-END -->

**Scope and faithfulness.**  Every statement of the paper is registered: one
Lean declaration per theorem, lemma or proposition, and one proposition per
cited result that is assumed.  A registered statement's text between the lines
`-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` is pinned by the
SHA-256 of those bytes in [`ledger/manifest.yaml`](ledger/manifest.yaml),
together with the line range in `paper/ucplanar.tex` and, for the paper's
numbered statements, the `\label` it transcribes; the proof after the end marker
may be rewritten freely.  In the manifest, a registered statement is `SEALED`
when it is proved with an axiom closure of exactly the three standard axioms,
and `FROZEN` when it is a cited result assumed rather than proved.  Every
registered statement is pinned by hash; only the `FROZEN` ones are assumed.

The paper-to-Lean map, node by node, is [`CORRESPONDENCE.md`](CORRESPONDENCE.md),
and [`PROOF.md`](PROOF.md) describes the mathematics of the proof and the Lean
tree.  The paper text in `paper/ucplanar.tex` is arXiv:2309.13728v2 with
corrections, and the Lean statements transcribe the corrected text; every
difference from the arXiv version is listed in
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md).  In summary:

- The model is a periodic plane graph `P : PeriodicPlaneGraph V`
  (`UCPlanar/Support/Periodic.lean`): a connected, locally finite graph with a
  proper coordinate realization, a rank-two translation action and finitely
  many vertex orbits, drawn in the plane with noncrossing polygonal edge arcs,
  translation invariant, with uniform bounds on the size and the diameter of a
  face.  Faces are the connected components of the complement of the drawing.
- Conductances, the Laplacian and harmonicity are those of `Lattice-Probability`
  (`LatticeProb.Network.IsCond`, `netLaplacian`, `HarmonicOn`).  The paper's
  Laplacian is the negative of `netLaplacian`; their zero equations agree.
- The reduction in Step 1 of the zero case, which deletes and contracts finite
  edge-connected components, is not formalized.  The statement is proved
  directly for the periodic plane graph, with the surrounding cycles supplied
  by the cited plane inputs.
- The Lean statement of Theorem 1.1 makes the limit explicit: the density of
  `{|f| ≤ 1}` in `B_n` converges to a real number `d` with `1 − ε ≤ d`.

In each frozen statement whose conclusion has a real existential constant, the
quantifier order is checked mechanically (`tools/check_constants.py`): no
radius, function, density or conductance parameter is bound before it.

## Guarantees

- **No `sorry`** in the library.  The four comparator challenges under `Audit/`
  each contain one intentional statement-level `sorry`, which the corresponding
  solution file proves.
- **No custom axiom.**  The four main theorems depend only on mathlib's
  standard axioms `propext`, `Classical.choice` and `Quot.sound`.
  [`UCPlanar/Meta/AxiomsAudit.lean`](UCPlanar/Meta/AxiomsAudit.lean) prints
  their axiom dependencies, and `python3 tools/check_axioms.py` checks the
  axiom closure of every registered statement.  The cited results above are
  hypotheses, not axioms.
- **Independent check of the statements.**  So that the main claims can be read
  without trusting the 26,000-line development, each main theorem is restated
  using only Mathlib, with no project or library definitions, in
  [`Audit/Liouville/Challenge.lean`](Audit/Liouville/Challenge.lean),
  [`Audit/UniformlyBounded/Challenge.lean`](Audit/UniformlyBounded/Challenge.lean),
  [`Audit/ZeroCase/Challenge.lean`](Audit/ZeroCase/Challenge.lean) and
  [`Audit/Counterexample/Challenge.lean`](Audit/Counterexample/Challenge.lean).
  Each challenge rebuilds the model from Mathlib primitives (lattice sites,
  graph balls, conductances, the network Laplacian and harmonic functions as in
  `Lattice-Probability`; polygonal sets as in the Schoenflies library; plane
  embeddings, faces, periodic plane graphs and their density notions; the
  crossing conductances of Theorem 5.1; and the cited results it assumes), and
  the corresponding `Solution.lean` proves the byte-identical statement from the
  library through the bridges in `Audit/Support/`.  The configurations in
  `Audit/*/comparator.json` are for
  [`leanprover/comparator`](https://github.com/leanprover/comparator), which
  confirms that the two statements have identical elaborated types and that the
  proof reduces to the three standard axioms; the workflow
  [`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) runs it
  on request.  `Audit/StatementRegression.lean` checks locally that each
  solution statement is exactly the challenge statement and mentions no
  constant of `UCPlanar`, `LatticeProb` or `Schoenflies`.  Every pair passed the
  comparator with the Lean kernel and again with the independent nanoda kernel.
  See [`Audit/README.md`](Audit/README.md) and
  [`Audit/COMPARATOR_RUNS.md`](Audit/COMPARATOR_RUNS.md).
- **Pinned toolchain.**  Lean `v4.32.0`, `mathlib` at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997`, `Lattice-Probability` at commit
  `9d44b4d` and `schoenflies-lean` at commit `05a43d29`, recorded in
  [`lean-toolchain`](lean-toolchain), [`lakefile.lean`](lakefile.lean) and
  [`lake-manifest.json`](lake-manifest.json).

## Size

About 26,000 lines of Lean in 171 modules, of which about 21,000 lines are code
once comments and blank lines are removed, on top of mathlib, the
Lattice-Probability library and the Schoenflies library.

## Building

The project uses [`elan`](https://github.com/leanprover/elan) (the Lean
toolchain manager) and Lake.  The toolchain is pinned in
[`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.32.0`), so `elan`
installs the right Lean version automatically, and the dependencies are pinned
to commits in `lakefile.lean` and [`lake-manifest.json`](lake-manifest.json).

```bash
lake exe cache get   # prebuilt Mathlib
lake build           # compile the project
```

```bash
lake build UCPlanar.Meta.AxiomsAudit   # print the axioms of the four main theorems
lake build Audit                       # the comparator challenges and solutions
lake build Audit.StatementRegression
```

To use the library, `import UCPlanar` pulls in the whole development; the main
results are in `import UCPlanar.MainTheorems`.

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`).

| command | what it guarantees |
|---|---|
| `python3 tools/check_manifest.py` | every frozen statement's bytes match its recorded SHA-256 and declaration name, every file under `UCPlanar/Frozen/` belongs to exactly one node, no `axiom`, `admit` or `sorryAx` token occurs in the source tree, and `sorry` occurs only in nodes in state `DRAFT_SORRY` (none is); needs neither Lake nor network |
| `python3 tools/check_axioms.py` | runs `#print axioms` on every registered export; each closure contains only `propext`, `Classical.choice` and `Quot.sound` |
| `python3 tools/check_constants.py` | in each frozen statement whose conclusion has a real existential constant, no radius, function, density or conductance parameter is bound before it |
| `python3 tools/check_warnings.py` | runs `lake build UCPlanar` and fails if the build fails or emits any warning other than the Lake notice about the Mathlib URL and the `sorry` warnings expected for `DRAFT_SORRY` nodes (none is registered) |

Also in `tools/`: `paper_anchors.py` checks that the line ranges in the
manifest match the paper's `\label`s (`--fix` repairs them); `sync_docs.py`
checks (`--write` regenerates) the status block of this file and the
registered-statements table of `CORRESPONDENCE.md`; `assumptions.py`
regenerates `ASSUMPTIONS.md` (`--check` verifies it is current);
`certificate.py` regenerates `CERTIFICATE.md` (`--check` compares it with the
file on disk); `freeze.py` registers or refreshes a node in the manifest.

## Repository layout

```
UCPlanar/
  MainTheorems.lean   the main theorems, stated in full
  Frozen/             the certified statement surface, one frozen statement per file
  External/           the three cited results, each a frozen Prop
  Support/            the definitions and lemmas the frozen statements are proved from:
                      periodic and plane graphs, the topological step, polynomial
                      approximation (Poly/), the three-ball and exponential bounds,
                      the Liouville step, the counterexample, the discrete Remez inequality
  Meta/               AxiomsAudit.lean
  Basic.lean          bounded density, exceptional count, uniform ellipticity
UCPlanar.lean         the root module (imports the whole library)
Audit/                Mathlib-only comparator challenges and solutions
ASSUMPTIONS.md        the cited results assumed, with their Lean statements (generated)
CORRESPONDENCE.md     paper ↔ Lean, node by node
PROOF.md              the mathematics of the proof and the Lean tree
CERTIFICATE.md        generated record of the toolchain, the build, each node's axiom
                      closure and the SHA-256 of each frozen statement
CONTRIBUTING.md       building notes and the elaboration policy for new files
CITATION.cff          citation metadata
formalization.yaml    models, tooling, cost, status and review (mathlib-initiative v0.4)
ledger/manifest.yaml  one row per registered statement: hash, paper source, state
paper/ucplanar.tex    the paper, pinned by the SHA-256 in ledger/manifest.yaml
paper/CHANGES_FROM_ARXIV.md  every difference between the pinned paper and arXiv:2309.13728v2
paper/ucplanar-arxiv.tex     the unmodified arXiv source; paper/arxiv/ holds its class files,
                      bibliography and figures
tools/                the checkers and generators listed under Building
.github/workflows/    the CI build and the comparator audit
lakefile.lean, lake-manifest.json, lean-toolchain   the pinned build
```

## How this was built

The Lean code was written mostly by Claude (Fable 5.1, Opus 5, Opus 5.5 and
Sonnet 5), with contributions by OpenAI's gpt-6-astra, gpt-6-luna and
gpt-5.6-luna; DeepSeek-v4.1-flash; Kimi k3; and GLM-5.3 and GLM-5.3-flash,
under the close supervision of the author; models, tooling, cost and review
status are disclosed in [`formalization.yaml`](formalization.yaml), following
the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors, citation, acknowledgements

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
audit in [`Audit/`](Audit/) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).  The paper source in `paper/` is included for
reference and is not covered by the Apache license.
