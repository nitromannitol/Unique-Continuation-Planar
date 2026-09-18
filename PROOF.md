# The proof and the Lean tree

This file describes the mathematics of *Unique continuation on planar graphs*
(Bou-Rabee, Cooperman, Ganguly, Discrete Analysis 2025:16) and the Lean 4
development that formalizes it. Part A states the chain of results as the paper
proves them. Part B maps each registered statement to the Lean declarations and
support modules that prove it. Part C lists the cited inputs, which enter as
explicit hypotheses and are not proved here. A section between Parts A and B
records the points where the formalized statements and proofs differ from the
published text, with the mathematical reason for each difference.

The pinned source is `paper/ucplanar.tex`. Every registered statement is a
declaration in its own file under `UCPlanar/Frozen/` or `UCPlanar/External/`,
with a paper line anchor recorded in `ledger/manifest.yaml`. The library
`UCPlanar` is built on Mathlib and on the shared library `LatticeProb`, which
supplies graph balls, conductances, harmonicity and the lattice `Site 2`.

## Part A. The mathematics

### The main theorem

A periodic planar graph is a connected, locally finite graph drawn in the plane
so that the drawing is invariant under a rank-two lattice of translations, with
finitely many vertex orbits. The paper's main result, `theorem:liouville`
(`ucplanar.tex:161-167`), is a quantitative Liouville theorem. Let the
conductances be positive and invariant under the translations. Then there is a
constant `ε > 0`, depending on the conductances, such that a function harmonic
on the whole graph whose bounded-value density

    |{x in B_n : |f(x)| <= 1}| / |B_n|

has a limit, as `n` tends to infinity, at least `1 - ε` is constant. The Lean
statement makes the limit explicit: the density of `{|f| <= 1}` in the graph
metric ball `B_n` converges to a real number `d` with `1 - ε <= d`. The
classical Liouville theorem is the statement that a harmonic function bounded
everywhere is constant, and the content of the theorem is that the bound is
needed only on a set of density close to one. The proof is by contradiction: a
nonconstant harmonic function is unbounded, and the two exponential bounds below
force it to be both at most and at least an exponential at the same scale.

### The topological lemma

The engine of the argument is `lemma:topological-lemma`
(`ucplanar.tex:222-231`). Let `γ` be a cycle of the graph and let `Z`, `P`, `M`
be disjoint vertex sets with `Z` on `γ`, with `P` and `M` inside the cycle
region, with a face path from each `z in Z` to a vertex adjacent to both a
positive and a negative vertex, and with every connected component of `P` and of
`M` meeting `γ \ Z`. Then `|Z| <= α |γ|` for a constant `α < 1`. The paper
states that `α` depends only on the maximum face size; the Lean statement
quantifies a degree bound `d` and a face-size bound `L` and returns `α`
depending on both, which is the form the counting argument uses. The key idea is
that the positive and negative sets interleave around the cycle. The proof
selects a maximal subset `Z'` of `Z` on which the two sign vertices and the face
paths are pairwise distinct, which loses only a factor of the fourth power of the
face size, and then walks around the cycle adding to a set `S` of vertices of
`γ \ Z` either the positive predecessor of the current point or, when that
predecessor repeats, the negative predecessor of the previous point. A repeat in
the second case would produce two disjoint paths whose endpoints alternate
around `γ`, which the Jordan curve theorem forbids, so each step of case (1) or
(3) adds a new vertex, and since case (2) occurs no more often than case (1),
`S` has at least half the cardinality of `Z'`. The Lean proof reduces
the interleaving to an explicit crosscut hypothesis and discharges it from the
cycle geometry.

### The zero case

`theorem:zero-case` (`ucplanar.tex:187-190`) is the unique continuation
statement for a function that vanishes on a set of density close to one. There
are constants `ε₀` and `n₀`, depending only on the periodic plane graph, such
that if `f` is harmonic on `B_{2n}` for `n >= n₀` and the set where `f` is
nonzero occupies at most an `ε`-fraction of `B_{2n}` for `ε < ε₀`, then `f`
vanishes on `B_n`. The proof has three steps. Step 1 reduces to the case where
the dual is a graph, by deleting finite two-edge-connected components and
contracting finite three-edge-connected components to a single edge of the
effective conductance. Step 2 uses the pigeonhole principle over the radii
`m in [1.5n, 2n]` to find a sphere `∂B_m` such that at most `C ε n` vertices
where `f` is nonzero are adjacent to a face of `∂B_m`. Step 3 argues by
contradiction: a nonzero vertex of `B_n`
generates, through the maximum principle, a connected cluster of faces meeting
the chosen sphere, and the boundary cycle of the filled cluster carries a set
`Z` of zeros to which the topological lemma applies. The lemma forces linearly
many vertices of the cycle to be adjacent to the sphere, contradicting Step 2
for `ε₀` small. The Lean proof does not formalize Step 1 and proves the
statement for the periodic plane graph directly; it keeps the two classical
plane inputs of Step 3 as hypotheses and assembles the remaining steps in
`ZeroAssemble`.

### The uniformly bounded case

`theorem:uniformly-bounded` (`ucplanar.tex:175-181`) is the same statement for
a function that is merely small on a set of density close to one, under the
additional hypothesis that the conductances are uniformly elliptic between
`λ` and `Λ`. There are constants `ε₀`, `n₀` and `A`, with `ε₀` and `A`
depending on the ellipticity ratio `Θ = Λ/λ`, such that if `f` is harmonic on
`B_{2n}` for `n >= n₀` and the set where `|f| > 1` occupies at most an
`ε`-fraction of `B_{2n}` for `ε < ε₀`, then `max_{B_n} |f| <= exp(A sqrt(ε) n)`.
The Lean
statement binds `n₀` first, so that the minimum radius depends only on the
geometry, and then `Θ`, `ε₀` and `A`; it gives the bound pointwise at every
vertex of `B_n`, which is the equivalent form the covering argument produces. The proof opens with an
observation that uses ellipticity: a vertex where `f` is small with a large
neighbour has a neighbour of the opposite sign and large magnitude. Step 1
repeats the proof of the zero case with the level set `{|f| <= A}` in place of
the zero set, over geometric bands of values, and obtains a coarse exponential
bound with a constant exponent. Step 2 covers `B_n` by `δ²` balls of radius
`δn` and applies Step 1 on each, which turns the constant exponent into the
exponent `A sqrt(ε)`. The Lean proof splits the two steps into `BandCoarse` and
`BandsCover`, with the band pigeonhole in `Bands` and the sign observation in
`BandSign`.

### The polynomial approximation

`lemma:poly-approx` (`ucplanar.tex:438-445`) approximates a harmonic function by
a polynomial on a lattice orbit. For every `α > 0` there is `c(α) > 0` such that
for every sufficiently large `R`, every `m <= c R` and every vertex `v`, a
function harmonic on the square `Q_{3R}` admits a polynomial `p` of degree at
most `m` with

    |f(x) - p(x)| <= α^m sup_{Q_{3R}} |f|

at every orbit point `x` of `v` in `Q_{cR}`. The Lean statement records the
degree bound as `p.totalDegree <= m` for a polynomial in two variables
evaluated at the drawing of `x`, and the error as `α^m` times the supremum norm
of `f` over `Q_{3R}`. The proof iterates the discrete
Caccioppoli inequality and applies a discrete Moser estimate to bound the
`m`-th forward difference, then takes the Newton interpolation of the orbit data
at a corner of the square and controls the Taylor remainder by the derivative
bound. The paper remarks that this is the only place in its argument where
translation invariance of the conductances is used; the Lean development also
uses it in `LiouElliptic`, which derives uniform ellipticity from periodicity.
The Lean proof is the `Poly` family of modules: `Basic` for the
vocabulary, `Caccioppoli` and `CaccioppoliLattice` for the energy inequality,
`Elliptic` and `DerivBound` for the Moser estimate, `Newton`, `Interpolation`
and `Orbit` for the interpolating polynomial, `Difference`, `Word`, `Factorial`,
`Square`, `Iterate` and `Volume` for the remainder, and `Bridge`, `Rebase`,
`Change`, `LatVar` and `Assembly` for the change of variables to the drawing.

### The three-ball inequality

`prop:three-ball` (`ucplanar.tex:468-480`) is the discrete three-ball
inequality. There is `ε > 0` such that if `f` is harmonic, bounded by `M` on
`Q_{kN}` for an outer radius `k >= 4` chosen after the conductance, and satisfies
`|f| <= 1` on at least a `(1 - ε)`-fraction of `Q_N`, then

    max_{Q_{2N}} |f| <= C M^{1/2} + C exp(-cN) M

with positive constants `c` and `C`. The proof follows the cited three-ball
argument on `Z²`, replacing the exact Poisson kernel by the polynomial
approximation lemma. It suffices to propagate the bound along one lattice line
and then along the other. On a line where `f` is small at half the integer
points, the approximating polynomial is a univariate polynomial bounded on half
of an interval, and the discrete Remez inequality carries the bound out to twice
the interval. The paper splits the propagation into two cases according to
whether `M exp(βN)` is at most `1`, choosing the degree of the approximating
polynomial as `γN` in the first case and `N/2` in the second, and fixes
`β = -log 32` and `α = 2^{-12}` at the end. Iterating the propagation and
covering the square gives the statement. The Lean statement gives the bound
pointwise at every vertex of `Q_{2N}` rather than as a maximum, which is the
equivalent form the propagation produces. The Lean proof is the `Three` family:
`ThreeBall` for the lattice
ingredients, `ThreeBridge` for the passage from the approximating polynomial to
the univariate polynomial, `ThreeLine` and `ThreeProp` for the two cases of the
one-dimensional propagation, `ThreeReach` for the doubling of the interval,
`ThreeCover` for the transfer of the density hypothesis to one coset of the
period lattice, and `ThreeAssembly` for the arithmetic and the composition along
the two families of lines.

### The exponential lower bound

`theorem:lower-bound` (`ucplanar.tex:422-433`) is the competing statement: a
nonconstant harmonic function that is bounded on most of the graph grows at
least exponentially. There is `b > 0` such that for small `ε` and large `N`, if
`f` is harmonic on the whole graph, attains a value at least `2` on the square
of radius `sqrt(N)`, and satisfies `|f| <= 1` on at least a `(1 - ε)`-fraction
of `Q_K` for every integer `K` between `sqrt(N)` and `2N`, then
`max_{Q_N} |f| >= exp(bN)`. The proof runs the three-ball inequality along a
dyadic ladder of scales, each rung turning a bound at one scale into a bound at
twice the scale, and closes with the discrete gradient estimate along one
lattice generator. The Lean proof is the `Lower` family: `LowerArith` for the
arithmetic of the dichotomy, `LowerBound` for the exponential bound on a square,
`LowerChain` and `LowerLadder` for one rung and the
ladder, `LowerShift` for the three-ball inequality at a translated square,
`LowerVolume` for the local density count, `LowerBoot` and `LowerBootstrap` for
the bootstrap, and `LowerAssembly` for the assembly. The paper states the
theorem on the unit square lattice and proves the periodic form in the
appendix, by the same argument with the three-ball proposition in place of the
discrete three-circle theorem. The Lean development proves the periodic form
directly along that route.

### The Liouville step

The main theorem is the comparison of the two exponential bounds. A nonconstant
harmonic function with bounded-value density close to one is unbounded by the
classical Liouville theorem, so it is at least `2` at some vertex after a change
of sign; the exponential lower bound then gives `exp(bN) <= max_{Q_N} |f|`,
while the uniformly bounded case, applied with the ellipticity ratio that
periodicity supplies, gives `max_{Q_N} |f| <= exp(A sqrt(ε) N)`. For `ε` small
the rate `A sqrt(ε)` is below `b`, so the upper bound is below the lower bound
at large scales, a contradiction. The Lean
proof is the `Liou` family: `LiouEllipticValue`, `LiouElliptic` and `LiouRatio`
for the ellipticity ratio of a periodic conductance, `LiouDensity`,
`LiouEventually`, `LiouCount` and `LiouDensityTransfer` for the passage from
the density limit to the exceptional count, `LiouTransfer`, `LiouBallSquare`,
`LiouFinalGeom` and `LiouSquareDensity` for the comparison of geometric squares
with graph metric balls, `LiouSupNorm` and `LiouSupBound` for the supremum norm,
`LiouUnbounded` for the contrapositive of the classical Liouville theorem,
`LiouCHeat`, `LiouKilled` and `LiouPeriodic` for the classical Liouville
theorem itself — a periodic network is recurrent by the Nash-Williams criterion,
and a bounded harmonic function on a recurrent network is constant —
`LiouExpCompare` for the exponential comparison, `LiouFinalContra` for the
contradiction, and `LiouAssembly`, `LiouBridge` and `LiouMain` for the assembly.
`LiouAssembly` defines the two predicates `UniformUpperBound` and
`PeriodicLowerBound` that the frozen statements instantiate, and `LiouBridge`
converts the frozen statements into them.

### The counterexample

`theorem:counterexample` (`ucplanar.tex:380-385`) shows that planarity is
essential. On the square lattice with crossing edges, for each choice of
positive `A₁ ≠ A₂` and `A₃ > 2A₁²A₂² / ((A₁-A₂)²(A₁+A₂))` there is `A₄ > 0` and
a harmonic function on the resulting periodic network supported on the diagonal
`{x₁ = x₂}`. The Lean statement is the sharper form the paper's proof gives:
the function is normalized by `h(0,0) = 1` and is nonzero exactly at the
diagonal sites, `f x ≠ 0 ↔ x 0 = x 1`. The function is
`h(x₁,x₂) = 1_{x₁=x₂} z_{x₁}` where `z₀ = 1` and
`A₁ z_i + A₂ z_{i-1} = 0`, and the condition on `A₃` is what makes the diagonal
equation solvable for a positive `A₄`. The Lean proof is the `Crossing` family,
which builds the graph, its conductances and its local finiteness, together with
`CounterexampleAlgebra` for the parity and the algebra of the diagonal
function.

## Part B. The Lean tree

### Registered nodes

The manifest registers eleven declarations: eight paper statements and three
cited inputs. The eight statements are `SEALED`; the three inputs are `FROZEN`
proposition-valued definitions.

| id | Lean name | file | state | paper |
|---|---|---|---|---|
| `N-001` | `UCPlanar.Frozen.liouville` | `UCPlanar/Frozen/Liouville.lean` | SEALED | `ucplanar.tex:161-167`, `theorem:liouville` |
| `N-002` | `UCPlanar.Frozen.uniformlyBounded` | `UCPlanar/Frozen/UniformlyBounded.lean` | SEALED | `ucplanar.tex:175-181`, `theorem:uniformly-bounded` |
| `N-003` | `UCPlanar.Frozen.zeroCase` | `UCPlanar/Frozen/ZeroCase.lean` | SEALED | `ucplanar.tex:187-190`, `theorem:zero-case` |
| `N-004` | `UCPlanar.Frozen.topological` | `UCPlanar/Frozen/Topological.lean` | SEALED | `ucplanar.tex:222-231`, `lemma:topological-lemma` |
| `N-005` | `UCPlanar.Frozen.counterexample` | `UCPlanar/Frozen/Counterexample.lean` | SEALED | `ucplanar.tex:380-385`, `theorem:counterexample` |
| `N-006` | `UCPlanar.Frozen.threeBall` | `UCPlanar/Frozen/ThreeBall.lean` | SEALED | `ucplanar.tex:468-480`, `prop:three-ball` |
| `N-007` | `UCPlanar.Frozen.polynomialApproximation` | `UCPlanar/Frozen/PolynomialApproximation.lean` | SEALED | `ucplanar.tex:438-445`, `lemma:poly-approx` |
| `N-008` | `UCPlanar.Frozen.periodicLowerBound` | `UCPlanar/Frozen/PeriodicLowerBound.lean` | SEALED | `ucplanar.tex:422-433`, `theorem:lower-bound` |
| `X-002` | `UCPlanar.External.EdgeSplitting` | `UCPlanar/External/EdgeSplitting.lean` | FROZEN | `ucplanar.tex:296-322`, Step 3 |
| `X-003` | `UCPlanar.External.Unicoherence` | `UCPlanar/External/Unicoherence.lean` | FROZEN | `ucplanar.tex:296-322`, Step 3 |
| `X-007` | `UCPlanar.External.MoserEstimate` | `UCPlanar/External/MoserEstimate.lean` | FROZEN | `ucplanar.tex:452-457` |

### Shared infrastructure

The vocabulary of the whole development is in `UCPlanar/Basic.lean` and the
modules `Periodic`, `Planar`, `Harmonic`, `Density`, `FiniteDomains` and
`Growth`. `Periodic` defines `UCPlanar.PeriodicGraph`, a connected locally
finite graph with a proper rank-two coordinate realization, a translation
action, finitely many vertex orbits, and finite balls; `PeriodicPlaneGraph`
adds a noncrossing drawing, its translation invariance, properness of the drawn
edges, a bound on face sizes and a bound on face diameters. `Planar` defines
`UCPlanar.PlaneEmbedding` with its faces, incidence, cofaciality and face bound.
`Harmonic` and `Density` supply the Laplacian sign and the exceptional-count and
density vocabulary, and the maximum principle is in `ZeroMax`, `ZeroSign` and
`TopoClusterReach`. `Growth` defines the bounded-value
density limit `UCPlanar.PeriodicGraph.HasBoundedDensity` and the eventual
exponential bound. `FiniteDomains` identifies the finite domains with their
defining geometric and graph sets.

The drawing is developed further in the `Planar` family: `PlanarCycle` for cycle
interiors and face paths, `PlanarTrace`, `PlanarFaces`, `PlanarMetric`,
`PlanarLattice`, `PlanarLabels`, `PlanarComponents`, `PlanarInterior`,
`PlanarBoundary`, `PlanarAttachments`, `PlanarDomain`, `PlanarOrder`,
`PlanarReduction` and `PlanarPacking`. These modules are shared by the
topological step and the zero case; `PlanarPacking` holds the finite separated
subsets and the bounded-neighbourhood counting that the density arguments use.
`PlanarTopological` combines them into
`UCPlanar.Support.topological_of_crosscuts`, which is the density bound of the
topological lemma with alternating-crosscut intersection as an explicit
hypothesis.

The filled cluster of Step 3 is the `Topo` family. `TopoWalk`, `TopoBridge`,
`TopoCrosscut`, `TopoTransport`, `TopoModel`, `TopoGenCrosscut`, `TopoChord`,
`TopoCycleArcs`, `TopoCross` and `TopoInterleave` build the crosscut and
interleaving machinery; `TopoCluster`, `TopoFaceCluster`, `TopoClusterBoundary`,
`TopoClusterEdges`, `TopoClusterInside`, `TopoClusterReach`, `TopoClusterBounded`
and `TopoClusterFace` build the cluster of faces and its boundary cycle;
`TopoStep3`, `TopoStep3Band`, `TopoStep3Closed` and `TopoStep3Component` state
the cycle produced by Step 3; `TopoWalksExternal` and `TopoArcLocal` discharge
the local finiteness of the faces and the local structure of the drawing. The
polygonal layer beneath them is `TopoBlock`, `TopoPolygonal`, `TopoPolyWalk`,
`TopoPolyConn`, `TopoPolyCycle`, `TopoJordan`, `TopoLines`, `TopoRegion`,
`TopoSeparate`, `TopoPuncture`, `TopoComponentArcs`, `TopoCorner`, `TopoLocal`,
`TopoProper`, `TopoMinimal`, `TopoEdgeSet`, `TopoEdgeWalk` and `TopoBounded`,
which turn the imported Jordan and crosscut theorems into statements about the
drawn edges of the graph; `TopoFace`, `TopoFaceLocal`, `TopoFaceWalks`,
`TopoFacePath` and `TopoFaceBand` develop the frontier of a face and the face
path of Step 3. The Jordan curve and crosscut theorems themselves are imported
from the pinned Schoenflies library.

### The topological step

`N-004` is proved by `UCPlanar.Support.topological_of_crosscuts` in
`PlanarTopological`, with the interleaving supplied by
`UCPlanar.Support.exists_common_vertex_of_interleaved` in `TopoInterleave`. The
frozen proof is a direct application of the two.

### The zero case

`N-003` is proved by `UCPlanar.Support.zeroCase_of_surrounding` in
`ZeroAssemble`, which consumes the surrounding cycles supplied by
`UCPlanar.Support.exists_hasSurroundingCycles` in `SurroundExists`. The
surrounding-cycle property is `UCPlanar.PeriodicPlaneGraph.HasSurroundingCycles`,
defined in `ZeroAssemble`; `SurroundExists` derives it from the two cited plane
inputs. The three steps are the modules `ZeroVolume`, `ZeroLower` and `ZeroGeom`
for the periodic geometry and the quadratic growth of balls, `ZeroCount` for the
pigeonhole with bounded multiplicity, `ZeroShell` for the sparse boundary
radius of Step 2, `ZeroSign` and `ZeroMax` for the maximum principle and the
sign components, and `ZeroCycle` for the boundary cycle of Step 3 and the linear
lower bound it forces. `ZeroAssemble` contains the core
`UCPlanar.Support.zeroCase_core` and the assembly.
### The uniformly bounded case

`N-002` is proved by `UCPlanar.Support.uniformlyBounded_of_surrounding` in
`BandCoarse`, from the same surrounding cycles. The two steps of Section 4 are
`BandSign` for the sign observation that opens the section, `Bands` for the
pigeonhole over geometric bands, `BandCoarse` for the coarse exponential bound
of Step 1, and `BandsCover` for the rescaling of Step 2. These modules reuse the
`Zero` family and the `Topo` family for the boundary cycle.

### The polynomial approximation

`N-007` is proved by `UCPlanar.Support.polynomialApproximation_aux` in
`Poly/Assembly`, with the statement predicate
`UCPlanar.PeriodicGraph.PolynomialApproximation` and the orbit predicate
`UCPlanar.PeriodicGraph.OnOrbit` defined in `Approximation`. The `Poly` family
is `Basic`, `Caccioppoli`, `CaccioppoliLattice`, `Elliptic`, `Iterate`,
`Factorial`, `Square`, `Difference`, `Newton`, `Interpolation`, `Orbit`, `Word`,
`Volume`, `DerivBound`, `Bridge`, `Rebase`, `Change`, `LatVar` and `Assembly`.

### The three-ball inequality

`N-006` is proved by `UCPlanar.Support.Three.threeBall_assembled` in
`ThreeAssembly`, with the main intermediate `threeBall_main` and the orbit form
`threeBall_orbit` in the same module. The `Three` family is `ThreeBall`,
`ThreeBridge`, `ThreeLine`, `ThreeProp`, `ThreeReach`, `ThreeCover` and
`ThreeAssembly`.

### The exponential lower bound

`N-008` is proved by `UCPlanar.Support.Lower.periodicLowerBound_main` in
`LowerAssembly`. The `Lower` family is `LowerArith`, `LowerBound`, `LowerShift`,
`LowerVolume`, `LowerChain`, `LowerLadder`, `LowerBoot`, `LowerBootstrap` and
`LowerAssembly`.

### The Liouville step

`N-001` is proved by `UCPlanar.Support.liouville_of_bounds` in `LiouMain`, which
calls `UCPlanar.Support.LiouFinal.liouville_final_of_density` in
`LiouFinalContra` with the two assembly predicates
`UCPlanar.Support.UniformUpperBound` and
`UCPlanar.Support.PeriodicLowerBound` defined in `LiouAssembly`, which the
frozen statements instantiate through
`UCPlanar.Support.uniformUpperBound_of_frozen` and
`UCPlanar.Support.periodicLowerBound_of_frozen` in `LiouBridge`. The `Liou`
family is `LiouEllipticValue`, `LiouElliptic`, `LiouRatio`, `LiouDensity`,
`LiouEventually`, `LiouCount`, `LiouDensityTransfer`, `LiouTransfer`,
`LiouBallSquare`, `LiouFinalGeom`, `LiouSquareDensity`, `LiouSupNorm`,
`LiouSupBound`, `LiouUnbounded`, `LiouExpCompare`, `LiouFinalContra`,
`LiouAssembly`, `LiouBridge` and `LiouMain`.

### The counterexample

`N-005` is proved in `UCPlanar/Frozen/Counterexample.lean` from the `Crossing`
family: `CrossingGraph` for the graph and its conductances, `CrossingWeights`,
`CrossingConductance`, `CrossingNeighbors`, `CrossingSum`, `CrossingLaplacian`,
`CrossingHarmonic`, `CrossingFinite` for local finiteness, `CrossingThreshold`
for the threshold on `A₃`, and `CrossingCoefficients` for the eight
conductances at a vertex, and
`CounterexampleAlgebra` for the parity and the algebra of the diagonal
function. The frozen proof names `UCPlanar.Support.fourth_positive`,
`UCPlanar.Support.third_positive`, `UCPlanar.Support.crossing_isCond`,
`UCPlanar.diagonalFunction`, `UCPlanar.Support.diagonal_laplacian`,
`UCPlanar.Support.diagonal_balance` and `UCPlanar.Support.ratio_nonzero`.

### Where the Lean route differs

The paper's Step 1 of the zero case reduces to the case where the graph is
two-edge connected and the dual has no multiple edges, by deleting finite
two-edge-connected components and contracting finite three-edge-connected
components to a single edge of the effective conductance. The Lean development
does not formalize that reduction and instead proves the statement for the
periodic plane graph directly, with the surrounding cycles supplied by the cited
plane inputs. The paper states the exponential lower bound on the unit square lattice and
proves the periodic form in the appendix; the Lean development proves the
periodic form directly along the appendix route.
The paper's three-ball proposition
fixes the outer radius at `4N`; the Lean statement allows any outer radius `k`
with `k >= 4` chosen after the conductance, which is the form the covering
argument uses.

## Part C. The cited inputs

Each cited input is a proposition-valued definition under `UCPlanar/External/`,
stated in the paper's vocabulary and carried as an explicit hypothesis of the
frozen statements that use it. None is an axiom, and none is proved here.

`X-002`, `UCPlanar.External.EdgeSplitting`, transcribes Janiszewski's theorem at
a point for the drawings of two finite edge sets of a plane graph: if the two
drawings meet in at most one drawn vertex, a point in a bounded complementary
component of the union of the two drawings lies in a bounded complementary
component of one of them. It is consumed by `N-003`, `N-002` and `N-001`.

`X-003`, `UCPlanar.External.Unicoherence`, transcribes unicoherence of the
sphere in the form the face walks use: for a connected plane graph, the frontier
of every bounded face is connected. It is consumed by `N-003`, `N-002` and
`N-001`.

The classical Liouville theorem for a periodic network, recalled at
`ucplanar.tex:159`, is proved rather than cited: `LiouCHeat`, `LiouKilled` and
`LiouPeriodic` show that a periodic network is recurrent — the Nash-Williams
criterion applied to the boundary cuts of the coordinate boxes, whose total
conductance grows at most linearly in the radius — and that on a recurrent
network every bounded harmonic function is constant.

The discrete Remez inequality of Buhovsky, Logunov, Malinnikova and Sodin,
Corollary 2.2, cited at `ucplanar.tex:504`, is proved rather than cited:
`RemezCheb`, `RemezLagrange`, `RemezMeasure` and `RemezDiscrete` show that a
real polynomial of degree at most `m` with `m < R`, bounded by `A` on at least
half of the integer points of `[-R, R]`, is bounded by `A (16R/(R-m))^m` on the
integer points of `[-2R, 2R]`.  Between consecutive points of the dense set, at
least `|S| - m` unit intervals contain no root of the derivative, so the
admissible set has positive Lebesgue measure and the sharp Remez inequality
applies; the sharp form is Bojanov's compression argument against the Chebyshev
polynomial. It is consumed by `N-006`, `N-008` and `N-001`.

`X-007`, `UCPlanar.External.MoserEstimate`, transcribes the discrete Moser
estimate of Delmotte, Proposition 5.3, in the form the derivative bound
consumes: for nested squares `Q_r` and `Q_s` and a function harmonic on `Q_s`,
each value of `f` on `Q_r` is at most `C/(s-r)` times the `ℓ²` norm of `f`
over `Q_s`, with a constant that depends on the network but not on the two
scales. It is consumed by `N-007`, `N-006`, `N-008` and `N-001`.

What is deliberately not assumed: the paper's own theorems are not hypotheses of
one another. `N-003`, `N-002`, `N-006`, `N-007` and `N-008` are proved from the
cited inputs and the graph hypotheses alone, and `N-001` is proved from `N-002`
and `N-008`. The counterexample `N-005` uses no cited
input. No statement assumes the conclusion of another statement of the paper.

This description matches the Lean tree it accompanies; the registered declarations are checked against `ledger/manifest.yaml` by `tools/check_manifest.py`.
