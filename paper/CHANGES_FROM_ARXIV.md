# Differences from the arXiv version

The formalization follows `paper/ucplanar.tex`, which is arXiv:2309.13728v2 with the corrections
below. The arXiv source will be replaced by the corrected text. The unmodified arXiv source is
`paper/ucplanar-arxiv.tex`; the class files, bibliography and figures it needs to compile are in
`paper/arxiv/`. The file `diff -u paper/ucplanar-arxiv.tex paper/ucplanar.tex` consists of exactly
the changes listed here. Line numbers refer to the corrected file.

## Abstract (line 136)

arXiv: "a discrete harmonic function which is bounded on a large portion of a periodic planar
graph is constant."
Corrected: "... of a periodic planar graph with periodic conductances is constant."

Without periodic conductances the claim is false. On the square lattice put `g(i) = i/(1+|i|)`
and `f(i,j) = g(i)`, with horizontal conductance `1/(g(i+1)-g(i))` and vertical conductance one:
`f` is harmonic, bounded and not constant. Theorem 1.1 already assumes periodic conductances.

## Section 1, definition of a periodic planar graph (line 142)

arXiv: "a graph for which there exists an embedding into the plane R² which is invariant under
translation by a two-dimensional-lattice L."
Corrected: "a connected, locally finite graph with a proper embedding into the plane R², with edges
drawn as polygonal arcs, which is invariant under translation by a two-dimensional-lattice L, with
finitely many vertex and edge orbits. Here proper means that every compact set meets only finitely
many vertices and edges. We assume that the faces have uniformly bounded diameter and that the
number of vertices incident to a face is uniformly bounded."

The printed definition admits the edgeless square lattice, on which `f(0) = 0` and `f = 2`
elsewhere is harmonic and not constant with bounded-value density one, and it admits infinitely
many vertices in a fundamental cell, so that the quotient `F` need not be finite. The added
hypotheses are the ones the arguments use: connectedness in Section 3, the finite quotient, the
face bounds in Lemma 2.1, and properness in the ball estimates. Every graph of the intended class
has a drawing of this form.

## Section 1, the bounded Liouville theorem (line 159)

arXiv: "Recall that any bounded harmonic function on G is constant."
Corrected: "Recall that, when the conductances are invariant under translation by L, any bounded
harmonic function on G is constant."

The example given for the abstract shows that periodicity is needed. With periodic conductances
there are finitely many conductance values, the network is recurrent, and a bounded harmonic
function is constant.

## Lemma 2.1 (`lemma:topological-lemma`), hypothesis (2) (line 226)

arXiv: "P and M are contained in the union of γ and the finite component of G ∖ γ."
Corrected: "... the union of γ and the vertices in the bounded component of the plane complement
of the drawn cycle γ."

Deleting a cycle need not leave a unique finite graph component: a facial cycle encloses no
vertex, and the lattice polygon with corners (0,0), (2,0), (2,1), (4,1), (4,0), (6,0), (6,3),
(4,3), (4,2), (2,2), (2,3), (0,3) encloses the vertices (1,1), (1,2), (5,1), (5,2), which form two
graph components. The bounded region of the plane is unique by the Jordan curve theorem.

## Lemma 2.1, dependence of the constant (line 230)

arXiv: "depending only on the maximum size of a face in the graph G"
Corrected: "depending only on the maximum vertex degree d and the maximum number L of vertices
incident to a face in G"

Face size alone does not suffice. Insert an n-gonal bipyramid into a face of a periodic
triangulation and repeat periodically; with γ the rim, P and M two rim vertices and Z the other
n−2 rim vertices, the face paths through a pole satisfy every hypothesis, all faces are
triangles, and |Z|/|γ| = 1 − 2/n, which exceeds the printed coefficient 162/163 at n = 400.

## Proof of Lemma 2.1, the packing bound (lines 234–241, `eq:bound-on-density`)

arXiv: the definition of `prev_P`, `prev_M`, a subset Z' on which p and m are injective and the
paths disjoint, and the bound |Z'|/|Z| ≥ (size of largest face)^{-4}.
Corrected: Z' is a maximal subset whose distinct vertices have face-distance greater than 4, the
face-distance is defined, and with K = (1+dL)^4 the bound reads |Z| ≤ K|Z'|. Disjointness of the
paths and injectivity of p and m follow because p(z), m(z) and β_z are within face-distance 2 of z.
The definition of `prev_P` and `prev_M` is deleted, since the new counting argument does not use
it.

A ball of face-radius 4 is not bounded by the face size alone; a closed cofacial neighbourhood has
at most 1 + dL vertices. The printed ratio is also undefined when Z is empty.

## Proof of Lemma 2.1, the count along γ (lines 243–247)

arXiv: the three-case construction of the sets S_j, the Jordan curve contradiction in case 3,
and α_F = (1 + ½(size of largest face)^{-4})^{-1}.
Corrected: with B = γ ∖ Z, discard the at most |B| vertices of Z' at face-distance at most 2 from
B; for the t remaining vertices the sign endpoints lie strictly inside γ and each path β_z lies in
the closed disk or can be replaced by the constant path at its terminal vertex on γ. Contracting
sign trees to vertices of B and the paths to their roots gives a simple plane bipartite graph with
t roots of degree two on the unbounded face and s ≤ |B| sign vertices, and Euler's formula gives
t ≤ 2s ≤ 2|B|. Hence |Z| ≤ 3K|B| and α_F := 3K/(3K+1).

The printed scan does not handle a face path on the exterior side of γ, and its index bookkeeping
fails when the terminal edges of the paths meet at shared sign endpoints. The replacement handles
both and yields an explicit coefficient.

## Figure 3 caption (`fig:third-case`, lines 253–255)

arXiv: "The contradiction in case 3 of the proof of Lemma 2.1. The red circle is prev_P(v_{i_{k'}})
= ... and the paths γ_P and γ_M are red and blue solid lines respectively."
Corrected: "The planar separation underlying Lemma 2.1: two paths inside γ joining alternating
vertices of γ must meet. The same color scheme as Figure 2 is used and the two paths, through G[P]
and through G[M], are red and blue solid lines respectively."

The corrected proof has no numbered cases and no indices k', j'.

## Section 3, Step 1, parallel dual edges (line 278)

arXiv: "a finite induced subgraph K of G which is 3-edge connected and for which there are only
two edges, e₁ and e₂, which connect K to G ∖ K. Let G' be ... the effective conductance of K
between the endpoints ... for each finite 3-edge connected component of G"
Corrected: "a finite connected component K of the graph obtained by removing two edges, e₁ and e₂,
which are the only edges that connect K to G ∖ K. Finiteness follows from the one-endedness of G.
If the two outside endpoints coincide, the maximum principle makes f constant on K, and we delete
K. Otherwise, let G' be ... the effective conductance of K together with e₁ and e₂ between the
outside endpoints ... for the translates of each such finite component"

Parallel dual edges give a two-edge cut, not a three-edge-connected piece: subdividing an edge of
a lattice gives two-edge cuts around paths. The effective conductance must include the two
attaching edges, as a path of three unit edges shows, and the case of coinciding endpoints would
otherwise produce a loop.

## Section 3, Step 2 (line 282)

arXiv: "some ∂B_m for m ∈ [1.5n, 2n] such the number of vertices for which f(v) ≠ 0 and which are
adjacent to a face in ∂B_m is at most Cεn."
Corrected: "m ∈ [1.5n, 2n−2C_F], where C_F exceeds one plus the maximum graph diameter of a face,
such the number of vertices for which f(v) ≠ 0 and which are within graph distance C_F of a vertex
adjacent to a face in ∂B_m is at most Cεn."

Step 3 charges each vertex of γ ∖ Z to a nonzero vertex within bounded distance of it, which need
not be adjacent to a face of ∂B_m; the count must include those vertices. The margin 2C_F keeps
all counted vertices in B_{2n}, where the density hypothesis applies, and the pigeonhole bound
holds because each vertex is counted for boundedly many m.

## Section 3, Step 3, the radius (line 293)

arXiv: "Let m ∈ [1.5n, 2n] be given by Step 2."
Corrected: "Let m ∈ [1.5n, 2n−2C_F] be given by Step 2."

This is the range chosen in Step 2.

## Section 3, Step 3, the face cluster (line 294)

arXiv: "Let N be the set of faces of G[B_m] which are adjacent to at least one vertex where f is
nonzero."
Corrected: "Let U be the set of vertices of B_m which are nonzero or adjacent to a vertex where f
is nonzero, and let N be the set of faces of G which are adjacent to at least one vertex of U."

Faces of the induced subgraph G[B_m] are not faces of G and cannot be vertices of G*. With the
printed set, the face walk of the third hypothesis can stop at a vertex of γ itself, and the
opposite-sign neighbour produced by harmonicity can then lie outside γ, so the pair of sign
witnesses is not admissible in Lemma 2.1. With U, a vertex of γ has no nonzero neighbour, and the
walk stops strictly inside γ.

## Section 3, Step 3, the boundary cycle (line 295)

arXiv: "Let γ be a cycle in G around the boundary of K ∪ {vertices in finite connected components
of G* ∖ K}."
Corrected: "Fill K by adjoining the finite connected components of G* ∖ K. The filled set and its
complement are connected in G*, so their edge boundary is a finite bond in G* and hence a simple
cycle γ in G."

The printed sentence asserts the existence of a single simple cycle without a reason. The
periodic dual is one-ended, so both sides of the filled set are connected, and planar cycle–cut
duality gives a simple cycle.

## Section 3, Step 3, the interior of γ (line 297)

arXiv: "Let D be the unique finite connected component of G ∖ γ. First, we note that D contains
x₀ ∈ B_n and a vertex adjacent to ∂B_m, so it has diameter at least n/2 and therefore its boundary,
γ, has length at least n/2."
Corrected: "Let D be the set of vertices in the bounded component of the plane complement of the
drawn cycle γ. The set γ ∪ D contains x₀ ∈ B_n and a vertex adjacent to ∂B_m, so its graph
diameter is at least n/2 − C(F). Periodicity then gives |γ| ≥ c(F)n for all sufficiently large n."

The examples for hypothesis (2) of Lemma 2.1 show that the graph component need not exist, and
the vertex adjacent to ∂B_m may lie on γ. The length of γ is comparable to the diameter of the
region only up to constants of the periodic graph.

## Section 3, Step 3, the third hypothesis (line 299)

arXiv: "there is some vertex w adjacent to F on which f(w) ≠ 0. Choose w to be the vertex closest
to z with this property, and let β = {z = w₀, ..., w_ℓ} be a shortest path such that w_ℓ is
adjacent to w. By minimality of β, we have f(w_ℓ) = 0 and therefore w_ℓ is also adjacent to some
vertex y with sgn f(y) = −sgn f(w)."
Corrected: "some vertex adjacent to F lies in U. Let β = {z = w₀, ..., w_ℓ} be a shortest path along
the boundary of F from z to a vertex of U. Since F ∉ ∂B_m, the path β lies in B_m, so by
minimality f vanishes on w₀, ..., w_{ℓ−1} and on their neighbors. In particular f(w_ℓ) = 0, so w_ℓ
is adjacent to a vertex w with f(w) ≠ 0 and, by harmonicity, to some vertex y with
sgn f(y) = −sgn f(w). By maximality of K, every face adjacent to w_ℓ lies in K, so w_ℓ ∈ D and
both w and y lie in γ ∪ D."

Lemma 2.1 needs a path along one face and sign witnesses inside γ. The printed path is not along
a face, and the opposite-sign neighbour of a vertex of γ can lie outside γ, for example a zero
vertex with one interior neighbour of value 1 and one exterior neighbour of value −1.

## Section 3, Step 3, the final count (lines 302–304)

arXiv: "Hence, at least (1−α_F) vertices in γ are adjacent to a face in ∂B_m. Each of these faces
must be adjacent to a vertex for which f is nonzero. However, since |γ| ≥ n/2, this contradicts
Step 2"
Corrected: "Hence, at least (1−α_F)|γ| vertices in γ are adjacent to a face in ∂B_m. Each vertex of
γ is adjacent to a face in K, so it lies within graph distance C_F of a vertex for which f is
nonzero. For the vertices above, such a vertex is counted in Step 2, and it lies within graph
distance C_F of at most C(F) vertices of γ. However, since |γ| ≥ c(F)n, this contradicts Step 2"

The factor |γ| was missing. A face of ∂B_m adjacent to a vertex of γ need not belong to K, so the
nonzero vertex is found through a face of K instead, with bounded multiplicity.

## Section 3, Remark after the proof (lines 307–308)

arXiv: "the density hypothesis ... may be replaced, as in Step 2, by a bound on the number of
non-zero vertices adjacent to ∂B_{2n}. In particular, this shows that if there are infinitely many
contours surrounding the origin for which the harmonic function has a high density of zeros, then
the function must be zero identically."
Corrected: "the density hypothesis ... may be replaced by a bound of c(F)n on the number of
non-zero vertices counted in Step 2, for some m ∈ [1.5n, 2n−2C_F] and sufficiently small
c(F) > 0. In particular, a globally harmonic function satisfying this bound for arbitrarily large n
is identically zero."

The contour statement is false. With a_i repeating 0, 1, 0, −1 and q = 2 + √3, the function
f(i,j) = a_i q^j is harmonic on Z² and not zero, while the boundary of [−2n, 2n] × [−n², n²] has
zero proportion 1 − 1/(n+2). The argument controls the number of nonzeros near one sphere on the
scale n, not their proportion on a contour.

## Section 4, Step 1, the pigeonhole band (lines 326–327)

arXiv: "a sufficiently large K(δ) and an integer A ∈ [1, K^n] for which
|{v : A < |f(v)| < 2Θ(max degree)A}| < δn."
Corrected: "a sufficiently large K(δ, F, Θ) and a number A ∈ [1, K^n] for which
|{v : A < |f(v)| ≤ 2Θ(max degree)A}| < δn."

The pigeonhole principle over the bands (q^j, q^{j+1}] with q = 2Θ(max degree) gives a real, not
integer, threshold, and the constant depends on the geometry and on Θ. The upper endpoint belongs
to the band because the opposite-sign argument applies to neighbours with |f| > qA.

## Section 4, Step 2, the covering argument (lines 336–340)

arXiv: δ = C^{-1}ε₁^{-1/2}ε^{1/2}, a cover of B_n by δ² balls of radius δn, Step 1 applied on
each ball, and max_{B_n}|f| ≤ α^{(C^{-1}ε₁^{-1/2})ε^{1/2}n}.
Corrected: δ = C₁ε₁^{-1/2}ε^{1/2} with C₁ large, r = ⌊δn⌋, a cover of B_n by at most Cδ^{-2}
balls B_r(z_i), Step 1 applied on the doubled balls B_{2r}(z_i), the bound
max_{B_n}|f| ≤ Cα^r ≤ exp(A√ε n), and the separate cases ε = 0 and δn < 2n₀.

In two dimensions order δ^{-2} balls are needed, Step 1 bounds f on B_r from the density on
B_{2r}, the prefactor C of Step 1 must be absorbed, and Step 1 applies only on radii at least n₀.
On the remaining small scales the exceptional set is empty.

## Theorem 5.1 (`theorem:counterexample`, line 372)

arXiv: "there is a harmonic function on (Z², E(A₁,A₂,A₃,A₄)) supported on the diagonal line
{x₁ = x₂}."
Corrected: "there is a harmonic function h with h(0,0) = 1 on (Z², E(A₁,A₂,A₃,A₄)) whose support
is the diagonal line {x₁ = x₂}."

Read as an inclusion of supports, the printed statement is satisfied by the zero function. The
construction in the proof has h(0,0) = z₀ = 1 and diagonal values z_i ≠ 0.

## Appendix A, standing hypothesis (line 408)

Added: "Throughout this appendix, the conductances a are invariant under translation by L."

The proof of Lemma A.2 uses this, as its text says, and Proposition A.3 and Theorem A.1 depend on
Lemma A.2.

## Theorem A.1 (`theorem:lower-bound`, line 413)

arXiv: "There is some b > 0 such that the following holds."
Corrected: "There is some b > 0 such that the following holds for every f with Δf = 0 on G."

Without harmonicity, f(0) = 2 and f = 0 elsewhere satisfies every hypothesis and violates the
conclusion.

## Proposition A.3 (`prop:three-ball`, lines 459–463)

arXiv: "There is some ε = ε(G) such that, if [density condition] and |f| ≤ M on Q_{4N}, then"
Corrected: "There exist ε = ε(G) > 0 and an integer k = k(G, a) ≥ 4 such that, if [density
condition] and Δf = 0 and |f| ≤ M on Q_{kN}, then"

Without harmonicity a single spike of height M in Q_{2N} ∖ Q_N violates the conclusion. The
outer square Q_{4N} cannot be reached: the proof needs Lemma A.2 on the conclusion square Q_{2N},
hence harmonicity on Q_{6N/c(α)}, and iterating the statement at smaller scales degrades the
exponent of M through 1/2, 3/4, 7/8, and so on. In the square lattice the exact Poisson kernel of
a square gives the constant 4.

## Proof of Proposition A.3, the reduction (after line 471)

Deleted: "As in [BLMS], it suffices to prove the following statement which implies the desired
result by a routine covering argument. *There is some ε > 0 and k ∈ N such that, if f is discrete
harmonic with |f| ≤ M on Q_{kN} ... on Q_{2N}.*"

The corrected proposition is this statement, and the covering argument does not exist, for the
reason given in the previous entry.

## Proof of Proposition A.3, small M and N (line 477)

Added before the two cases: "We may assume M ≥ 1 and N ≥ 4. For M < 1 use |f| ≤ M ≤ M^{1/2}, and
absorb the finitely many smaller positive N into C exp(−cN)M."

The proof uses N ≥ 4 to get γ ≤ 3/4, and the composition of the two directions below uses M ≥ 1.

## Proof of Proposition A.3, the approximation domain (lines 487 and 502)

arXiv: ‖f − p‖_{L^∞(Q_N ∩ (v+L))} ≤ α^{γN}M, and the same with exp(βN)M.
Corrected: Q_{2N} in place of Q_N in both displays.

The approximation error is used at every s ∈ [−2N, 2N], so it is needed on Q_{2N}.

## Proof of Proposition A.3, the one-dimensional exponent (lines 495 and 497)

arXiv: "≤ 3α^{−γN/2} ≤ (3/α)M^{1/2}", with the conditions log(16/(1−γ)) ≤ −½ log α and
log 64 ≤ −½ log α.
Corrected: "≤ 3α^{−γN/4} ≤ (3/α^{1/4})M^{1/4}", with the conditions log(16/(1−γ)) ≤ −¼ log α and
log 64 ≤ −¼ log α.

The one-dimensional step is applied twice, and the second application starts from the bound of
the first. By homogeneity a one-dimensional exponent θ composes to 2θ − θ², which is 3/4 at
θ = 1/2. The exponent 1/4 gives 7/16 ≤ 1/2.

## Proof of Proposition A.3, the second case (line 500)

arXiv: "approximate u instead by a polynomial of degree ½N"
Corrected: "approximate f instead by a polynomial of degree at most ⌊N/2⌋"

The function is f, and the degree is an integer. The Remez factor stays at most 32^{N/2}.

## Proof of Proposition A.3, the constants and the two directions (line 514)

arXiv: "the desired constraints are satisfied for β := −log 32 and α := 2^{−12}."
Corrected: "... for β := −log 32 and α := 2^{−24}. The one-dimensional estimate is therefore
C(M^{1/4} + exp(−cN)M). More generally, a bound T > 0 at the good sites gives
C(T^{3/4}M^{1/4} + exp(−cN)M) by rescaling. Applying this estimate first horizontally and then
vertically gives |f| ≤ CM^{7/16} + C exp(−3cN/4)M ≤ CM^{1/2} + C exp(−3cN/4)M on Q_{2N}, since
M ≥ 1."

The condition log 64 ≤ −¼ log α fails at α = 2^{−12} and holds with equality at α = 2^{−24}, where
β/log α = 5/24 ≤ 1/2 still gives γ ≤ 3/4. The printed proof did not carry out the second
direction.

## Proof of Theorem A.1 (line 522)

arXiv: "replacing each reference to Theorem 3.1 (the discrete three-circle theorem) with
Proposition A.3, which is the same statement generalized to periodic planar graphs."
Corrected: "... with Proposition A.3 applied to the translates of f by L, which is the same
statement generalized to periodic planar graphs with Q_{kN} in place of Q_{4N}. The argument
there tolerates every fixed k at the cost of the constants. The chain of three-ball inequalities
only gains once the maximum of |f| exceeds a fixed constant, and this follows from
(`eq:derivative-bound`) at m = 1. Indeed, if |f| were bounded by a constant on Q_{C√N} for a
sufficiently large C, then the differences D₁f and D₂f would be small multiples of N^{−1/2} on
Q_{C√N/3}. Hence f > 1 at every vertex of Q_K, for K = ⌈√N⌉, in the translated lattice of a vertex
of Q_{⌊√N⌋} where f ≥ 2. These vertices form a fixed positive fraction of Q_K ∩ V, which contradicts
the density hypothesis at the scale K for ε sufficiently small."

Proposition A.3 now has the outer square Q_{kN}, and on a periodic graph it holds at squares
centred at points of L, which the translations provide. Three-ball inequalities alone cannot force
growth, since a harmonic function with |f| ≤ 2 satisfies all of them; the starting constant comes
from the gradient estimate, which on the square lattice is standard and on a periodic graph is
(`eq:derivative-bound`) at m = 1.
