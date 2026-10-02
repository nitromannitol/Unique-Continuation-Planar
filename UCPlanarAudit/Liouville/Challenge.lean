import Mathlib

/-!
# Theorem 1.1 (`theorem:liouville`): comparator challenge

Mathlib-only comparator challenge for Theorem 1.1 (`theorem:liouville`) of Bou-Rabee,
Cooperman and Ganguly, *Unique continuation on planar graphs* (Discrete Analysis 2025:16). The
certified statement is `UCPlanar.Frozen.liouville`, restated in `UCPlanar/MainTheorems.lean`
as `UCPlanar.liouville`. Content: for conductances on a periodic plane graph that are
invariant under the translation lattice there is `ε > 0` such that every function harmonic on
the whole graph, whose set `{|f| ≤ 1}` has a density limit at least `1 - ε` in the
graph-metric balls about some vertex, is constant.

Only Mathlib is imported.  The vocabulary between `VOCABULARY-BEGIN` and
`VOCABULARY-END` rebuilds, from Mathlib primitives, every definition needed to
read the theorem: lattice sites, graph-metric balls, conductances, the network
Laplacian and harmonic functions (copied from `Lattice-Probability`), polygonal
sets of the plane (copied from the Schoenflies library), plane embeddings and
their faces, periodic plane graphs with their squares, balls and density
notions, the crossing conductances of the counterexample, and the cited
results.  It is a statement-level copy of the definitions the repository uses
(see `UCPlanarAudit/README.md` for the provenance table) and is byte-identical in all
four challenges.  The sole intentional `sorry` is the proof of the final
theorem.

## Cited results

The paper uses results from the literature without proof.  The repository
does not prove them either: each is a proposition taken as an explicit
hypothesis, and this challenge carries the same hypotheses, restated in the
vocabulary:
   * `External.MoserEstimate`: the discrete Moser estimate (Delmotte 1999, Proposition 5.3);
   * `External.EdgeSplitting`: Janiszewski's theorem at a point (Newman, Chapter V, Theorem 9.3);
   * `External.Unicoherence`: unicoherence of the sphere, as connected face frontiers
     (Newman, Chapter VI).

## Presentation deltas

None at the level of the displayed statement: the theorem below is the
statement of `UCPlanar.liouville` with every repository and library name replaced by
its vocabulary copy.  The structures of the vocabulary (`IsCond`,
`PlaneEmbedding`, `PeriodicGraph`, `PeriodicPlaneGraph`) are new inductive
types; the solution transports them field by field
(`UCPlanarAudit/Support/LiouvilleBridge.lean`).
-/

-- VOCABULARY-BEGIN
namespace UCPlanarAudit

/-! ## 1. Sites, graph balls, conductances and harmonic functions

Copied from the shared library `Lattice-Probability` (`LatticeProb/Site.lean`,
`LatticeProb/Graph/Basic.lean`, `LatticeProb/Network/Basic.lean`). -/

section LatticeProb

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

variable {V : Type*}

/-- The graph-metric ball `B(x, r) = {v : dist(v, x) ≤ r}`. -/
def closedBall (G : SimpleGraph V) (x : V) (r : ℕ) : Set V := {v | G.edist v x ≤ r}

/-- `c` is a conductance on `G`: symmetric, positive on the edges of `G`, and
zero on every pair that is not an edge. -/
structure IsCond (G : SimpleGraph V) (c : V → V → ℝ) : Prop where
  symm : ∀ x y, c x y = c y x
  pos : ∀ ⦃x y⦄, G.Adj x y → 0 < c x y
  zero_of_not_adj : ∀ ⦃x y⦄, ¬ G.Adj x y → c x y = 0

/-- The network Laplacian `Δ_c f(x) = ∑_{y ∼ x} c(x,y) (f y - f x)`. -/
noncomputable def netLaplacian (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (f : V → ℝ) (x : V) : ℝ :=
  ∑ y ∈ G.neighborFinset x, c x y * (f y - f x)

/-- `f` is `c`-harmonic on `S`. -/
def HarmonicOn (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ) (f : V → ℝ)
    (S : Set V) : Prop :=
  ∀ x ∈ S, netLaplacian G c f x = 0

end LatticeProb

/-! ## 2. Polygonal sets of the Euclidean plane

Copied from the pinned Schoenflies library (`Schoenflies/Plane.lean`,
`Schoenflies/PolyPath.lean`, `Schoenflies/Polygonal.lean`). -/

section Polygonal

/-- The Euclidean plane. -/
abbrev EPlane := EuclideanSpace ℝ (Fin 2)

/-- The carrier of a polygonal path: the union of the segments joining consecutive vertices. -/
def poly : List EPlane → Set EPlane
  | [] => ∅
  | [v] => {v}
  | u :: v :: rest => segment ℝ u v ∪ poly (v :: rest)

/-- A set is polygonal when it is the carrier of a finite vertex list. -/
def IsPolygonal (A : Set EPlane) : Prop := ∃ vs : List EPlane, A = poly vs

end Polygonal

/-! ## 3. Plane embeddings (`UCPlanar/Support/Planar.lean`, `TopoEdgeSet.lean`,
`TopoTransport.lean`) -/

section Planar

open scoped Classical

/-- The real coordinate plane. -/
abbrev Plane := Fin 2 → ℝ

/-- The identity homeomorphism from the coordinate plane to the Euclidean plane. -/
noncomputable def planeHomeo : Plane ≃ₜ EPlane :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm

/-- A topological embedding of a simple graph in the plane: injective vertex positions and
polygonal edge arcs that meet only at common endpoints. -/
structure PlaneEmbedding {V : Type*} (G : SimpleGraph V) where
  pos : V → Plane
  pos_injective : Function.Injective pos
  edge : ∀ {x y}, G.Adj x y → Path (pos x) (pos y)
  edge_injective : ∀ {x y} (h : G.Adj x y), Function.Injective (edge h)
  edge_symm : ∀ {x y} (h : G.Adj x y), Set.range (edge h) = Set.range (edge h.symm)
  vertex_on_edge : ∀ {x y} (h : G.Adj x y) z,
    pos z ∈ Set.range (edge h) → z = x ∨ z = y
  edge_inter : ∀ {x y u v} (h : G.Adj x y) (k : G.Adj u v),
    ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) →
    Set.range (edge h) ∩ Set.range (edge k) ⊆
      ({pos x, pos y} : Set Plane) ∩ {pos u, pos v}
  edge_polygonal : ∀ {x y} (h : G.Adj x y),
    IsPolygonal (planeHomeo '' Set.range (edge h))

/-- The union of the drawn vertices and edges. -/
def PlaneEmbedding.trace {V : Type*} {G : SimpleGraph V}
    (E : PlaneEmbedding G) : Set Plane :=
  Set.range E.pos ∪ {p | ∃ x y, ∃ h : G.Adj x y, p ∈ Set.range (E.edge h)}

/-- Faces are connected components of the complement of the drawing. -/
def PlaneEmbedding.IsFace {V : Type*} {G : SimpleGraph V}
    (E : PlaneEmbedding G) (F : Set Plane) : Prop :=
  ∃ p ∉ E.trace, F = connectedComponentIn E.traceᶜ p

/-- A vertex is incident to a face when its image lies in the face frontier. -/
def PlaneEmbedding.Incident {V : Type*} {G : SimpleGraph V}
    (E : PlaneEmbedding G) (F : Set Plane) (x : V) : Prop :=
  E.pos x ∈ frontier F

/-- A uniform bound on the number of vertices incident to a face. -/
def PlaneEmbedding.FaceBound {V : Type*} {G : SimpleGraph V}
    (E : PlaneEmbedding G) (L : ℕ) : Prop :=
  ∀ F, E.IsFace F → {x | E.Incident F x}.Finite ∧ {x | E.Incident F x}.ncard ≤ L

end Planar

section Trace

open Set

/-- The plane arc drawn by an unordered pair of adjacent vertices. -/
def PlaneEmbedding.arcOf {V : Type*} {G : SimpleGraph V}
    (E : PlaneEmbedding G) (e : Sym2 V) : Set Plane :=
  {p | ∃ x y, ∃ h : G.Adj x y, e = s(x, y) ∧ p ∈ Set.range (E.edge h)}

/-- The drawing of a set of edges. -/
def PlaneEmbedding.edgesTrace {V : Type*} {G : SimpleGraph V}
    (E : PlaneEmbedding G) (T : Set (Sym2 V)) : Set Plane :=
  ⋃ e ∈ T, E.arcOf e

/-- The bounded complementary components of a set, in any ambient space. -/
def insideOf {X : Type*} [TopologicalSpace X] [Bornology X] (S : Set X) : Set X :=
  {x | x ∉ S ∧ Bornology.IsBounded (connectedComponentIn Sᶜ x)}

end Trace

/-! ## 4. Periodic plane graphs (`UCPlanar/Support/Periodic.lean`, `UCPlanar/Basic.lean`,
`UCPlanar/Support/Growth.lean`) -/

section Periodic

open scoped Classical

/-- A connected, locally finite periodic graph with a finite set of vertex orbits. -/
structure PeriodicGraph (V : Type*) where
  graph : SimpleGraph V
  locallyFinite : graph.LocallyFinite
  connected : graph.Connected
  pos : V → Plane
  pos_injective : Function.Injective pos
  period : Plane ≃ₗ[ℝ] Plane
  shift : Site 2 → V → V
  shift_zero : ∀ x, shift 0 x = x
  shift_add : ∀ a b x, shift (a + b) x = shift a (shift b x)
  shift_adj : ∀ a x y, graph.Adj (shift a x) (shift a y) ↔ graph.Adj x y
  pos_shift : ∀ a x, pos (shift a x) = pos x + period (fun i => (a i : ℝ))
  representatives : Finset V
  covers : ∀ x, ∃ v ∈ representatives, ∃ a, shift a v = x
  finite_squares : ∀ R : ℝ, {x | ∀ i, |pos x i| ≤ R}.Finite
  finite_balls : ∀ x n, (closedBall graph x n).Finite

attribute [instance] PeriodicGraph.locallyFinite

/-- A periodic graph with a compatible plane embedding. -/
structure PeriodicPlaneGraph (V : Type*) extends PeriodicGraph V where
  embedding : PlaneEmbedding graph
  embedding_pos : embedding.pos = pos
  edge_shift : ∀ a x y (h : graph.Adj x y),
    Set.range (embedding.edge ((shift_adj a x y).mpr h)) =
      (fun p => p + period (fun i => (a i : ℝ))) '' Set.range (embedding.edge h)
  proper_edges : ∀ R : ℝ, {x | ∃ y, ∃ h : graph.Adj x y,
    ∃ p ∈ Set.range (embedding.edge h), ∀ i, |p i| ≤ R}.Finite
  bounded_faces : ∃ L, embedding.FaceBound L
  face_diameter : ∃ R : ℝ, ∀ F, embedding.IsFace F → ∀ p ∈ F, ∀ q ∈ F, dist p q ≤ R

/-- The vertices in a geometric square of radius `R`. -/
noncomputable def PeriodicGraph.square {V : Type*}
    (P : PeriodicGraph V) (R : ℝ) : Finset V :=
  (P.finite_squares R).toFinset

/-- A finite graph metric ball. -/
noncomputable def PeriodicGraph.ball {V : Type*}
    (P : PeriodicGraph V) (o : V) (n : ℕ) : Finset V :=
  (P.finite_balls o n).toFinset

/-- Translation invariance of an undirected conductance. -/
def PeriodicGraph.PeriodicConductance {V : Type*}
    (P : PeriodicGraph V) (c : V → V → ℝ) : Prop :=
  ∀ a x y, c (P.shift a x) (P.shift a y) = c x y

/-- The fraction of a finite set on which `|f| ≤ a`, with value zero on the empty set. -/
noncomputable def boundedDensity {V : Type*} (S : Finset V) (f : V → ℝ)
    (a : ℝ) : ℝ :=
  ((S.filter (fun x => |f x| ≤ a)).card : ℝ) / S.card

/-- The number of vertices of a finite set on which `|f| > a`. -/
noncomputable def exceptionalCount {V : Type*} (S : Finset V) (f : V → ℝ)
    (a : ℝ) : ℕ :=
  (S.filter (fun x => a < |f x|)).card

/-- Strict uniform bounds on the edge conductances. -/
def UniformlyElliptic {V : Type*} (G : SimpleGraph V) (c : V → V → ℝ)
    (lam big : ℝ) : Prop :=
  0 < lam ∧ lam < big ∧ ∀ x y, G.Adj x y → lam < c x y ∧ c x y < big

end Periodic

/-- Existence of the bounded-value density limit, with its lower bound. -/
def PeriodicGraph.HasBoundedDensity {V : Type*} (P : PeriodicGraph V)
    (o : V) (f : V → ℝ) (ε : ℝ) : Prop :=
  ∃ d : ℝ, 1 - ε ≤ d ∧ Filter.Tendsto
    (fun n : ℕ => boundedDensity (P.ball o n) f 1) Filter.atTop (nhds d)

/-! ## 5. The conductances of the non-planar counterexample
(`UCPlanar/Support/CrossingGraph.lean`) -/

section Crossing

open scoped Classical

/-- The vector `(1,1)` of the square lattice. -/
def diagonalStep : Site 2 := fun _ => 1

/-- The directed edge list issued from an even vertex. -/
def crossingRelation (x y : Site 2) : Prop :=
  Even (x 0 + x 1) ∧
    (y = x - unit 0 ∨ y = x - unit 1 ∨
     y = x + unit 0 ∨ y = x + unit 1 ∨
     y = x + (2 : ℤ) • diagonalStep ∨
     y = x - (2 : ℤ) • diagonalStep ∨
     y = x + diagonalStep ∨ y = x - diagonalStep)

/-- The undirected graph generated by the edge list: the square lattice with the diagonal
jumps by `±(1,1)` and `±(2,2)` from even vertices. -/
def crossingGraph : SimpleGraph (Site 2) :=
  SimpleGraph.fromRel crossingRelation

/-- The contribution from one endpoint to the conductance of an edge.
Each diagonal edge receives half its conductance from each endpoint. -/
noncomputable def crossingOutgoing (a b t d : ℝ)
    (x y : Site 2) : ℝ :=
  if Even (x 0 + x 1) then
    if y = x - unit 0 ∨ y = x - unit 1 then a
    else if y = x + unit 0 ∨ y = x + unit 1 then b
    else if y = x + (2 : ℤ) • diagonalStep ∨
      y = x - (2 : ℤ) • diagonalStep then t / 2
    else if y = x + diagonalStep ∨ y = x - diagonalStep then d / 2
    else 0
  else 0

/-- The symmetric conductance `𝓔(A₁, A₂, A₃, A₄)` with parameters `a, b, t, d`. -/
noncomputable def crossingConductance (a b t d : ℝ)
    (x y : Site 2) : ℝ :=
  crossingOutgoing a b t d x y + crossingOutgoing a b t d y x

end Crossing

/-! ## 6. The results the paper cites without proof

Each is a proposition, taken as an explicit hypothesis by the theorems that use it; none is
proved here.  Copied from `UCPlanar/External/`. -/

namespace External

section Plane

open scoped Classical

/-- Janiszewski's theorem at a point, for the drawings of two finite edge sets of a plane
graph (Newman, *Elements of the Topology of Plane Sets of Points*, Chapter V, Theorem 9.3),
assumed. -/
def EdgeSplitting {V : Type*} {G : SimpleGraph V}
    (E : PlaneEmbedding G) : Prop :=
  ∀ T₁ T₂ : Finset (Sym2 V), ↑T₁ ⊆ G.edgeSet → ↑T₂ ⊆ G.edgeSet → Disjoint T₁ T₂ →
    ∀ v : V, (∀ z : V, (∃ e ∈ T₁, z ∈ e) → (∃ f ∈ T₂, z ∈ f) → z = v) →
    ∀ p : Plane, p ∈ insideOf (E.edgesTrace ↑(T₁ ∪ T₂)) →
      p ∈ insideOf (E.edgesTrace ↑T₁) ∨
        p ∈ insideOf (E.edgesTrace ↑T₂)

end Plane

/-- Unicoherence of the sphere, in the form that the frontier of every bounded face of the
drawing of a connected plane graph is connected (Newman, *Elements of the Topology of Plane
Sets of Points*, Chapter VI), assumed. -/
def Unicoherence {V : Type*} {G : SimpleGraph V}
    (E : PlaneEmbedding G) : Prop :=
  G.Connected → ∀ F, E.IsFace F → Bornology.IsBounded F → IsPreconnected (frontier F)

/-- The discrete Moser estimate on a periodic network (Delmotte, Rev. Mat. Iberoamericana 15
(1999), Proposition 5.3), assumed. -/
def MoserEstimate {V : Type*} (P : PeriodicGraph V)
    (c : V → V → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ r s : ℝ, 0 < r → r < s → ∀ f : V → ℝ,
      (∀ x ∈ P.square s, netLaplacian P.graph c f x = 0) →
      ∀ x ∈ P.square r,
        |f x| ≤ (C / (s - r)) * Real.sqrt (∑ y ∈ P.square s, f y ^ 2)

end External

end UCPlanarAudit
-- VOCABULARY-END

namespace UCPlanarAudit

/-- Theorem 1.1 (`theorem:liouville`). -/
theorem liouville {V : Type*} (P : PeriodicPlaneGraph V)
    (c : V → V → ℝ) (hc : IsCond P.graph c)
    (hp : P.toPeriodicGraph.PeriodicConductance c)
    (hMos : External.MoserEstimate P.toPeriodicGraph c)
    (hES : External.EdgeSplitting P.embedding)
    (hU : External.Unicoherence P.embedding) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (o : V) (f : V → ℝ),
      HarmonicOn P.graph c f Set.univ →
      P.toPeriodicGraph.HasBoundedDensity o f ε → ∃ a : ℝ, ∀ x, f x = a := by
  sorry

end UCPlanarAudit
