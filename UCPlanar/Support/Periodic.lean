/-
Periodic graphs with a proper rank-two coordinate realization.
-/
import UCPlanar.Support.Planar
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Group.Basic

open scoped Classical

/-- A connected, locally finite periodic graph with a finite set of vertex orbits. -/
structure UCPlanar.PeriodicGraph (V : Type*) where
  graph : SimpleGraph V
  locallyFinite : graph.LocallyFinite
  connected : graph.Connected
  pos : V → UCPlanar.Plane
  pos_injective : Function.Injective pos
  period : UCPlanar.Plane ≃ₗ[ℝ] UCPlanar.Plane
  shift : LatticeProb.Site 2 → V → V
  shift_zero : ∀ x, shift 0 x = x
  shift_add : ∀ a b x, shift (a + b) x = shift a (shift b x)
  shift_adj : ∀ a x y, graph.Adj (shift a x) (shift a y) ↔ graph.Adj x y
  pos_shift : ∀ a x, pos (shift a x) = pos x + period (fun i => (a i : ℝ))
  representatives : Finset V
  covers : ∀ x, ∃ v ∈ representatives, ∃ a, shift a v = x
  finite_squares : ∀ R : ℝ, {x | ∀ i, |pos x i| ≤ R}.Finite
  finite_balls : ∀ x n, (LatticeProb.Graph.closedBall graph x n).Finite

attribute [instance] UCPlanar.PeriodicGraph.locallyFinite

/-- A periodic graph with a compatible plane embedding. -/
structure UCPlanar.PeriodicPlaneGraph (V : Type*) extends UCPlanar.PeriodicGraph V where
  embedding : UCPlanar.PlaneEmbedding graph
  embedding_pos : embedding.pos = pos
  edge_shift : ∀ a x y (h : graph.Adj x y),
    Set.range (embedding.edge ((shift_adj a x y).mpr h)) =
      (fun p => p + period (fun i => (a i : ℝ))) '' Set.range (embedding.edge h)
  proper_edges : ∀ R : ℝ, {x | ∃ y, ∃ h : graph.Adj x y,
    ∃ p ∈ Set.range (embedding.edge h), ∀ i, |p i| ≤ R}.Finite
  bounded_faces : ∃ L, embedding.FaceBound L
  face_diameter : ∃ R : ℝ, ∀ F, embedding.IsFace F → ∀ p ∈ F, ∀ q ∈ F, dist p q ≤ R

/-- The vertices in a geometric square of radius `R`. -/
noncomputable def UCPlanar.PeriodicGraph.square {V : Type*}
    (P : UCPlanar.PeriodicGraph V) (R : ℝ) : Finset V :=
  (P.finite_squares R).toFinset

/-- A finite graph metric ball, using the shared graph distance. -/
noncomputable def UCPlanar.PeriodicGraph.ball {V : Type*}
    (P : UCPlanar.PeriodicGraph V) (o : V) (n : ℕ) : Finset V :=
  (P.finite_balls o n).toFinset

/-- Translation invariance of an undirected conductance. -/
def UCPlanar.PeriodicGraph.PeriodicConductance {V : Type*}
    (P : UCPlanar.PeriodicGraph V) (c : V → V → ℝ) : Prop :=
  ∀ a x y, c (P.shift a x) (P.shift a y) = c x y

/-- A finite supremum norm, with the usual zero value on the empty domain. -/
noncomputable def UCPlanar.supNorm {V : Type*} (S : Finset V) (f : V → ℝ) : ℝ :=
  ((S.sup (fun x => ‖f x‖₊) : NNReal) : ℝ)
