/-
Cycle interiors, face paths and the boundary conditions of Section 2.
-/
import UCPlanar.Support.Planar
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Topology.MetricSpace.Bounded

open scoped Classical

/-- The geometric trace of a graph walk. -/
def UCPlanar.PlaneEmbedding.walkTrace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} : G.Walk x y → Set UCPlanar.Plane
  | .nil => {E.pos x}
  | .cons h tail => Set.range (E.edge h) ∪ E.walkTrace tail

/-- Vertices in the bounded plane region enclosed by a cycle, including the cycle. -/
def UCPlanar.PlaneEmbedding.cycleRegion {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {o : V} (γ : G.Walk o o) : Set V :=
  {x | x ∈ γ.support ∨ (E.pos x ∉ E.walkTrace γ ∧
    Bornology.IsBounded (connectedComponentIn (E.walkTrace γ)ᶜ (E.pos x)))}

/-- Each component of an induced subgraph meets the specified boundary. -/
def UCPlanar.ComponentsMeetBoundary {V : Type*} (G : SimpleGraph V)
    (S boundary : Set V) : Prop :=
  ∀ x : S, ∃ y : S, y.val ∈ boundary ∧ (G.induce S).Reachable x y

/-- A path along one face, avoiding both signs, ends next to both signs. -/
def UCPlanar.PlaneEmbedding.FacePathToSigns {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (P M : Set V) (z : V) : Prop :=
  ∃ F, E.IsFace F ∧ E.Incident F z ∧
    ∃ w, ∃ β : G.Walk z w, β.IsPath ∧ E.walkTrace β ⊆ frontier F ∧
      (∀ x ∈ β.support, x ∉ P ∪ M) ∧
      (∃ p ∈ P, G.Adj w p) ∧ (∃ m ∈ M, G.Adj w m)

/-- Faces touching both a vertex set and its complement. -/
def UCPlanar.PlaneEmbedding.BoundaryFace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (S : Set V) (F : Set UCPlanar.Plane) : Prop :=
  E.IsFace F ∧ (∃ x ∈ S, E.Incident F x) ∧ (∃ y ∉ S, E.Incident F y)
