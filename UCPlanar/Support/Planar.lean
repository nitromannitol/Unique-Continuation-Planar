/-
Plane embeddings and the complementary faces of a drawn graph.
-/
import LatticeProb.Network.Basic
import LatticeProb.Site
import Mathlib.Topology.Path
import Mathlib.Topology.Connected.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Schoenflies.Polygonal

open scoped Classical

/-- The real coordinate plane. -/
abbrev UCPlanar.Plane := Fin 2 → ℝ

/-- The identity homeomorphism from the coordinate plane to the Euclidean plane. -/
noncomputable def UCPlanar.Support.planeHomeo : UCPlanar.Plane ≃ₜ Schoenflies.Plane :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).symm

/-- A topological embedding of a simple graph in the plane. -/
structure UCPlanar.PlaneEmbedding {V : Type*} (G : SimpleGraph V) where
  pos : V → UCPlanar.Plane
  pos_injective : Function.Injective pos
  edge : ∀ {x y}, G.Adj x y → Path (pos x) (pos y)
  edge_injective : ∀ {x y} (h : G.Adj x y), Function.Injective (edge h)
  edge_symm : ∀ {x y} (h : G.Adj x y), Set.range (edge h) = Set.range (edge h.symm)
  vertex_on_edge : ∀ {x y} (h : G.Adj x y) z,
    pos z ∈ Set.range (edge h) → z = x ∨ z = y
  edge_inter : ∀ {x y u v} (h : G.Adj x y) (k : G.Adj u v),
    ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) →
    Set.range (edge h) ∩ Set.range (edge k) ⊆
      ({pos x, pos y} : Set UCPlanar.Plane) ∩ {pos u, pos v}
  edge_polygonal : ∀ {x y} (h : G.Adj x y),
    Schoenflies.IsPolygonal (UCPlanar.Support.planeHomeo '' Set.range (edge h))

/-- The union of the drawn vertices and edges. -/
def UCPlanar.PlaneEmbedding.trace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) : Set UCPlanar.Plane :=
  Set.range E.pos ∪ {p | ∃ x y, ∃ h : G.Adj x y, p ∈ Set.range (E.edge h)}

/-- Faces are connected components of the complement of the drawing. -/
def UCPlanar.PlaneEmbedding.IsFace {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (F : Set UCPlanar.Plane) : Prop :=
  ∃ p ∉ E.trace, F = connectedComponentIn E.traceᶜ p

/-- A vertex is incident to a face when its image lies in the face frontier. -/
def UCPlanar.PlaneEmbedding.Incident {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (F : Set UCPlanar.Plane) (x : V) : Prop :=
  E.pos x ∈ frontier F

/-- Cofacial vertices, the adjacency underlying face distance. -/
def UCPlanar.PlaneEmbedding.Cofacial {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (x y : V) : Prop :=
  ∃ F, E.IsFace F ∧ E.Incident F x ∧ E.Incident F y

/-- Two faces are dual neighbors when their frontiers contain a common edge. -/
def UCPlanar.PlaneEmbedding.DualAdjacent {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (F H : Set UCPlanar.Plane) : Prop :=
  F ≠ H ∧ E.IsFace F ∧ E.IsFace H ∧
    ∃ x y, ∃ h : G.Adj x y, Set.range (E.edge h) ⊆ frontier F ∩ frontier H

/-- A uniform bound on the number of vertices incident to a face. -/
def UCPlanar.PlaneEmbedding.FaceBound {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (L : ℕ) : Prop :=
  ∀ F, E.IsFace F → {x | E.Incident F x}.Finite ∧ {x | E.Incident F x}.ncard ≤ L
