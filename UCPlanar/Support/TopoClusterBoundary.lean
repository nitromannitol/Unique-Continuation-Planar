/- The boundary edges of the cluster of faces, and the cycle of Step 3 they carry. -/
import UCPlanar.Support.TopoFaceCluster
import UCPlanar.Support.ZeroCycle
import Mathlib

open Set
open scoped Classical

/-- **The frontier of the cluster is drawn by a finite edge set.**  Some finite set of edges
covers the frontier of the region filled by the faces meeting `N`, and each of its arcs lies on
that frontier. -/
def UCPlanar.PlaneEmbedding.HasClusterBoundary {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (N : Set V) : Prop :=
  ∃ T : Finset (Sym2 V), ↑T ⊆ G.edgeSet ∧
    frontier (E.clusterRegion N) ⊆ E.edgesTrace ↑T ∧
    ∀ e ∈ T, E.arcOf e ⊆ frontier (E.clusterRegion N)

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **The cycle surrounding the cluster.**  Given the boundary cycle theorem, a locally finite
family of faces, a bounded filled region and a finite edge set drawing its frontier, a cycle of
the graph encloses the prescribed vertex of `N` and avoids `N` altogether. -/
theorem exists_cycle_of_clusterBoundary (E : UCPlanar.PlaneEmbedding G)
    (hbc : E.HasBoundaryCycles) (hLF : E.LocallyFiniteFaces) {N : Set V} {x₀ : V} (hx₀ : x₀ ∈ N)
    (hbdd : Bornology.IsBounded (E.clusterRegion N)) (hcb : E.HasClusterBoundary N) :
    ∃ (b : V) (γ : G.Walk b b), γ.IsCycle ∧ x₀ ∈ E.cycleRegion γ ∧
      (∀ z ∈ γ.support, z ∉ N) ∧
      (∀ z ∈ γ.support, ∃ F ∈ E.facesAvoiding N, E.Incident F z) ∧
      ∀ z ∈ γ.support, E.pos z ∈ frontier (E.clusterRegion N) := by
  obtain ⟨T, hT, hcover, harc⟩ := hcb
  obtain ⟨b, γ, hcyc, _, hreg, hout, hinc, _, hwt⟩ :=
    exists_surrounding_cycle E hbc hLF hx₀ hbdd hT hcover harc
  exact ⟨b, γ, hcyc, hreg, hout, hinc,
    fun z hz => hwt ((E.pos_mem_walkTrace_iff γ z).mpr hz)⟩

/-- **The cycle of Step 3 of Section 3.**  The cluster is built from the vertices where the
harmonic function is large inside the sphere of radius `m`; the cycle it carries encloses the
prescribed such vertex, and each of its own vertices is either small or outside that sphere. -/
theorem exists_step3_cycle (Q : UCPlanar.PeriodicPlaneGraph V)
    (hbc : Q.embedding.HasBoundaryCycles) (hLF : Q.embedding.LocallyFiniteFaces)
    (W : Set V) (o : V) (m : ℕ) {x₀ : V} (hx₀W : x₀ ∉ W) (hx₀m : Q.graph.dist o x₀ ≤ m)
    (hbdd : Bornology.IsBounded
      (Q.embedding.clusterRegion {y | y ∉ W ∧ Q.graph.dist o y ≤ m}))
    (hcb : Q.embedding.HasClusterBoundary {y | y ∉ W ∧ Q.graph.dist o y ≤ m}) :
    ∃ (b : V) (γ : Q.graph.Walk b b), γ.IsCycle ∧ x₀ ∈ Q.embedding.cycleRegion γ ∧
      ∀ z ∈ γ.support, z ∈ W ∨ m < Q.graph.dist o z := by
  obtain ⟨b, γ, hcyc, hreg, hout, _, _⟩ :=
    exists_cycle_of_clusterBoundary Q.embedding hbc hLF (N := {y | y ∉ W ∧ Q.graph.dist o y ≤ m})
      (x₀ := x₀) ⟨hx₀W, hx₀m⟩ hbdd hcb
  refine ⟨b, γ, hcyc, hreg, ?_⟩
  intro z hz
  by_cases hzW : z ∈ W
  · exact Or.inl hzW
  · refine Or.inr ?_
    by_contra hle
    exact hout z hz ⟨hzW, by omega⟩

/-- **The vertices of the Step 3 cycle satisfy the boundary clause of `SurroundedBy`.**  A vertex
of the cycle where the function is not small lies outside the sphere of radius `m`, and, being
confined to the buffer of that sphere, witnesses its own nearness to the boundary. -/
theorem mem_of_not_nearBoundaryOutside (Q : UCPlanar.PeriodicPlaneGraph V) (W : Set V)
    (o : V) (m r : ℕ) {b : V} (γ : Q.graph.Walk b b)
    (hdich : ∀ z ∈ γ.support, z ∈ W ∨ m < Q.graph.dist o z)
    (hconf : ∀ z ∈ γ.support, Q.graph.dist o z ≤ m + r) :
    ∀ z ∈ γ.support, ¬ UCPlanar.NearBoundaryOutside Q.graph W o m r z → z ∈ W := by
  intro z hz hnear
  by_contra hzW
  refine hnear ⟨z, by simp, hzW, ?_, hconf z hz⟩
  rcases hdich z hz with h | h
  · exact absurd h hzW
  · omega

end UCPlanar.Support
