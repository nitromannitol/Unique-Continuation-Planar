/- The boundary edges of the filled cluster: finitely many arcs of the drawing meet a bounded
part of the plane, so the frontier of a bounded filled region is drawn by a finite edge set. -/
import UCPlanar.Support.TopoClusterBoundary
import Mathlib

open Set
open scoped Classical

/-- **The frontier of the filled region is a union of whole arcs.**  Every point of it lies on an
arc of the drawing which lies on that frontier in its entirety.  This is the two-sidedness of an
edge, the one local property of the drawing that the boundary edge set needs. -/
def UCPlanar.PlaneEmbedding.FrontierArcs {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) (N : Set V) : Prop :=
  ∀ p ∈ frontier (E.clusterRegion N), ∃ e ∈ G.edgeSet,
    p ∈ E.arcOf e ∧ E.arcOf e ⊆ frontier (E.clusterRegion N)

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **Finitely many edges of a periodic plane graph reach a bounded part of the plane.**  Both
endpoints of such an edge belong to the finite set of vertices supplied by properness. -/
theorem finite_edges_meeting_bounded (Q : UCPlanar.PeriodicPlaneGraph V)
    {A : Set UCPlanar.Plane} (hA : Bornology.IsBounded A) :
    {e : Sym2 V | e ∈ Q.graph.edgeSet ∧ (Q.embedding.arcOf e ∩ A).Nonempty}.Finite := by
  classical
  obtain ⟨R, hR⟩ := hA.subset_closedBall (0 : UCPlanar.Plane)
  set X : Set V := {x | ∃ y, ∃ h : Q.graph.Adj x y,
    ∃ p ∈ Set.range (Q.embedding.edge h), ∀ i, |p i| ≤ R} with hX
  have hXfin : X.Finite := Q.proper_edges R
  refine Set.Finite.subset (Set.Finite.image (fun q : V × V => s(q.1, q.2)) (hXfin.prod hXfin)) ?_
  rintro e ⟨he, p, hp1, hp2⟩
  obtain ⟨x, y, h, rfl, hp⟩ := hp1
  have hbound : ∀ i, |p i| ≤ R := by
    have hball := hR hp2
    rw [Metric.mem_closedBall, dist_zero_right] at hball
    intro i
    have h3 : ‖p i‖ ≤ ‖p‖ := norm_le_pi_norm p i
    rw [Real.norm_eq_abs] at h3
    linarith
  have hxX : x ∈ X := ⟨y, h, p, hp, hbound⟩
  have hyX : y ∈ X := ⟨x, h.symm, p, by rw [← Q.embedding.edge_symm h]; exact hp, hbound⟩
  exact ⟨(x, y), ⟨hxX, hyX⟩, rfl⟩

/-- **The boundary edge set of a bounded filled region is finite.**  Its arcs lie on the frontier,
which is bounded, so only finitely many edges are available. -/
theorem finite_boundaryEdges (Q : UCPlanar.PeriodicPlaneGraph V) (N : Set V)
    (hbdd : Bornology.IsBounded (Q.embedding.clusterRegion N)) :
    {e : Sym2 V | e ∈ Q.graph.edgeSet ∧ (Q.embedding.arcOf e).Nonempty ∧
      Q.embedding.arcOf e ⊆ frontier (Q.embedding.clusterRegion N)}.Finite := by
  refine Set.Finite.subset
    (finite_edges_meeting_bounded Q (A := frontier (Q.embedding.clusterRegion N))
      (hbdd.closure.subset frontier_subset_closure)) ?_
  rintro e ⟨he, ⟨p, hp⟩, hsub⟩
  exact ⟨he, p, hp, hsub hp⟩

/-- **The frontier of a bounded filled region is drawn by a finite edge set.**  This is the
boundary edge set of Step 3, granted that the frontier is a union of whole arcs. -/
theorem hasClusterBoundary_of_frontierArcs (Q : UCPlanar.PeriodicPlaneGraph V) (N : Set V)
    (hbdd : Bornology.IsBounded (Q.embedding.clusterRegion N))
    (hFA : Q.embedding.FrontierArcs N) : Q.embedding.HasClusterBoundary N := by
  classical
  set S : Set (Sym2 V) := {e : Sym2 V | e ∈ Q.graph.edgeSet ∧ (Q.embedding.arcOf e).Nonempty ∧
    Q.embedding.arcOf e ⊆ frontier (Q.embedding.clusterRegion N)} with hS
  have hfin : S.Finite := finite_boundaryEdges Q N hbdd
  refine ⟨hfin.toFinset, ?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at he
    exact he.1
  · intro p hp
    obtain ⟨e, he, hpe, hsub⟩ := hFA p hp
    refine Set.mem_biUnion (?_ : e ∈ (hfin.toFinset : Set (Sym2 V))) hpe
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨he, ⟨p, hpe⟩, hsub⟩
  · intro e he
    rw [Set.Finite.mem_toFinset] at he
    exact he.2.2

end UCPlanar.Support
