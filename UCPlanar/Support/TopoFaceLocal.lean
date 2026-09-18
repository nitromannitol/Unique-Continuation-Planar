/- Local finiteness of the faces, reduced to a statement about the plane: a neighbourhood that
meets only finitely many connected components of its part off the drawing meets only finitely
many faces. -/
import UCPlanar.Support.TopoClusterEdges
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*} {G : SimpleGraph V}

/-- **A neighbourhood meets at most as many faces as its part off the drawing has components.**
Each component off the drawing is connected in the complement of the drawing, so it determines a
single face, and every face meeting the neighbourhood arises this way. -/
theorem finite_faces_meeting_of_finite_components (Q : UCPlanar.PeriodicPlaneGraph V)
    {t : Set UCPlanar.Plane}
    (hcomp : {C | ∃ q ∈ t \ Q.embedding.trace,
      C = connectedComponentIn (t \ Q.embedding.trace) q}.Finite) :
    {F : {F : Set UCPlanar.Plane // Q.embedding.IsFace F} |
      ((F : Set UCPlanar.Plane) ∩ t).Nonempty}.Finite := by
  classical
  set S : Set UCPlanar.Plane := t \ Q.embedding.trace with hS
  set φ : UCPlanar.Plane → Set UCPlanar.Plane :=
    fun q => connectedComponentIn Q.embedding.traceᶜ q with hφ
  have hsub : S ⊆ Q.embedding.traceᶜ := fun q hq => hq.2
  have hcover : φ '' S ⊆ ⋃ C ∈ {C | ∃ q ∈ S, C = connectedComponentIn S q}, φ '' C := by
    rintro _ ⟨q, hq, rfl⟩
    exact Set.mem_biUnion ⟨q, hq, rfl⟩ ⟨q, mem_connectedComponentIn hq, rfl⟩
  have himg : (φ '' S).Finite := by
    refine Set.Finite.subset (Set.Finite.biUnion hcomp ?_) hcover
    rintro C ⟨q, hq, rfl⟩
    refine Set.Subsingleton.finite ?_
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have hC : connectedComponentIn S q ⊆ φ u :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn hu
        ((connectedComponentIn_subset S q).trans hsub)
    exact connectedComponentIn_eq (hC hv)
  refine Set.Finite.of_finite_image ?_ (fun a _ b _ hab => Subtype.ext hab)
  refine himg.subset ?_
  rintro F ⟨⟨F', hF'⟩, ⟨q, hqF, hqt⟩, rfl⟩
  refine ⟨q, ⟨hqt, isFace_subset_compl_trace Q.embedding hF' hqF⟩, ?_⟩
  obtain ⟨p₀, hp₀, hFeq⟩ := hF'
  subst hFeq
  exact (connectedComponentIn_eq hqF).symm

/-- **Local finiteness of the faces is a statement about the plane and the drawing alone.** -/
theorem locallyFiniteFaces_of_components (Q : UCPlanar.PeriodicPlaneGraph V)
    (h : ∀ p : UCPlanar.Plane, ∃ t ∈ nhds p, {C | ∃ q ∈ t \ Q.embedding.trace,
      C = connectedComponentIn (t \ Q.embedding.trace) q}.Finite) :
    Q.embedding.LocallyFiniteFaces := by
  intro p
  obtain ⟨t, ht, hfin⟩ := h p
  exact ⟨t, ht, finite_faces_meeting_of_finite_components Q hfin⟩

/-- **Near any point the drawing is the drawing of finitely many edges.**  Properness bounds the
edges that reach a ball, so the only thing between the present fields of a periodic plane graph
and local finiteness of its faces is that a ball minus finitely many polygonal arcs has finitely
many connected components. -/
theorem exists_finite_trace_near (Q : UCPlanar.PeriodicPlaneGraph V) (p : UCPlanar.Plane)
    (r : ℝ) : ∃ T : Set (Sym2 V), T.Finite ∧ ↑T ⊆ Q.graph.edgeSet ∧
      ∀ q ∈ Metric.closedBall p r, q ∈ Q.embedding.trace → q ∈ Q.embedding.edgesTrace T := by
  classical
  refine ⟨{e : Sym2 V | e ∈ Q.graph.edgeSet ∧
      (Q.embedding.arcOf e ∩ Metric.closedBall p r).Nonempty},
    finite_edges_meeting_bounded Q Metric.isBounded_closedBall, fun e he => he.1, ?_⟩
  intro q hq hqt
  rw [trace_eq_edgesTrace Q] at hqt
  obtain ⟨e, he, hqe⟩ := exists_arcOf_of_mem_edgesTrace Q.embedding hqt
  exact Set.mem_biUnion (show e ∈ _ from ⟨he, q, hqe, hq⟩) hqe

end UCPlanar.Support
