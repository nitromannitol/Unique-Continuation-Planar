/- The face walks of Step 3, granted the cited unicoherence of the sphere: the frontier of every
face is connected, every face is bounded by the diameter bound of the periodic plane graph, and
the frontier is then covered by whole arcs, which is what joins the vertices of a face along it. -/
import UCPlanar.Support.TopoArcLocal
import UCPlanar.External.Unicoherence
import Mathlib

open Set
open scoped Classical

namespace UCPlanar.Support

variable {V : Type*}

/-- Every face of a periodic plane graph is bounded, by the uniform diameter bound. -/
theorem isBounded_isFace (Q : UCPlanar.PeriodicPlaneGraph V) {F : Set UCPlanar.Plane}
    (hF : Q.embedding.IsFace F) : Bornology.IsBounded F := by
  obtain ⟨R, hR⟩ := Q.face_diameter
  rw [Metric.isBounded_iff]
  exact ⟨R, fun x hx y hy => hR F hF x hx y hy⟩

/-- **The frontier of every face is drawn by finitely many whole arcs**, granted unicoherence. -/
theorem faceFrontierArcs_of_unicoherence (Q : UCPlanar.PeriodicPlaneGraph V)
    (hU : UCPlanar.External.Unicoherence Q.embedding) {F : Set UCPlanar.Plane}
    (hF : Q.embedding.IsFace F) : Q.embedding.FaceFrontierArcs F :=
  faceFrontierArcs_of_preconnected Q hF (hU Q.connected F hF (isBounded_isFace Q hF))
    (isBounded_isFace Q hF)

/-- **The face walks, granted unicoherence.**  The vertices incident to a face are joined by a
walk drawn on its frontier. -/
theorem faceWalks_of_unicoherence (Q : UCPlanar.PeriodicPlaneGraph V)
    (hU : UCPlanar.External.Unicoherence Q.embedding) : Q.embedding.FaceWalks :=
  faceWalks_of_frontierArcs Q.embedding
    (fun _ hF => faceFrontierArcs_of_unicoherence Q hU hF)
    (fun F hF => hU Q.connected F hF (isBounded_isFace Q hF))

/-- **A walk drawn on the frontier of a face may be taken to be a path**, so its length is below
the face bound.  Every vertex of such a walk is incident to the face. -/
theorem exists_short_face_walk (Q : UCPlanar.PeriodicPlaneGraph V) {L : ℕ}
    (hL : Q.embedding.FaceBound L) (hFW : Q.embedding.FaceWalks) {F : Set UCPlanar.Plane}
    (hF : Q.embedding.IsFace F) {u v : V} (hu : Q.embedding.Incident F u)
    (hv : Q.embedding.Incident F v) : Q.graph.dist u v ≤ L := by
  classical
  obtain ⟨β, hβ⟩ := hFW F hF u v hu hv
  have hsupp : ∀ z ∈ β.bypass.support, Q.embedding.Incident F z := by
    intro z hz
    have hz' : z ∈ β.support := SimpleGraph.Walk.support_bypass_subset_support β hz
    exact hβ ((Q.embedding.pos_mem_walkTrace_iff β z).mpr hz')
  have hpath : β.bypass.IsPath := β.bypass_isPath
  have hfin : {x | Q.embedding.Incident F x}.Finite := (hL F hF).1
  have hsub : β.bypass.support.toFinset ⊆ hfin.toFinset := by
    intro z hz
    rw [List.mem_toFinset] at hz
    exact hfin.mem_toFinset.mpr (hsupp z hz)
  have hcard : β.bypass.support.toFinset.card ≤ L := by
    refine le_trans (Finset.card_le_card hsub) ?_
    have hc : hfin.toFinset.card = {x | Q.embedding.Incident F x}.ncard :=
      (Set.ncard_eq_toFinset_card _ hfin).symm
    rw [hc]
    exact (hL F hF).2
  have hlen : β.bypass.length + 1 ≤ L := by
    have hnodup := hpath.support_nodup
    have : β.bypass.support.toFinset.card = β.bypass.support.length :=
      List.toFinset_card_of_nodup hnodup
    rw [SimpleGraph.Walk.length_support] at this
    omega
  exact le_trans (SimpleGraph.dist_le β.bypass) (by omega)

end UCPlanar.Support
