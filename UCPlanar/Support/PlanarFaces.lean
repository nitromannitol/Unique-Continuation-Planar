/- Finite paths in the frontier of a face. -/
import UCPlanar.Support.PlanarTrace

open scoped Classical

/-- Every vertex of a walk along a face is incident to that face. -/
theorem UCPlanar.PlaneEmbedding.support_incident_of_walkTrace_subset {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {x y : V}
    (p : G.Walk x y) (F : Set UCPlanar.Plane) (htrace : E.walkTrace p ⊆ frontier F) :
    ∀ z ∈ p.support, E.Incident F z := by
  intro z hz
  exact htrace ((E.pos_mem_walkTrace_iff p z).mpr hz)

/-- A face-size bound controls the number of vertices in any walk along that face. -/
theorem UCPlanar.PlaneEmbedding.card_support_le_faceBound {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (p : G.Walk x y)
    (F : Set UCPlanar.Plane) (hF : E.IsFace F) (L : ℕ) (hL : E.FaceBound L)
    (htrace : E.walkTrace p ⊆ frontier F) : p.support.toFinset.card ≤ L := by
  have hs : (p.support.toFinset : Set V) ⊆ {z | E.Incident F z} := by
    intro z hz
    exact E.support_incident_of_walkTrace_subset p F htrace z (List.mem_toFinset.mp hz)
  have hc := Set.ncard_le_ncard hs (hL F hF).1
  rw [Set.ncard_coe_finset] at hc
  exact hc.trans (hL F hF).2

/-- A simple path along a face of size at most `L` has length strictly below `L`. -/
theorem UCPlanar.PlaneEmbedding.length_lt_faceBound {V : Type*} {G : SimpleGraph V}
    (E : UCPlanar.PlaneEmbedding G) {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (F : Set UCPlanar.Plane) (hF : E.IsFace F) (L : ℕ) (hL : E.FaceBound L)
    (htrace : E.walkTrace p ⊆ frontier F) : p.length < L := by
  have hc := E.card_support_le_faceBound p F hF L hL htrace
  rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support] at hc
  omega

/-- All vertices of a face path are cofacial with its starting vertex. -/
theorem UCPlanar.PlaneEmbedding.support_cofacial_of_walkTrace_subset {V : Type*}
    {G : SimpleGraph V} (E : UCPlanar.PlaneEmbedding G) {x y : V}
    (p : G.Walk x y) (F : Set UCPlanar.Plane) (hF : E.IsFace F)
    (htrace : E.walkTrace p ⊆ frontier F) : ∀ z ∈ p.support, E.Cofacial x z := by
  intro z hz
  exact ⟨F, hF, E.support_incident_of_walkTrace_subset p F htrace x p.start_mem_support,
    E.support_incident_of_walkTrace_subset p F htrace z hz⟩

