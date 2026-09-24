/- Alternating crosscuts intersect: the general Jordan-curve form. -/
import UCPlanar.Support.TopoWalk
import Schoenflies.CrosscutCells
import Schoenflies.PolyArcRealize

open scoped Classical

namespace UCPlanar.Support

/-- Two arcs of a Jordan curve whose endpoints alternate around it, with the second arc's
interior inside the curve and the first arc a crosscut of it, meet. This is the general-plane
form of the alternating-crosscut intersection used by the topological lemma. -/
theorem alternating_inter_nonempty_general {C A₁ A₂ P Q : Set Schoenflies.Plane}
    {p q w₁ w₂ : Schoenflies.Plane}
    (hcross : Schoenflies.IsCrosscut C P p q) (hcut : Schoenflies.IsCutPair C p q A₁ A₂)
    (hQ : IsPreconnected Q) (hQside : Q ⊆ Schoenflies.inside C)
    (hw₁ : w₁ ∈ closure Q) (hw₂ : w₂ ∈ closure Q)
    (hw₁A : w₁ ∈ A₁) (hw₁B : w₁ ∉ A₂) (hw₂B : w₂ ∈ A₂) (hw₂A : w₂ ∉ A₁) :
    (Q ∩ P).Nonempty := by
  have hj : ∀ S : Set Schoenflies.Plane, Schoenflies.IsJordanCurve S → Schoenflies.IsSeparating S :=
    fun S hS => Schoenflies.jordan_curve_theorem hS
  have hdecomp := hcross.inside_diff_eq hj hcut hcross.hasArcCollars
  have hcomp₁ := hcross.side_isComponent hj hcut
  have hcomp₂ := hcross.side_isComponent hj hcut.symm
  have hclos₁ := hcross.closure_side_inter hj hcut
  have hclos₂ := hcross.closure_side_inter hj hcut.symm
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem] at hempty
  have hsub : Q ⊆ Schoenflies.inside C \ P := fun z hz => ⟨hQside hz, fun hzP => hempty z ⟨hz, hzP⟩⟩
  obtain ⟨z, hz⟩ : Q.Nonempty := by
    by_contra hQ'
    rw [Set.not_nonempty_iff_eq_empty] at hQ'
    rw [hQ', closure_empty] at hw₁
    simp at hw₁
  have hzcell : z ∈ Schoenflies.inside (A₁ ∪ P) ∪ Schoenflies.inside (A₂ ∪ P) := by
    rw [← hdecomp]; exact hsub hz
  rcases hzcell with hz₁ | hz₂
  · have hQ₁ : Q ⊆ Schoenflies.inside (A₁ ∪ P) := by
      have hcc := hQ.subset_connectedComponentIn hz hsub
      rwa [hcomp₁ z hz₁] at hcc
    have hmem : w₂ ∈ closure (Schoenflies.inside (A₁ ∪ P)) ∩ C :=
      ⟨closure_mono hQ₁ hw₂, Schoenflies.IsCutPair.snd_subset hcut hw₂B⟩
    rw [hclos₁] at hmem
    exact hw₂A hmem
  · have hQ₂ : Q ⊆ Schoenflies.inside (A₂ ∪ P) := by
      have hcc := hQ.subset_connectedComponentIn hz hsub
      rwa [hcomp₂ z hz₂] at hcc
    have hmem : w₁ ∈ closure (Schoenflies.inside (A₂ ∪ P)) ∩ C :=
      ⟨closure_mono hQ₂ hw₁, Schoenflies.IsCutPair.fst_subset hcut hw₁A⟩
    rw [hclos₂] at hmem
    exact hw₁B hmem

end UCPlanar.Support
